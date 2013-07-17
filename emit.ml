open Llvm
open Closure

let the_module : llmodule option ref = ref None

let get_module () =
  match !the_module with
  | None -> failwith "Emit.get_module: llmodule not initialised"
  | Some m -> m
  
let initialise () =
  match !the_module with
  | None -> the_module := Some (create_module (global_context ()) "")
  | Some m ->
      Printf.eprintf "Emit.initialise: llmodule already initialised.";
      dispose_module m; the_module := Some (create_module (global_context ()) "")

let cleanup () =
  match !the_module with
  | None -> ()
  | Some m ->
      dispose_module m;
      the_module := None

let const_int w n =
  const_int (integer_type (global_context ()) w) n

let new_block b label =
  let f = block_parent (insertion_block b) in
  append_block (global_context ()) label f

let get_function name =
  Printf.eprintf "looking up function '%s'.\n" name;
  match lookup_function name (get_module ()) with
  | Some f -> f
  | None -> failwith "Emit.get_function this shouldn't happen."

let int_t w =
  integer_type (global_context ()) w

let rec emit_type = function
  | Type.Unit -> int_t 32
  | Type.Bool -> int_t 32
  | Type.Int ->  int_t 32
  | Type.Float -> double_type (global_context ())
  | Type.Fun (tl, t) ->
      pointer_type (struct_type (global_context ())
        [| pointer_type (function_type
          (emit_type t)
          (Array.of_list (pointer_type (int_t 8) :: List.map emit_type tl))) |])
  | Type.Tuple (tl) ->
      pointer_type (struct_type (global_context ())
        (Array.of_list (List.map emit_type tl)))
  | Type.Array t ->
      pointer_type (emit_type t)
  | Type.Var _ ->
      failwith "Emit.emit_type: Var type"

let make_cls b env (id, t) clos =
  let actual_fv = List.map (fun x -> M.find x env) clos.actual_fv in
  let tl, t =
    (match t with Type.Fun (tl, t) -> tl, t | _ -> assert false) in
  let fn_type = 
    function_type (emit_type t)
     (Array.of_list (pointer_type (int_t 8) ::
       List.map emit_type tl)) in
  let clos_type = struct_type (global_context ())
    (Array.of_list (pointer_type fn_type :: 
      List.map type_of actual_fv)) in
  let clos_value = build_malloc clos_type id b in
  ignore (build_store (get_function id)
    (build_gep clos_value [| const_int 32 0; const_int 32 0 |] "" b) b);
  let rec loop i = function
    | [] -> ()
    | v :: rest ->
        ignore (build_store v
          (build_gep clos_value [| const_int 32 0; const_int 32 i |] "" b) b);
        loop (i+1) rest
  in loop 1 actual_fv;
  build_pointercast clos_value
    (pointer_type (struct_type (global_context ())
      [| pointer_type fn_type |])) id b

let let_tuple b env idtl id =
  let tuple = M.find id env in
  let rec loop env i = function
    | [] -> env
    | (id1, _) :: rest ->
        loop (M.add id1 (build_load
          (build_gep tuple [| const_int 32 0; const_int 32 i |] id1 b) id1 b) env) (i+1) rest
  in loop env 0 idtl

let app_dir b env id idl =
  let f = get_function id in
  (* let copy_of_fnptr = build_alloca (type_of f) "" b in
  ignore (build_store f copy_of_fnptr b);
  let copy_of_fnptr = build_pointercast copy_of_fnptr
    (pointer_type (int_t 8)) "" b in *)
  let copy_of_fnptr = const_null (pointer_type (int_t 8)) in (* XXX *)
  let inst = build_call f
    (Array.of_list (copy_of_fnptr ::
      List.map (fun x -> M.find x env) idl)) "" b in
  inst

let app_cls b env id idl =
  let clos = M.find id env in
  let f = build_gep clos [| const_int 32 0; const_int 32 0 |] "" b in
  let f = build_load f "" b in
  let inst = build_call f
    (Array.of_list (build_pointercast clos (pointer_type (int_t 8)) "" b ::
      List.map (fun x -> M.find x env) idl)) "" b in
  inst

let initialise_array b va vlen vinit =
  let bbcurr = insertion_block b in
  let bbcond = new_block b "array.cond" in
  let bbbody = new_block b "array.init" in
  let bbdone = new_block b "array.done" in
  ignore (build_br bbcond b);
  position_at_end bbcond b;
  let counter = build_phi [const_int 32 0, bbcurr] "counter" b in
  add_incoming ((build_add counter (const_int 32 1) "" b), bbbody) counter;
  ignore (build_cond_br (build_icmp Icmp.Slt counter vlen "" b) bbbody bbdone b);
  position_at_end bbbody b;
  ignore (build_store vinit (build_gep va [| counter |] "" b) b);
  ignore (build_br bbcond b);
  position_at_end bbdone b

let rec f_nontail b env e =
  match e with
  | Unit ->
      const_int 32 0
  | Int n ->
      const_int 32 n
  | Float f ->
      const_float (double_type (global_context ())) f
  | Neg id ->
      build_neg (M.find id env) "" b
  | Add (id1, id2) ->
      build_add (M.find id1 env) (M.find id2 env) "" b
  | Sub (id1, id2) ->
      build_sub (M.find id1 env) (M.find id2 env) "" b
  | FNeg (id) ->
      build_fneg (M.find id env) "" b
  | FAdd (id1, id2) ->
      build_fadd (M.find id1 env) (M.find id2 env) "" b
  | FSub (id1, id2) ->
      build_fsub (M.find id1 env) (M.find id2 env) "" b
  | FMul (id1, id2) ->
      build_fmul (M.find id1 env) (M.find id2 env) "" b
  | FDiv (id1, id2) ->
      build_fdiv (M.find id1 env) (M.find id2 env) "" b
  | IfEq (id1, id2, e1, e2) ->
      f_if_nontail b env (build_icmp Icmp.Eq (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | IfLE (id1, id2, e1, e2) ->
      f_if_nontail b env (build_icmp Icmp.Sle (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | Let ((id, _), e1, e2) ->
      let v = f_nontail b env e1 in
      set_value_name id v;
      f_nontail b (M.add id v env) e2
  | Var id ->
      M.find id env
  | MakeCls ((id, t), clos, e) ->
      let vclos = make_cls b env (id, t) clos in
      f_nontail b (M.add id vclos env) e
  | AppCls (id, idl) ->
      app_cls b env id idl
  | AppDir (Id.L id, idl) ->
      app_dir b env id idl
  | Tuple (idl) ->
      let values = Array.of_list (List.map (fun x -> M.find x env) idl) in
      let tuple_types = Array.map type_of values in
      let tuple_type = struct_type (global_context ()) tuple_types in
      let tuple = build_malloc tuple_type "" b in
      Array.iteri (fun i v ->
        ignore (build_store v
        (build_gep tuple [| const_int 32 0; const_int 32 i |] "" b) b)) values;
      tuple
  | LetTuple (idtl, id, e) ->
      let env = let_tuple b env idtl id in
      f_nontail b env e
  | Array (id1, id2) ->
      let v1 = M.find id1 env in
      let v2 = M.find id2 env in
      let t2 = type_of v2 in
      let v = build_array_malloc t2 v1 "" b in
      let v = build_pointercast v (pointer_type t2) "" b in
      initialise_array b v v1 v2;
      v
  | Get (id1, id2) ->
      build_load (build_gep (M.find id1 env)
        [| M.find id2 env |] "" b) "" b
  | Put (id1, id2, id3) ->
      ignore (build_store (M.find id3 env) (build_gep (M.find id1 env)
        [| M.find id2 env |] "" b) b);
      const_int 32 0
  | ExtArray (Id.L id, t) ->
      build_load (declare_global (pointer_type (emit_type t)) id
        (get_module ())) id b
  | ExtFunApp (Id.L id, t, idl) ->
      let vl = List.map (fun x -> M.find x env) idl in
      let tl = List.map type_of vl in
      let f = declare_function id
        (function_type (emit_type t)
          (Array.of_list tl)) (get_module ()) in
      build_call f (Array.of_list vl) "" b

and f_if_nontail b env c e1 e2 =
  let bb_yay = new_block b "yes" in
  let bb_nay = new_block b "nay" in
  ignore (build_cond_br c bb_yay bb_nay b);
  let b_yay = builder_at_end (global_context ()) bb_yay in
  let b_nay = builder_at_end (global_context ()) bb_nay in
  let v_yay = f_nontail b_yay env e1 in
  let bb_yay = insertion_block b_yay in
  let v_nay = f_nontail b_nay env e2 in
  let bb_nay = insertion_block b_nay in
  let bb_done = new_block b_yay "done" in
  ignore (build_br bb_done b_yay);
  ignore (build_br bb_done b_nay);
  build_phi [ v_yay, bb_yay; v_nay, bb_nay ] "" b

let rec f_tail b env e =
  match e with
  | IfEq (id1, id2, e1, e2) ->
      f_if_tail b env (build_icmp Icmp.Eq (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | IfLE (id1, id2, e1, e2) ->
      f_if_tail b env (build_icmp Icmp.Sle (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | Let ((id, _), e1, e2) ->
      let v = f_nontail b env e1 in
      set_value_name id v;
      f_tail b (M.add id v env) e2
  | MakeCls ((id, t), clos, e) ->
      let vclos = make_cls b env (id, t) clos in
      f_tail b (M.add id vclos env) e
  | AppCls (id, idl) ->
      let inst = app_cls b env id idl in
      set_tail_call true inst;
      ignore (build_ret inst b)
  | AppDir (Id.L id, idl) ->
      let inst = app_dir b env id idl in
      set_tail_call true inst;
      ignore (build_ret inst b)
  | LetTuple (idtl, id, e) ->
      let env = let_tuple b env idtl id in
      f_tail b env e
  | _ ->
      let v = f_nontail b env e in
      ignore (build_ret v b)

and f_if_tail b env c e1 e2 =
  let bb_yay = new_block b "yes" in
  let bb_nay = new_block b "nay" in
  ignore (build_cond_br c bb_yay bb_nay b);
  let b_yay = builder_at_end (global_context ()) bb_yay in
  let b_nay = builder_at_end (global_context ()) bb_nay in
  f_tail b_yay env e1;
  f_tail b_nay env e2

let get_function_type fn =
  let _, t = fn.name in
  let t = ( match t with Type.Fun (_, t) -> t | _ -> assert false ) in
  function_type
    (emit_type t)
    (Array.of_list (pointer_type (int_t 8) ::
      (List.map (fun (_, t) -> emit_type t) fn.args)))

let emit_fn_header fn =
  let Id.L name, t = fn.name in
  let f = define_function name (get_function_type fn) (get_module ()) in
  set_function_call_conv CallConv.fast f;
  set_linkage Linkage.Internal f

let get_closure_type fn =
  pointer_type (struct_type (global_context ())
    (Array.of_list
      (pointer_type (get_function_type fn) ::
        List.map (fun (_, t) -> emit_type t) fn.formal_fv)))

let emit_fn_body fn =
  let Id.L name, t = fn.name in
  let f = get_function name in
  let b = builder_at_end (global_context ()) (entry_block f) in
  let clos = build_pointercast (param f 0) (get_closure_type fn) "clos" b in
  let env = M.add name clos M.empty in
  let rec loop env i = function
    | [] -> env
    | (id, t) :: rest ->
        loop (M.add id
          (build_load
            (build_gep clos [| const_int 32 0; const_int 32 i |] id b) id b) env)
          (i+1) rest
  in let env = loop env 1 fn.formal_fv in
  let rec loop env i = function
    | [] -> env
    | (id, _) :: rest ->
        set_value_name id (param f i);
        loop (M.add id (param f i) env) (i+1) rest in
  let env = loop env 1 fn.args in
  f_tail b env fn.body

let f oc (Prog(fundefs, e)) =
  initialise ();
  List.iter emit_fn_header fundefs;
  List.iter emit_fn_body fundefs;
  let main_fun = define_function "main"
    (function_type (int_t 32) [| |]) (get_module ()) in
  let b = builder_at_end (global_context ()) (entry_block main_fun) in
  ignore (f_nontail b M.empty e);
  ignore (build_ret (const_int 32 0) b);
  if not (Llvm_bitwriter.output_bitcode oc (get_module ())) then
    failwith "Failure during output of LLVM bitcode";
  cleanup ()
