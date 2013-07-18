open Llvm
open Closure

let the_module : llmodule option ref = ref None
let the_builder = builder (global_context ())

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

let new_block label =
  let f = block_parent (insertion_block the_builder) in
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
  | Type.Bool -> int_t 1
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

let make_cls env (id, t) clos =
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
  let clos_value = build_malloc clos_type id the_builder in
  ignore (build_store (get_function id)
    (build_gep clos_value [| const_int 32 0; const_int 32 0 |] "" the_builder)
      the_builder);
  let rec loop i = function
    | [] -> ()
    | v :: rest ->
        ignore (build_store v
          (build_gep clos_value [| const_int 32 0; const_int 32 i |] ""
            the_builder) the_builder);
        loop (i+1) rest
  in loop 1 actual_fv;
  build_pointercast clos_value
    (pointer_type (struct_type (global_context ())
      [| pointer_type fn_type |])) id the_builder

let let_tuple env idtl id =
  let tuple = M.find id env in
  let rec loop env i = function
    | [] -> env
    | (id1, _) :: rest ->
        loop (M.add id1 (build_load
          (build_gep tuple [| const_int 32 0; const_int 32 i |] id1 the_builder)
            id1 the_builder) env) (i+1) rest
  in loop env 0 idtl

let app_dir env id idl =
  let f = get_function id in
  (* let copy_of_fnptr = build_alloca (type_of f) "" b in
  ignore (build_store f copy_of_fnptr b);
  let copy_of_fnptr = build_pointercast copy_of_fnptr
    (pointer_type (int_t 8)) "" b in *)
  let copy_of_fnptr = const_null (pointer_type (int_t 8)) in (* XXX *)
  build_call f
    (Array.of_list (copy_of_fnptr ::
      List.map (fun x -> M.find x env) idl)) "" the_builder

let app_cls env id idl =
  let clos = M.find id env in
  let f = build_gep clos [| const_int 32 0; const_int 32 0 |] "" the_builder in
  let f = build_load f "" the_builder in
  build_call f
    (Array.of_list (build_pointercast clos (pointer_type (int_t 8)) ""
      the_builder :: List.map (fun x -> M.find x env) idl)) "" the_builder

let initialise_array va vlen vinit =
  let bbcurr = insertion_block the_builder in
  let bbcond = new_block "array.cond" in
  let bbbody = new_block "array.init" in
  let bbdone = new_block "array.done" in
  ignore (build_br bbcond the_builder);
  position_at_end bbcond the_builder;
  let counter = build_phi [const_int 32 0, bbcurr] "counter" the_builder in
  add_incoming ((build_add counter (const_int 32 1) "" the_builder), bbbody) counter;
  ignore (build_cond_br (build_icmp Icmp.Slt counter vlen "" the_builder)
    bbbody bbdone the_builder);
  position_at_end bbbody the_builder;
  ignore (build_store vinit (build_gep va [| counter |] "" the_builder)
    the_builder);
  ignore (build_br bbcond the_builder);
  position_at_end bbdone the_builder

let get_eq_op x y =
  match classify_type (type_of x), classify_type (type_of y) with
  | TypeKind.Integer, TypeKind.Integer -> build_icmp Icmp.Eq x y
  | TypeKind.Double, TypeKind.Double -> build_fcmp Fcmp.Oeq x y
  | TypeKind.Pointer, TypeKind.Pointer ->
      (fun s b -> build_icmp Icmp.Eq
        (build_ptrtoint x (int_t 64) "" b)
        (build_ptrtoint y (int_t 64) "" b) s b)
  | _, _ ->
      failwith (Printf.sprintf "Emit.get_eq_op: unexpected operand types (%s, %s)"
        (string_of_lltype (type_of x)) (string_of_lltype (type_of y)))

let get_le_op x y =
  match classify_type (type_of x), classify_type (type_of y) with
  | TypeKind.Integer, TypeKind.Integer -> build_icmp Icmp.Sle x y
  | TypeKind.Double, TypeKind.Double -> build_fcmp Fcmp.Ole x y
  | TypeKind.Pointer, TypeKind.Pointer ->
      (fun s b -> build_icmp Icmp.Ule
        (build_ptrtoint x (int_t 64) "" b)
        (build_ptrtoint y (int_t 64) "" b) s b)
  | _, _ ->
      failwith (Printf.sprintf "Emit.get_le_op: unexpected operand types (%s, %s)"
        (string_of_lltype (type_of x)) (string_of_lltype (type_of y)))

let rec f_nontail env e =
  match e with
  | Unit ->
      const_int 32 0
  | Bool b ->
      const_int 1 (if b then 1 else 0)
  | Int n ->
      const_int 32 n
  | Float f ->
      const_float (double_type (global_context ())) f
  | Not id ->
      build_not (M.find id env) "" the_builder
  | Neg id ->
      build_neg (M.find id env) "" the_builder
  | Add (id1, id2) ->
      build_add (M.find id1 env) (M.find id2 env) "" the_builder
  | Sub (id1, id2) ->
      build_sub (M.find id1 env) (M.find id2 env) "" the_builder
  | FNeg (id) ->
      build_fneg (M.find id env) "" the_builder
  | FAdd (id1, id2) ->
      build_fadd (M.find id1 env) (M.find id2 env) "" the_builder
  | FSub (id1, id2) ->
      build_fsub (M.find id1 env) (M.find id2 env) "" the_builder
  | FMul (id1, id2) ->
      build_fmul (M.find id1 env) (M.find id2 env) "" the_builder
  | FDiv (id1, id2) ->
      build_fdiv (M.find id1 env) (M.find id2 env) "" the_builder
  | Eq (id1, id2) ->
      (get_eq_op (M.find id1 env) (M.find id2 env)) "" the_builder
  | LE (id1, id2) ->
      (get_le_op (M.find id1 env) (M.find id2 env)) "" the_builder
  | If (id, e1, e2) ->
      f_if_nontail env (M.find id env) e1 e2
  (* | IfEq (id1, id2, e1, e2) ->
      f_if_nontail b env (build_icmp Icmp.Eq (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | IfLE (id1, id2, e1, e2) ->
      f_if_nontail b env (build_icmp Icmp.Sle (M.find id1 env)
        (M.find id2 env) "" b) e1 e2 *)
  | Let ((id, _), e1, e2) ->
      let v = f_nontail env e1 in
      set_value_name id v;
      f_nontail (M.add id v env) e2
  | Var id ->
      M.find id env
  | MakeCls ((id, t), clos, e) ->
      let vclos = make_cls env (id, t) clos in
      f_nontail (M.add id vclos env) e
  | AppCls (id, idl) ->
      app_cls env id idl
  | AppDir (Id.L id, idl) ->
      app_dir env id idl
  | Tuple (idl) ->
      let values = Array.of_list (List.map (fun x -> M.find x env) idl) in
      let tuple_types = Array.map type_of values in
      let tuple_type = struct_type (global_context ()) tuple_types in
      let tuple = build_malloc tuple_type "" the_builder in
      Array.iteri (fun i v ->
        ignore (build_store v
          (build_gep tuple [| const_int 32 0; const_int 32 i |] "" the_builder)
            the_builder)) values;
      tuple
  | LetTuple (idtl, id, e) ->
      let env = let_tuple env idtl id in
      f_nontail env e
  | Array (id1, id2) ->
      let v1 = M.find id1 env in
      let v2 = M.find id2 env in
      let t2 = type_of v2 in
      let v = build_array_malloc t2 v1 "" the_builder in
      let v = build_pointercast v (pointer_type t2) "" the_builder in
      initialise_array v v1 v2;
      v
  | Get (id1, id2) ->
      build_load (build_gep (M.find id1 env)
        [| M.find id2 env |] "" the_builder) "" the_builder
  | Put (id1, id2, id3) ->
      ignore (build_store (M.find id3 env) (build_gep (M.find id1 env)
        [| M.find id2 env |] "" the_builder) the_builder);
      const_int 32 0
  | ExtArray (Id.L id, t) ->
      build_load (declare_global (pointer_type (emit_type t)) id
        (get_module ())) id the_builder
  | ExtFunApp (Id.L id, t, idl) ->
      let vl = List.map (fun x -> M.find x env) idl in
      let tl = List.map type_of vl in
      let f = declare_function id
        (function_type (emit_type t)
          (Array.of_list tl)) (get_module ()) in
      build_call f (Array.of_list vl) "" the_builder

and f_if_nontail env c e1 e2 =
  let bb_yay = new_block "yes" in
  let bb_nay = new_block "nay" in
  let bb_done = new_block "done" in
  ignore (build_cond_br c bb_yay bb_nay the_builder);
  position_at_end bb_yay the_builder;
  let v_yay = f_nontail env e1 in
  let bb_yay = insertion_block the_builder in
  ignore (build_br bb_done the_builder);
  position_at_end bb_nay the_builder;
  let v_nay = f_nontail env e2 in
  let bb_nay = insertion_block the_builder in
  ignore (build_br bb_done the_builder);
  position_at_end bb_done the_builder;
  build_phi [ v_yay, bb_yay; v_nay, bb_nay ] "" the_builder

let rec f_tail env e =
  match e with
  | If (id, e1, e2) ->
      f_if_tail env (M.find id env) e1 e2
  (* | IfEq (id1, id2, e1, e2) ->
      f_if_tail b env (build_icmp Icmp.Eq (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | IfLE (id1, id2, e1, e2) ->
      f_if_tail b env (build_icmp Icmp.Sle (M.find id1 env)
        (M.find id2 env) "" b) e1 e2 *)
  | Let ((id, _), e1, e2) ->
      let v = f_nontail env e1 in
      set_value_name id v;
      f_tail (M.add id v env) e2
  | MakeCls ((id, t), clos, e) ->
      let vclos = make_cls env (id, t) clos in
      f_tail (M.add id vclos env) e
  | AppCls (id, idl) ->
      let inst = app_cls env id idl in
      set_tail_call true inst;
      ignore (build_ret inst the_builder)
  | AppDir (Id.L id, idl) ->
      let inst = app_dir env id idl in
      set_tail_call true inst;
      ignore (build_ret inst the_builder)
  | LetTuple (idtl, id, e) ->
      let env = let_tuple env idtl id in
      f_tail env e
  | _ ->
      let v = f_nontail env e in
      ignore (build_ret v the_builder)

and f_if_tail env c e1 e2 =
  let bb_yay = new_block "yes" in
  let bb_nay = new_block "nay" in
  ignore (build_cond_br c bb_yay bb_nay the_builder);
  position_at_end bb_yay the_builder;
  f_tail env e1;
  position_at_end bb_nay the_builder;
  f_tail env e2

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
  position_at_end (entry_block f) the_builder;
  (* let b = builder_at_end (global_context ()) (entry_block f) in *)
  let clos = build_pointercast (param f 0) (get_closure_type fn) "clos"
    the_builder in
  let env = M.add name clos M.empty in
  let rec loop env i = function
    | [] -> env
    | (id, t) :: rest ->
        loop (M.add id
          (build_load
            (build_gep clos [| const_int 32 0; const_int 32 i |] id the_builder)
              id the_builder) env) (i+1) rest
  in let env = loop env 1 fn.formal_fv in
  let rec loop env i = function
    | [] -> env
    | (id, _) :: rest ->
        set_value_name id (param f i);
        loop (M.add id (param f i) env) (i+1) rest in
  let env = loop env 1 fn.args in
  f_tail env fn.body

let f oc (Prog(fundefs, e)) =
  initialise ();
  List.iter emit_fn_header fundefs;
  List.iter emit_fn_body fundefs;
  let main_fun = define_function "main"
    (function_type (int_t 32) [| |]) (get_module ()) in
  position_at_end (entry_block main_fun) the_builder;
  ignore (f_nontail M.empty e);
  ignore (build_ret (const_int 32 0) the_builder);
  if not (Llvm_bitwriter.output_bitcode oc (get_module ())) then
    failwith "Failure during output of LLVM bitcode";
  cleanup ()
