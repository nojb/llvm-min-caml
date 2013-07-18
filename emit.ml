open Llvm
open Gc

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

let atom env a =
  match a with
  | Var id -> M.find id env
  | Root id -> build_load (M.find id env) id the_builder

let emit_alloca t id v =
  let b = builder_at_end (global_context ())
    (entry_block (block_parent (insertion_block the_builder))) in
  let a = build_alloca t id b in
  ignore (build_call (declare_function "llvm.gcroot"
    (function_type (void_type (global_context ()))
      [| pointer_type (pointer_type (int_t 8)); pointer_type (int_t 8) |])
    (get_module ()))
    [| build_pointercast a (pointer_type (pointer_type (int_t 8))) "" b;
      const_null (pointer_type (int_t 8)) |] "" b);
  ignore (build_store v a the_builder);
  a

let make_cls env clos =
  let actual_fv = List.map (atom env) clos.actual_fv in
  let Id.L id, t = clos.entry in
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

let let_tuple env atl tuple =
  let rec loop env i = function
    | [] -> env
    | (Var id1, _) :: rest ->
        loop (M.add id1 (build_load
          (build_gep tuple [| const_int 32 0; const_int 32 i |] id1 the_builder)
            id1 the_builder) env) (i+1) rest
    | (Root id1, t) :: rest ->
        let a = emit_alloca (emit_type t) id1
          (build_load (build_gep tuple [| const_int 32 0; const_int 32 i |] id1 the_builder)
            id1 the_builder) in
        loop (M.add id1 a env) (i+1) rest
  in loop env 0 atl

let app_dir env id vl =
  let f = get_function id in
  (* let copy_of_fnptr = build_alloca (type_of f) "" b in
  ignore (build_store f copy_of_fnptr b);
  let copy_of_fnptr = build_pointercast copy_of_fnptr
    (pointer_type (int_t 8)) "" b in *)
  let copy_of_fnptr = const_null (pointer_type (int_t 8)) in (* XXX *)
  build_call f
    (Array.of_list (copy_of_fnptr :: vl)) "" the_builder

let app_cls env clos vl =
  let f = build_gep clos [| const_int 32 0; const_int 32 0 |] "" the_builder in
  let f = build_load f "" the_builder in
  build_call f
    (Array.of_list (build_pointercast clos (pointer_type (int_t 8)) ""
      the_builder :: vl)) "" the_builder

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
  | Not a ->
      build_not (atom env a) "" the_builder
  | Neg a ->
      build_neg (atom env a) "" the_builder
  | Add (a1, a2) ->
      build_add (atom env a1) (atom env a2) "" the_builder
  | Sub (a1, a2) ->
      build_sub (atom env a1) (atom env a2) "" the_builder
  | FNeg (a) ->
      build_fneg (atom env a) "" the_builder
  | FAdd (a1, a2) ->
      build_fadd (atom env a1) (atom env a2) "" the_builder
  | FSub (a1, a2) ->
      build_fsub (atom env a1) (atom env a2) "" the_builder
  | FMul (a1, a2) ->
      build_fmul (atom env a1) (atom env a2) "" the_builder
  | FDiv (a1, a2) ->
      build_fdiv (atom env a1) (atom env a2) "" the_builder
  | Eq (a1, a2) ->
      (get_eq_op (atom env a1) (atom env a2)) "" the_builder
  | LE (a1, a2) ->
      (get_le_op (atom env a1) (atom env a2)) "" the_builder
  | If (a, e1, e2) ->
      f_if_nontail env (atom env a) e1 e2
  (* | IfEq (id1, id2, e1, e2) ->
      f_if_nontail b env (build_icmp Icmp.Eq (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | IfLE (id1, id2, e1, e2) ->
      f_if_nontail b env (build_icmp Icmp.Sle (M.find id1 env)
        (M.find id2 env) "" b) e1 e2 *)
  | Let ((Var id, _), e1, e2) ->
      let v = f_nontail env e1 in
      set_value_name id v;
      f_nontail (M.add id v env) e2
  | Let ((Root id, t), e1, e2) ->
      let v = f_nontail env e1 in
      set_value_name id v;
      let a = emit_alloca (emit_type t) id v in
      let res = f_nontail (M.add id a env) e2 in
      ignore (build_store (const_null (emit_type t)) a the_builder);
      res
  | Atom a ->
      atom env a
  | MakeCls (clos) ->
      make_cls env clos
  | AppCls (a, al) ->
      app_cls env (atom env a) (List.map (atom env) al)
  | AppDir (Id.L id, al) ->
      app_dir env id (List.map (atom env) al)
  | Tuple (al) ->
      let values = Array.of_list (List.map (atom env) al) in
      let tuple_types = Array.map type_of values in
      let tuple_type = struct_type (global_context ()) tuple_types in
      let tuple = build_malloc tuple_type "" the_builder in
      (* FIXME XXX the malloc should come BEFORE the atom env a's so that
       * they are loaded after the malloc! - otherwise there is not
       * much point in spilling them to the stack. *)
      Array.iteri (fun i v ->
        ignore (build_store v
          (build_gep tuple [| const_int 32 0; const_int 32 i |] "" the_builder)
            the_builder)) values;
      tuple
  | LetTuple (atl, a, e) ->
      let env = let_tuple env atl (atom env a) in
      f_nontail env e (* should zero out the gcroots afterwards XXX *)
  | Array (a1, a2) ->
      let v1 = atom env a1 in
      let v2 = atom env a2 in
      let t2 = type_of v2 in
      let v = build_array_malloc t2 v1 "" the_builder in
      let v = build_pointercast v (pointer_type t2) "" the_builder in
      initialise_array v v1 v2;
      v
  | Get (a1, a2) ->
      build_load (build_gep (atom env a1)
        [| atom env a2 |] "" the_builder) "" the_builder
  | Put (a1, a2, a3) ->
      ignore (build_store (atom env a3) (build_gep (atom env a1)
        [| atom env a2 |] "" the_builder) the_builder);
      const_int 32 0
  | ExtArray (Id.L id, t) ->
      build_load (declare_global (pointer_type (emit_type t)) id
        (get_module ())) id the_builder
  | ExtFunApp (Id.L id, t, al) ->
      let vl = List.map (atom env) al in
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
  | If (a, e1, e2) ->
      f_if_tail env (atom env a) e1 e2
  (* | IfEq (id1, id2, e1, e2) ->
      f_if_tail b env (build_icmp Icmp.Eq (M.find id1 env)
        (M.find id2 env) "" b) e1 e2
  | IfLE (id1, id2, e1, e2) ->
      f_if_tail b env (build_icmp Icmp.Sle (M.find id1 env)
        (M.find id2 env) "" b) e1 e2 *)
  | Let ((Var id, _), e1, e2) ->
      let v = f_nontail env e1 in
      set_value_name id v;
      f_tail (M.add id v env) e2
  | Let ((Root id, t), e1, e2) ->
      let v = f_nontail env e1 in
      set_value_name id v;
      let a = emit_alloca (emit_type t) id v in
      (* don't need to zero out gcroot in tail position *)
      f_tail (M.add id a env) e2
  | AppCls (a, al) ->
      let inst = app_cls env (atom env a) (List.map (atom env) al) in
      set_tail_call true inst;
      ignore (build_ret inst the_builder)
  | AppDir (Id.L id, al) ->
      let inst = app_dir env id (List.map (atom env) al) in
      set_tail_call true inst;
      ignore (build_ret inst the_builder)
  | LetTuple (atl, a, e) ->
      let env = let_tuple env atl (atom env a) in
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
  Printf.eprintf "emitting llvm bitcode for %s\n" name;
  let f = get_function name in
  position_at_end (entry_block f) the_builder; (* this is needed so that the
  new_block "start" below works! *)
  let start = new_block "start" in
  position_at_end start the_builder;
  (* let b = builder_at_end (global_context ()) (entry_block f) in *)
  let clos = build_pointercast (param f 0) (get_closure_type fn) "clos"
    the_builder in
  let env = M.add name clos M.empty in
  let rec loop env i = function
    | [] -> env
    | (Var id, _) :: rest ->
        loop (M.add id
          (build_load
            (build_gep clos [| const_int 32 0; const_int 32 i |] id the_builder)
              id the_builder) env) (i+1) rest
    | (Root id, t) :: rest ->
        let a = emit_alloca (emit_type t) id
          (build_load
            (build_gep clos [| const_int 32 0; const_int 32 i |] id the_builder)
              id the_builder) in
        loop (M.add id a env) (i+1) rest
  in let env = loop env 1 fn.formal_fv in
  Printf.eprintf "done with first loop for %s\n" name;
  let rec loop env i = function
    | [] -> env
    | (Var id, _) :: rest ->
        set_value_name id (param f i);
        loop (M.add id (param f i) env) (i+1) rest
    | (Root id, t) :: rest ->
        set_value_name id (param f i);
        let a = emit_alloca (emit_type t) id (param f i) in
        set_value_name id a;
        loop (M.add id a env) (i+1) rest in
  let env = loop env 1 fn.args in
  Printf.eprintf "done with second loop for %s\n" name;
  flush stderr;
  f_tail env fn.body;
  position_at_end (entry_block f) the_builder;
  ignore (build_br start the_builder)

let f oc (Prog(fundefs, e)) =
  (* XXX fix gcroots in main () *)
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
