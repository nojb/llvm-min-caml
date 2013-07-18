open Prim

(* give names to intermediate values (K-normalization) *)

type t = (* K正規化後の式 (caml2html: knormal_t) *)
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Prim of Prim.primitive * Id.t list
  | If of Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | ExtArray of Id.t * Type.t
  | ExtFunApp of Id.t * Type.t * Id.t list
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec fv = function (* 式に出現する（自由な）変数 (caml2html: knormal_fv) *)
  | Unit | Bool _ | Int(_) | Float(_) | ExtArray(_, _) -> S.empty
  | Prim (_, xs) -> S.of_list xs
  | If(x, e1, e2) -> S.add x (S.union (fv e1) (fv e2))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = S.diff (fv e1) (S.of_list (List.map fst yts)) in
      S.diff (S.union zs (fv e2)) (S.singleton x)
  | App(x, ys) -> S.of_list (x :: ys)
  | ExtFunApp(_, _, xs) -> S.of_list xs
  | LetTuple(xs, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xs)))

let insert_let (e, t) k = (* letを挿入する補助関数 (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
      let x = Id.gentmp t in
      let e', t' = k x in
      Let((x, t), e, e'), t'

let rec g env = function (* K正規化ルーチン本体 (caml2html: knormal_g) *)
  | Syntax.Unit -> Unit, Type.Unit
  | Syntax.Bool(b) -> Bool b, Type.Bool
  | Syntax.Int(i) -> Int(i), Type.Int
  | Syntax.Float(d) -> Float(d), Type.Float
  | Syntax.Not(e) ->
      insert_let (g env e) (fun x ->
        Prim (Pnot, [x]), Type.Bool)
  | Syntax.Neg(e) ->
      insert_let (g env e)
    (fun x -> Prim (Pnegint, [x]), Type.Int)
  | Syntax.Add(e1, e2) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Prim (Paddint, [x; y]), Type.Int))
  | Syntax.Sub(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
    (fun y -> Prim (Psubint, [x; y]), Type.Int))
  | Syntax.FNeg(e) ->
      insert_let (g env e)
    (fun x -> Prim (Pnegfloat, [x]), Type.Float)
  | Syntax.FAdd(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
    (fun y -> Prim (Paddfloat, [x; y]), Type.Float))
  | Syntax.FSub(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
    (fun y -> Prim (Psubfloat, [x; y]), Type.Float))
  | Syntax.FMul(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Prim (Pmulfloat, [x; y]), Type.Float))
  | Syntax.FDiv(e1, e2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Prim (Pdivfloat, [x; y]), Type.Float))
  | Syntax.Eq (e1, e2) ->
      insert_let (g env e1) (fun x ->
  insert_let (g env e2) (fun y ->
      Prim (Ptest Peq_test, [x; y]), Type.Bool))
  | Syntax.LE (e1, e2) ->
      insert_let (g env e1) (fun x ->
    insert_let (g env e2) (fun y -> (* XXX only handles integer LE *)
        Prim (Ptest (Pint_test PTle), [x; y]), Type.Bool))
  | Syntax.If(e1, e2, e3) ->
      insert_let (g env e1) (fun x ->
        let e2', t2 = g env e2 in
        let e3', t3 = g env e3 in
        If (x, e2', e3'), t2)
  | Syntax.Let((x, t), e1, e2) ->
      let e1', t1 = g env e1 in
      let e2', t2 = g (M.add x t env) e2 in
      Let((x, t), e1', e2'), t2
  | Syntax.Var(x) when M.mem x env -> Var(x), M.find x env
  | Syntax.Var(x) -> (* 外部配列の参照 (caml2html: knormal_extarray) *)
      (match M.find x !Typing.extenv with
      | Type.Array(t') as t -> ExtArray (x, t'), t
      | _ -> failwith (Printf.sprintf "external variable %s does not have an array type" x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
      let env' = M.add x t env in
      let e2', t2 = g env' e2 in
      let e1', t1 = g (M.add_list yts env') e1 in
      LetRec({ name = (x, t); args = yts; body = e1' }, e2'), t2
  | Syntax.App(Syntax.Var(f), e2s) when not (M.mem f env) -> (* 外部関数の呼び出し (caml2html: knormal_extfunapp) *)
      (match M.find f !Typing.extenv with
      | Type.Fun(_, t) ->
	  let rec bind xs = function (* "xs" are identifiers for the arguments *)
	    | [] -> ExtFunApp(f, t, xs), t
	    | e2 :: e2s ->
		insert_let (g env e2)
		  (fun x -> bind (xs @ [x]) e2s) in
	  bind [] e2s (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.App(e1, e2s) ->
      (match g env e1 with
      | _, Type.Fun(_, t) as g_e1 ->
	  insert_let g_e1
	    (fun f ->
	      let rec bind xs = function (* "xs" are identifiers for the arguments *)
		| [] -> App(f, xs), t
		| e2 :: e2s ->
		    insert_let (g env e2)
		      (fun x -> bind (xs @ [x]) e2s) in
	      bind [] e2s) (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.Tuple(es) ->
      let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
	| [] -> Prim (Pmaketuple, xs), Type.Tuple(ts)
	| e :: es ->
	    let _, t as g_e = g env e in
	    insert_let g_e
	      (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
      bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
      insert_let (g env e1)
	(fun y ->
	  let e2', t2 = g (M.add_list xts env) e2 in
	  LetTuple(xts, y, e2'), t2)
  | Syntax.Array(e1, e2) ->
      insert_let (g env e1)
	(fun x ->
	  let _, t2 as g_e2 = g env e2 in
	  insert_let g_e2
	    (fun y ->
        Prim (Pmakearray, [x; y]), Type.Array(t2)))
	      (* let l =
		match t2 with
		| Type.Float -> "create_float_array"
		| _ -> "create_array" in
	      ExtFunApp(l, Type.Array(t2), [x; y]), Type.Array(t2))) *)
  | Syntax.Get(e1, e2) ->
      (match g env e1 with
      |	_, Type.Array(t) as g_e1 ->
	  insert_let g_e1
	    (fun x -> insert_let (g env e2)
		(fun y -> Prim (Pget, [x; y]), t))
      | _ -> assert false)
  | Syntax.Put(e1, e2, e3) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> insert_let (g env e3)
		(fun z -> Prim (Pput, [x; y; z]), Type.Unit)))

let f e = fst (g M.empty e)
