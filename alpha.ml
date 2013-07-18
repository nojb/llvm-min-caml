(* rename identifiers to make them unique (alpha-conversion) *)

open KNormal

let find x env = try M.find x env with Not_found -> x

let rec g env = function (* α変換ルーチン本体 (caml2html: alpha_g) *)
  | Unit -> Unit
  | Bool(b) -> Bool(b)
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Prim (p, xs) -> Prim (p, List.map (fun x -> find x env) xs)
  | If(x, e1, e2) -> If(find x env, g env e1, g env e2)
  | Let((x, t), e1, e2) -> (* letのα変換 (caml2html: alpha_let) *)
      let x' = Id.genid x in
      Let((x', t), g env e1, g (M.add x x' env) e2)
  | Var(x) -> Var(find x env)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recのα変換 (caml2html: alpha_letrec) *)
      let env = M.add x (Id.genid x) env in
      let ys = List.map fst yts in
      let env' = M.add_list2 ys (List.map Id.genid ys) env in
      LetRec({ name = (find x env, t);
	       args = List.map (fun (y, t) -> (find y env', t)) yts;
	       body = g env' e1 },
	     g env e2)
  | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys)
  | LetTuple(xts, y, e) -> (* LetTupleのα変換 (caml2html: alpha_lettuple) *)
      let xs = List.map fst xts in
      let env' = M.add_list2 xs (List.map Id.genid xs) env in
      LetTuple(List.map (fun (x, t) -> (find x env', t)) xts,
	       find y env,
	       g env' e)
  | ExtArray(x, t) -> ExtArray(x, t)
  | ExtFunApp(x, t, ys) -> ExtFunApp(x, t, List.map (fun y -> find y env) ys)

let f = g M.empty
