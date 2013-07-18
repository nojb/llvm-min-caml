open KNormal

let find x env = try M.find x env with Not_found -> x (* 置換のための関数 (caml2html: beta_find) *)

let rec g env = function (* β簡約ルーチン本体 (caml2html: beta_g) *)
  | Unit -> Unit
  | Bool(b) -> Bool(b)
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Prim (p, xs) -> Prim (p, List.map (fun x -> find x env) xs)
  | If(x, e1, e2) -> If(find x env, g env e1, g env e2)
  | Let((x, t), e1, e2) -> (* letのβ簡約 (caml2html: beta_let) *)
      (match g env e1 with
      | Var(y) ->
	  Format.eprintf "beta-reducing %s = %s@." x y;
	  g (M.add x y env) e2
      | e1' ->
	  let e2' = g env e2 in
	  Let((x, t), e1', e2'))
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = xt; args = yts; body = g env e1 }, g env e2)
  | Var(x) -> Var(find x env) (* 変数を置換 (caml2html: beta_var) *)
  | LetTuple(xts, y, e) -> LetTuple(xts, find y env, g env e)
  | App(g, xs) -> App(find g env, List.map (fun x -> find x env) xs)
  | ExtArray(x, t) -> ExtArray(x, t)
  | ExtFunApp(x, t, ys) -> ExtFunApp(x, t, List.map (fun y -> find y env) ys)

let f = g M.empty
