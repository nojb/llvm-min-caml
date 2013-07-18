open KNormal
open Prim

let memb x env =
  try (match M.find x env with Bool(_) -> true | _ -> false)
  with Not_found -> false
let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Prim (Pmaketuple, _) -> true | _ -> false)
  with Not_found -> false

let findb x env = (match M.find x env with Bool(b) -> b | _ -> raise Not_found)
let findi x env = (match M.find x env with Int(i) -> i | _ -> raise Not_found)
let findf x env = (match M.find x env with Float(d) -> d | _ -> raise Not_found)
let findt x env = (match M.find x env with Prim (Pmaketuple, ys) -> ys | _ -> raise Not_found)

let rec g env = function (* 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  | Var(x) when memi x env -> Int(findi x env)
  (* | Var(x) when memf x env -> Float(findf x env) *)
  (* | Var(x) when memt x env -> Tuple(findt x env) *)
  | Prim (Pnot, [x]) when memb x env -> Bool(not (findb x env))
  | Prim (Pnegint, [x]) when memi x env -> Int(-(findi x env))
  | Prim (Paddint, [x; y]) when memi x env && memi y env -> Int(findi x env + findi y env) (* 足し算のケース (caml2html: constfold_add) *)
  | Prim (Psubint, [x; y]) when memi x env && memi y env -> Int(findi x env - findi y env)
  | Prim (Pnegfloat, [x]) when memf x env -> Float(-.(findf x env))
  | Prim (Paddfloat, [x; y]) when memf x env && memf y env -> Float(findf x env +. findf y env)
  | Prim (Psubfloat, [x; y]) when memf x env && memf y env -> Float(findf x env -. findf y env)
  | Prim (Pmulfloat, [x; y]) when memf x env && memf y env -> Float(findf x env *. findf y env)
  | Prim (Pdivfloat, [x; y]) when memf x env && memf y env -> Float(findf x env /. findf y env)
  | Prim (Ptest Peq_test, [x; y]) when memb x env && memb y env -> Bool(findb x env = findb y env)
  | Prim (Ptest Peq_test, [x; y]) when memi x env && memi y env -> Bool(findi x env = findi y env)
  | Prim (Ptest Peq_test, [x; y]) when memf x env && memf y env -> Bool(findf x env = findf y env)
  | Prim (Ptest (Pint_test PTle), [x; y]) when memi x env && memi y env ->
      Bool(findi x env <= findi y env)
  | Prim (Ptest (Pfloat_test PTle), [x; y]) when memf x env && memf y env ->
      Bool(findf x env <= findf y env)
  | If(x, e1, e2) when memb x env -> if findb x env then g env e1 else g env e2
  | If(x, e1, e2) -> If(x, g env e1, g env e2)
  (* | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env e1 else g env e2
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env e1 else g env e2
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2) *)
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
      let e1' = g env e1 in
      let e2' = g (M.add x e1' env) e2 in
      Let((x, t), e1', e2')
  | LetRec({ name = x; args = ys; body = e1 }, e2) ->
      LetRec({ name = x; args = ys; body = g env e1 }, g env e2)
  | LetTuple(xts, y, e) when memt y env ->
      List.fold_left2
	(fun e' xt z -> Let(xt, Var(z), e'))
	(g env e)
	xts
	(findt y env)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e)
  | e -> e

let f = g M.empty
