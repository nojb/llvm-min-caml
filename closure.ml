open Prim

type closure = { entry : Id.l * Type.t; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Prim of primitive * Id.t list
  | If of Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of closure
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | ExtArray of Id.l * Type.t
  | ExtFunApp of Id.l * Type.t * Id.t list
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type prog = Prog of fundef list * t

let rec fv = function
  | Unit | Bool(_) | Int(_) | Float(_) | ExtArray(_, _) -> S.empty
  | Prim (_, xs) -> S.of_list xs
  | If(x, e1, e2) -> S.add x (S.union (fv e1) (fv e2))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls({ entry = l; actual_fv = ys }) -> S.of_list ys
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | ExtFunApp (_, _, xs)
  | AppDir(_, xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))

let toplevel : fundef list ref = ref []

let rec g env known = function (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Bool(b) -> Bool(b)
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Prim (p, xs) -> Prim (p, xs)
  | KNormal.If(x, e1, e2) -> If(x, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (M.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
      (* 関数定義let rec x y1 ... yn = e1 in e2の場合は、
	 xに自由変数がない(closureを介さずdirectに呼び出せる)
	 と仮定し、knownに追加してe1をクロージャ変換してみる *)
      let toplevel_backup = !toplevel in
      let env' = M.add x t env in
      let known' = S.add x known in
      let e1' = g (M.add_list yts env') known' e1 in
      (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
      (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
      let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
      let known', e1' =
	if S.is_empty zs then known', e1' else
	(* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
	(Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	 Format.eprintf "function %s cannot be directly applied in fact@." x;
	 toplevel := toplevel_backup;
	 let e1' = g (M.add_list yts env') known e1 in
	 known, e1') in
      let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* 自由変数のリスト *)
      let zts = List.map (fun z -> (z, M.find z env')) zs in (* ここで自由変数zの型を引くために引数envが必要 *)
      toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
      let e2' = g env' known' e2 in
      if S.mem x (fv e2') then (* xが変数としてe2'に出現するか *)
	Let ((x, t), MakeCls { entry = (Id.L(x), t); actual_fv = zs }, e2') (* 出現していたら削除しない *)
      else
	(Format.eprintf "eliminating closure(s) %s@." x;
	 e2') (* 出現しなければMakeClsを削除 *)
  | KNormal.App(x, ys) when S.mem x known -> (* 関数適用の場合 (caml2html: closure_app) *)
      Format.eprintf "directly applying %s@." x;
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.ExtArray(x, t) -> ExtArray(Id.L(x), t)
  | KNormal.ExtFunApp(x, t, ys) -> ExtFunApp (Id.L ("min_caml_" ^ x), t, ys) (*
  AppDir(Id.L("min_caml_" ^ x), ys) *)

let f e =
  toplevel := [];
  let e' = g M.empty S.empty e in
  Prog(List.rev !toplevel, e')
