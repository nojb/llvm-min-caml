type atom =
  | Var of Id.t
  | Root of Id.t

type closure = { entry : Id.l * Type.t; actual_fv : atom list }

type t =
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Prim of Prim.primitive * atom list
  | If of atom * t * t
  | Let of (atom * Type.t) * t * t
  | Atom of atom
  | MakeCls of closure
  | AppCls of atom * atom list
  | AppDir of Id.l * atom list
  | LetTuple of (atom * Type.t) list * atom * t
  | ExtArray of Id.l * Type.t
  | ExtFunApp of Id.l * Type.t * atom list

val triggers : Closure.t -> bool
val roots : Closure.t -> S.t
val g : bool M.t -> Closure.t -> t

type fundef = { name : Id.l * Type.t;
  args : (atom * Type.t) list;
  formal_fv : (atom * Type.t) list;
  body : t }

type prog = Prog of fundef list * t

val f_fundef : Closure.fundef -> fundef
val f : Closure.prog -> prog
