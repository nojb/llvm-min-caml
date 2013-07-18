type closure = { entry : Id.l * Type.t; actual_fv : Id.t list }
type t =
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Prim of Prim.primitive * Id.t list
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

val fv : t -> S.t
val f : KNormal.t -> prog
