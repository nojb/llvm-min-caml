type t =
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
  | ExtArray of Id.t * Type.t (* element type *)
  | ExtFunApp of Id.t * Type.t * Id.t list
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

val fv : t -> S.t
val f : Syntax.t -> t
