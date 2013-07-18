type primitive =
  | Ptest of bool_test
  | Pnot
  | Pnegint
  | Paddint | Psubint
  | Pnegfloat
  | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
  | Pmakearray | Pget | Pput
  | Pmaketuple

and bool_test =
  | Peq_test
  | Pnoteq_test
  | Pint_test of prim_test
  | Pfloat_test of prim_test

and prim_test =
  | PTeq
  | PTle
