let rec g a b c =
  (a, b, c) 
in
let rec f a b c =
  let t = (a, b, c) in
  g t t 23
in
f 1 2 3
