module Somewhere.Ctx

%access public export
%default total

parameters (prop : (a, b : t) -> a = b)
  sizeLem : (xs, ys : List t) -> length xs = length ys -> xs = ys
  sizeLem []      []      Refl = Refl
  sizeLem []      (y::ys) prf = absurd prf
  sizeLem (x::xs) []      prf = absurd prf
  sizeLem (x::xs) (y::ys) prf = rewrite prop x y in
                                cong {f=(::) y} $ sizeLem xs ys (succInjective (length xs) (length ys) prf)

  symAppend : (xs, ys : List t) -> xs ++ ys = ys ++ xs
  symAppend xs ys = sizeLem (xs ++ ys) (ys ++ xs)
                            (rewrite lengthAppend xs ys in
                             rewrite lengthAppend ys xs in
                             plusCommutative (length xs) (length ys))