module Somewhere.Schanuel

import Data.List
import Somewhere.Species
import Somewhere.Thinning

%default total

--Can't solve constraint between:
--        ?a [no locals in scope]
--and
--        .a rec
--
--record Sh (t : List a -> Type) (scope : List a) where
--  constructor MkSh
--  {support : List a}
--  element : t support
--  thinning : Thin support scope

data Sh : Sp a -> Sp a where
  MkSh : {sup : List a} -> t sup -> Thin sup sco -> Sh t sco

mapSh : (s :-> t) -> (Sh s :-> Sh t)
mapSh f (MkSh ts th) = MkSh (f ts) th

pureSh : t :-> Sh t
pureSh tx = MkSh tx (I x)

-- TODO LHS printing goes crazy here
bindSh : Sh (Sh t) :-> Sh t
bindSh (MkSh (MkSh ts th) th2) = MkSh ts (compThin th th2)

thinSh : Thin xs ys -> Sh t xs -> Sh t ys
thinSh th (MkSh ts th2) = MkSh ts (compThin th2 th)

infixr 1 :=>
(:=>) : Sp a -> Sp a -> Type
(:=>) s t = s :-> Sh t

infixr 1 =<<
public export
(=<<) : (s :=> t) -> (Sh s :-> Sh t)
(=<<) f sh = bindSh $ mapSh f sh