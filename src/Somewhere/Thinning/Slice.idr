module Somewhere.Thinning.Slice

import Data.List
import Somewhere.Thinning

%default total

infixr 1 :->/
(:->/) : {xs, ys : List a} -> Thin xs zs -> Thin ys zs -> Type
(:->/) txz tyz = (txy : Thin xs ys ** CompGraph txy tyz txz)

data Cover : Bool -> Thin xs xys -> Thin ys xys -> Type where
  NilC   : Cover b    Nil Nil
  Take1C : Cover b    tx ty -> Cover b    (Take tx) (Skip ty)
  Take2C : Cover b    tx ty -> Cover b    (Skip tx) (Take ty)
  TakesC : Cover True tx ty -> Cover True (Take tx) (Take ty)

coverUnique : (c1, c2 : Cover b tx ty) -> c1 = c2
coverUnique  NilC        NilC       = Refl
coverUnique (Take1C c1) (Take1C c2) = cong Take1C $ coverUnique c1 c2
coverUnique (Take2C c1) (Take2C c2) = cong Take2C $ coverUnique c1 c2
coverUnique (TakesC c1) (TakesC c2) = cong TakesC $ coverUnique c1 c2