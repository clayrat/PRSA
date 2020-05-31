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

-- TODO https://github.com/idris-lang/Idris2/issues/213
-- Can't bind implicit Somewhere.Thinning.Slice.{a:12030} of type {a:12023}[7]
--Uninhabited ({a : Type} -> {ys : List a} -> Cover b (Skip t1) (Skip t2)) where
--  uninhabited NilC impossible

notSkipSkip : Not (Cover b (Skip t1) (Skip t2))
notSkipSkip NilC impossible

coverUnique : (c1, c2 : Cover b tx ty) -> c1 = c2
coverUnique  NilC        NilC       = Refl
coverUnique (Take1C c1) (Take1C c2) = cong Take1C $ coverUnique c1 c2
coverUnique (Take2C c1) (Take2C c2) = cong Take2C $ coverUnique c1 c2
coverUnique (TakesC c1) (TakesC c2) = cong TakesC $ coverUnique c1 c2

--Can't solve constraint between:
--        ?a [no locals in scope]
--and
--        .a rec
--
--record Coproduct (txz : Thin xs zs) (tyz : Thin ys zs) where
--  constructor MkCoproduct
--  {support : List a}
--  {thinning : Thin support zs}
--  {txs : Thin xs support}
--  {tys : Thin ys support}
--  factor1 : CompGraph txs thinning txz
--  cover : Cover True txs tys
--  factor2 : CompGraph tys thinning tyz

data Coproduct : Thin xs zs -> Thin ys zs -> Type where
  MkCoproduct :
      {support : List a}
   -> {thinning : Thin support zs}
   -> {txs : Thin xs support}
   -> {tys : Thin ys support}
   -> (factor1 : CompGraph txs thinning txz)
   -> (cover : Cover True txs tys)
   -> (factor2 : CompGraph tys thinning tyz)
   -> Coproduct txz tyz

coproduct : {zs : List a} -> (txz : Thin xs zs) -> (tyz : Thin ys zs) -> Coproduct txz tyz
coproduct  Nil        Nil       = MkCoproduct NilG NilC NilG
coproduct (Skip txz) (Skip tyz) = case coproduct txz tyz of
  MkCoproduct tl cv tr => MkCoproduct (SkipR tl) cv (SkipR tr)
coproduct (Skip txz) (Take tyz) = case coproduct txz tyz of
  MkCoproduct tl cv tr => MkCoproduct (SkipL tl) (Take2C cv) (Take2 tr)
coproduct (Take txz) (Skip tyz) = case coproduct txz tyz of
  MkCoproduct tl cv tr => MkCoproduct (Take2 tl) (Take1C cv) (SkipL tr)
coproduct (Take txz) (Take tyz) = case coproduct txz tyz of
  MkCoproduct tl cv tr => MkCoproduct (Take2 tl) (TakesC cv) (Take2 tr)

coproductUnversal :
     {txz  : Thin xs  zs}
  -> {txxy : Thin xs  xys}
  -> {tyz  : Thin ys  zs}
  -> {tyxy : Thin ys  xys}
  -> {txyz  : Thin xys zs}
  -> (t1 : CompGraph txxy txyz txz)
  -> Cover True txxy tyxy
  -> (t2 : CompGraph tyxy txyz tyz)
  -> {twz : Thin ws zs}
  -> txz :->/ twz
  -> tyz :->/ twz
  -> txyz :->/ twz
coproductUnversal  NilG              c   NilG       (Nil ** NilG)          (Nil ** NilG)          = (Nil ** NilG)
coproductUnversal (SkipL t1)         c  (SkipL t2)   sl1                    sl2                   = void $ notSkipSkip c
coproductUnversal (SkipR t1)         c  (SkipR t2)  (Skip txy1**SkipL cg1) (Skip txy2**SkipL cg2) =
  case coproductUnversal t1 c t2 (txy1**cg1) (txy2**cg2) of
    (txy ** cgxy) => (Skip txy ** SkipL cgxy)
coproductUnversal (SkipR t1)         c  (SkipR t2)  (     txy1**SkipR cg1) (     txy2**SkipR cg2) =
  case coproductUnversal t1 c t2 (txy1**cg1) (txy2**cg2) of
    (txy ** cgxy) => (txy ** SkipR cgxy)
coproductUnversal (Take2 t1) (Take1C c) (SkipL t2)  (Take txy1**Take2 cg1) (Skip txy2**SkipL cg2) =
  case coproductUnversal t1 c t2 (txy1**cg1) (txy2**cg2) of
    (txy ** cgxy) => (Take txy ** Take2 cgxy)
coproductUnversal (SkipL t1) (Take2C c) (Take2 t2)  (Skip txy1**SkipL cg1) (Take txy2**Take2 cg2) =
  case coproductUnversal t1 c t2 (txy1**cg1) (txy2**cg2) of
    (txy ** cgxy) => (Take txy ** Take2 cgxy)
coproductUnversal (Take2 t1)         c  (SkipR t2)   sl1                    sl2                   impossible
coproductUnversal (SkipR t1)         c  (Take2 t2)   sl1                    sl2                   impossible
coproductUnversal (Take2 t1) (TakesC c) (Take2 t2)  (Take txy1**Take2 cg1) (Take txy2**Take2 cg2) =
  case coproductUnversal t1 c t2 (txy1**cg1) (txy2**cg2) of
    (txy ** cgxy) => (Take txy ** Take2 cgxy)

pull : {tx : Thin xs zs} -> {ty : Thin ys zs}
    -> Cover b tx ty -> (tz : Thin zs1 zs)
    -> (xs1 ** ys1 ** tx1 : Thin xs1 zs1 ** ty1 : Thin ys1 zs1 ** Cover b tx1 ty1)
pull  NilC       Nil          = ([] ** [] ** Nil ** Nil ** NilC)
pull (Take1C c) (Skip tz)     = pull c tz
pull (Take1C c) (Take {y} tz) = case pull c tz of
  (xs1 ** ys1 ** tx1 ** ty1 ** c1) => (y::xs1 ** ys1 ** Take tx1 ** Skip ty1 ** Take1C c1)
pull (Take2C c) (Skip tz)     = pull c tz
pull (Take2C c) (Take {y} tz) = case pull c tz of
  (xs1 ** ys1 ** tx1 ** ty1 ** c1) => (xs1 ** y::ys1 ** Skip tx1 ** Take ty1 ** Take2C c1)
pull (TakesC c) (Skip tz)     = pull c tz
pull (TakesC c) (Take {y} tz) = case pull c tz of
  (xs1 ** ys1 ** tx1 ** ty1 ** c1) => (y::xs1 ** y::ys1 ** Take tx1 ** Take ty1 ** TakesC c1)

coproductUnique : {tx : Thin xs zs} -> {ty : Thin ys zs}
               -> (c1, c2 : Coproduct tx ty) -> c1 = c2
coproductUnique (MkCoproduct  NilG        NilC        NilG      ) (MkCoproduct  NilG        NilC        NilG)       = Refl
coproductUnique (MkCoproduct (SkipL f11) (Take2C c1) (Take2 f12)) (MkCoproduct (SkipL f21) (Take2C c2) (Take2 f22)) =
  case coproductUnique (MkCoproduct f11 c1 f12) (MkCoproduct f21 c2 f22) of
    Refl => Refl
coproductUnique (MkCoproduct (SkipL f11) (Take2C c1) (Take2 f12)) (MkCoproduct (SkipR f21)  c2          f22       ) = absurd f22
coproductUnique (MkCoproduct (SkipL f11)  c1          f12       ) (MkCoproduct (Take2 f21)  c2          f22       ) impossible
coproductUnique (MkCoproduct (SkipR f11)  c1          f12       ) (MkCoproduct (SkipL f21) (Take2C c2) (Take2 f22)) = absurd f12
coproductUnique (MkCoproduct (SkipR f11)  c1         (SkipR f12)) (MkCoproduct (SkipR f21)  c2         (SkipR f22)) =
  case coproductUnique (MkCoproduct f11 c1 f12) (MkCoproduct f21 c2 f22) of
    Refl => Refl
coproductUnique (MkCoproduct (SkipR f11)  c1          f12       ) (MkCoproduct (Take2 f21)  c2          f22       ) impossible
coproductUnique (MkCoproduct (Take2 f11) (Take1C c1) (SkipL f12)) (MkCoproduct (Take2 f21) (Take1C c2) (SkipL f22)) =
  case coproductUnique (MkCoproduct f11 c1 f12) (MkCoproduct f21 c2 f22) of
    Refl => Refl
coproductUnique (MkCoproduct (Take2 f11) (TakesC c1) (Take2 f12)) (MkCoproduct (Take2 f21) (TakesC c2) (Take2 f22)) =
  case coproductUnique (MkCoproduct f11 c1 f12) (MkCoproduct f21 c2 f22) of
    Refl => Refl

coverAppend : {tx  : Thin xs  zs}
           -> {ty  : Thin ys  zs}
           -> {tx1 : Thin xs1 zs1}
           -> {ty1 : Thin ys1 zs1}
           -> Cover b tx ty
           -> Cover b tx1 ty1
           -> Cover b (thinAppend tx tx1) (thinAppend ty ty1)
coverAppend  NilC      c1 = c1
coverAppend (Take1C c) c1 = Take1C $ coverAppend c c1
coverAppend (Take2C c) c1 = Take2C $ coverAppend c c1
coverAppend (TakesC c) c1 = TakesC $ coverAppend c c1

coverConcat : (xs, ys : List a) -> (tx : Thin xs (xs ++ ys) ** ty : Thin ys (xs ++ ys) ** Cover b tx ty)
coverConcat []      []      = (Nil ** Nil ** NilC)
coverConcat []      (y::ys) = case coverConcat [] ys of
  (tx ** ty ** c) => (Skip tx ** Take ty ** Take2C c)
coverConcat (x::xs) ys      = case coverConcat xs ys of
  (tx ** ty ** c) => (Take tx ** Skip ty ** Take1C c)
