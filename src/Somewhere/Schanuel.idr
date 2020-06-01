module Somewhere.Schanuel

import Data.List
import Somewhere.Species
import Somewhere.Thinning
import Somewhere.Thinning.Slice

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

public export
data Sh : Sp a -> Sp a where
  MkSh : {sup : List a} -> t sup -> Thin sup sco -> Sh t sco

export
thinning : Sh s t -> (sup ** Thin sup t)
thinning (MkSh {sup} _ t) = (sup ** t)

export
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
public export
(:=>) : Sp a -> Sp a -> Type
(:=>) s t = s :-> Sh t

infixr 1 =<<
public export
(=<<) : (s :=> t) -> (Sh s :-> Sh t)
(=<<) f sh = bindSh $ mapSh f sh

-- Can't solve constraint between:
--         ?a [no locals in scope]
-- and
--         .a rec
--
-- record Ten (s, t : Sp a) (zs : List a) where
--   constructor MkTen
--   proj1 : Sh s zs
--   proj2 : Sh t zs
--   cover : Cover True (snd $ thinning proj1) (snd $ thinning proj2)

public export
data Ten : Sp a -> Sp a -> Sp a where
  MkTen : (proj1 : Sh s zs) -> (proj2 : Sh t zs) -> Cover True (snd $ thinning proj1) (snd $ thinning proj2) -> Ten s t zs

Proj1 : Ten s t zs -> Sh s zs
Proj1 (MkTen p1 _ _) = p1

Proj2 : Ten s t zs -> Sh t zs
Proj2 (MkTen _ p2 _) = p2

Cover : Ten s t zs -> Sh t zs

mkPair : (shs : Sh s zs) -> (sht : Sh t zs) -> Coproduct (snd $ thinning shs) (snd $ thinning sht) -> Sh (Ten s t) zs
mkPair (MkSh tss ths) (MkSh tst tht) (MkCoproduct {thinning = th} {txs} {tys} tl cv tr) = MkSh (MkTen (MkSh tss txs) (MkSh tst tys) cv) th

export
pair : {zs : List a} -> Sh s zs -> Sh t zs -> Sh (Ten s t) zs
pair shs@(MkSh tss ths) sht@(MkSh tst tht) = mkPair shs sht (coproduct ths tht)

beta1 : {zs : List a} -> (shs : Sh s zs) -> (sht : Sh t zs) -> (Proj1 =<< pair shs sht) = shs
beta1 (MkSh tss ths) (MkSh tst tht) with (coproduct ths tht)
  beta1 (MkSh tss ths) (MkSh tst tht) | MkCoproduct tl cv tr = cong (MkSh tss) (lemma2 tl)

beta2 : {zs : List a} -> (shs : Sh s zs) -> (sht : Sh t zs) -> (Proj2 =<< pair shs sht) = sht
beta2 (MkSh tss ths) (MkSh tst tht) with (coproduct ths tht)
  beta2 (MkSh tss ths) (MkSh tst tht) | MkCoproduct tl cv tr = cong (MkSh tst) (lemma2 tr)

-- etaSublemma

etaLemma : {zs : List a} -> (ps : Sh (Ten s t) zs) -> pair (Proj1 =<< ps) (Proj2 =<< ps) = ps
etaLemma ps@(MkSh (MkTen (MkSh ss ths) (MkSh ts tht) cv) th) =
  rewrite coproductUnique (coproduct (compThin ths th) (compThin tht th)) self in
  Refl
  where
    self : Coproduct (compThin ths th) (compThin tht th)
    self = MkCoproduct triId cv triId

public export
data Bind : List a -> Sp a -> Sp a where
  MkBind : {xs : List a} -> Thin xs ys -> t (xs ++ zs) -> Bind ys t zs

mkBinding : t xys -> Splitting xys ys zs th -> Sh (Bind ys t) zs
mkBinding txys (MkSplitting th1 th2 (Refl ** Refl)) = MkSh (MkBind th1 txys) th2

export
iso1 : {ys : List a} -> Hom (flip (++)) (Cx ys) (Sh t) :-> Sh (Bind ys t)
iso1 f = case f Refl MkCx of
    MkSh ts th => mkBinding ts (splitThin ys th)

iso2 : {ys : List a} -> Sh (Bind ys t) :-> Hom (flip (++)) (Cx ys) (Sh t)
iso2 (MkSh (MkBind th ta) th2) Refl MkCx = MkSh ta (thinAppend th th2)

--lemma1 : (xs, ys, yzs, zs : List a)
--       -> (f : Hom (flip (++)) (Cx ys) (Sh t) zs)
--       -> (eq : xs ++ zs = yzs)
--       -> (c : Cx ys xs)
--       -> iso2 (iso1 f) eq c = f eq c
--lemma1 f eq c = ?wat

lemma2 : {ys : List a} -> (zs : List a) -> (f : Sh (Bind ys t) zs) -> iso1 (iso2 f) = f
lemma2 zs (MkSh (MkBind th ta) th2) =
  rewrite splitUnique (thinAppend th th2) (splitThin ys (thinAppend th th2)) (alreadySplit th th2) in
  Refl