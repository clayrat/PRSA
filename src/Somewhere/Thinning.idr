module Somewhere.Thinning

import Data.List

--%access public export
%default total

-- thinning aka order-preserving embedding
data Thin : List a -> List a -> Type where
  Nil  : Thin [] []
  Skip : Thin xs ys -> Thin xs      (a::ys)
  Take : Thin xs ys -> Thin (a::xs) (a::ys)

skips : {xs : List a} -> Thin [] xs
skips {xs=[]}   = Nil
skips {xs=_::_} = Skip skips

skipsInv : (snx : Thin [] xs) -> snx = skips {xs}
skipsInv  Nil     = Refl
skipsInv (Skip s) = cong Skip $ skipsInv s

I : (xs : List a) -> Thin xs xs
I [] = Nil
I (x::xs) = Take $ I xs

compThin : Thin xs ys -> Thin ys zs -> Thin xs zs
compThin  txy       (Skip tyz) = Skip $ compThin txy tyz
compThin (Skip txy) (Take tyz) = Skip $ compThin txy tyz
compThin (Take txy) (Take tyz) = Take $ compThin txy tyz
compThin  Nil       Nil      = Nil

idComp : (s : Thin xs ys) -> compThin (I xs) s = s
idComp  Nil     = Refl
idComp (Skip s) = cong Skip $ idComp s
idComp (Take s) = cong Take $ idComp s

compId : (s : Thin xs ys) -> compThin s (I ys) = s
compId  Nil     = Refl
compId (Skip s) = cong Skip $ compId s
compId (Take s) = cong Take $ compId s

compAssoc : (twx : Thin ws xs) ->
            (txy : Thin xs ys) ->
            (tyz : Thin ys zs) ->
            compThin twx (compThin txy tyz) = compThin (compThin twx txy) tyz
compAssoc  twx        txy       (Skip tyz) = cong Skip $ compAssoc twx txy tyz
compAssoc  twx       (Skip txy) (Take tyz) = cong Skip $ compAssoc twx txy tyz
compAssoc (Skip twx) (Take txy) (Take tyz) = cong Skip $ compAssoc twx txy tyz
compAssoc (Take twx) (Take txy) (Take tyz) = cong Take $ compAssoc twx txy tyz
compAssoc  Nil        Nil        Nil       = Refl

bij : List a -> List a -> Type
bij xs ys = (Thin xs ys, Thin ys xs)

eqBij : {xs : List a} -> xs = ys -> bij xs ys
eqBij Refl = (I xs, I xs)

notThinsEmp : Not (Thin (x::xs) [])
notThinsEmp Nil impossible

-- this clashes with the later instance on `Thin [x] []`

--Uninhabited (Thin (x::xs) []) where
--  uninhabited = notThinsEmp

lp : Thin (x::xs) ys -> Thin xs ys
lp (Skip s) = Skip $ lp s
lp (Take s) = Skip s

Uninhabited (Thin (x::xs) xs) where
  uninhabited Nil impossible
  uninhabited (Skip s) = uninhabited $ lp s
  uninhabited (Take s) = uninhabited s

antiSym : bij xs ys -> xs = ys
antiSym (Nil, tyx) = Refl
antiSym (Take {a} txy, Take tyx) = cong (a ::) $ antiSym (txy, tyx)
antiSym (Skip txy, tyx) = absurd $ compThin tyx txy
antiSym (txy, Skip tyx) = absurd $ compThin txy tyx

thin : (txx : Thin xs xs) -> txx = I xs
thin  Nil     = Refl
thin (Skip s) = absurd s
thin (Take s) = cong Take $ thin s

data CompGraph : Thin xs ys -> Thin ys zs -> Thin xs zs -> Type where
  NilG  : CompGraph Nil Nil Nil
  SkipR : CompGraph txy tyz txz -> CompGraph (Skip txy) (Take tyz) (Skip txz)
  SkipL : CompGraph txy tyz txz -> CompGraph       txy  (Skip tyz) (Skip txz)
  Take2 : CompGraph txy tyz txz -> CompGraph (Take txy) (Take tyz) (Take txz)

Uninhabited (CompGraph txy (Skip tyz) (Take txz)) where
  uninhabited NilG impossible

Uninhabited (CompGraph (Take txy) (Take tyz) (Skip txz)) where
  uninhabited NilG impossible

lemma1 : (txy : Thin xs ys) -> (tyz : Thin ys zs) -> (txz : Thin xs zs)
       -> compThin txy tyz = txz -> CompGraph txy tyz txz
lemma1  Nil        Nil        Nil                     Refl = NilG
lemma1 (Skip txy) (Take tyz) (Skip (compThin txy tyz)) Refl = SkipR $ lemma1 txy tyz (compThin txy tyz) Refl
lemma1  txy       (Skip tyz) (Skip (compThin txy tyz)) Refl = SkipL $ lemma1 txy tyz (compThin txy tyz) Refl
lemma1 (Take txy) (Take tyz) (Take (compThin txy tyz)) Refl = Take2 $ lemma1 txy tyz (compThin txy tyz) Refl

lemma2 : CompGraph txy tyz txz -> compThin txy tyz = txz
lemma2  NilG      = Refl
lemma2 (SkipR cg) = cong Skip $ lemma2 cg
lemma2 (SkipL cg) = cong Skip $ lemma2 cg
lemma2 (Take2 cg) = cong Take $ lemma2 cg

lemma3 : (cg1, cg2 : CompGraph txy tyz txz) -> cg1 = cg2
lemma3  NilG       NilG       = Refl
lemma3 (SkipR cg) (SkipR cg2) = cong SkipR $ lemma3 cg cg2
lemma3 (SkipL cg) (SkipL cg2) = cong SkipL $ lemma3 cg cg2
lemma3 (Take2 cg) (Take2 cg2) = cong Take2 $ lemma3 cg cg2

squareSym : {twx : Thin ws xs}
         -> {txz : Thin xs zs}
         -> {twy : Thin ws ys}
         -> {tyz : Thin ys zs}
         -> CompGraph twx txz (compThin twy tyz) -> CompGraph twy tyz (compThin twx txz)
squareSym cg = lemma1 twy tyz (compThin twx txz) $ sym $ lemma2 cg

triId : {txy : Thin xs ys} -> {tyz : Thin ys zs} -> CompGraph txy tyz (compThin txy tyz)
triId = lemma1 txy tyz (compThin txy tyz) Refl

injective : (txy1, txy2 : Thin xs ys) -> (tyz : Thin ys zs)
         -> CompGraph txy1 tyz (compThin txy2 tyz) -> txy1 = txy2
injective  Nil         Nil         Nil        NilG      = Refl
injective (Skip txy1) (Skip txy2) (Take tyz) (SkipR cg) = cong Skip $ injective txy1 txy2 tyz cg
injective  txy1        txy2       (Skip tyz) (SkipL cg) = injective txy1 txy2 tyz cg
injective (Take txy1) (Take txy2) (Take tyz) (Take2 cg) = cong Take $ injective txy1 txy2 tyz cg

noCoproducts : (y : a) -> (xs : List a)
             -> (i1, i2 : Thin [y] xs)
             -> (t1 : Thin xs [y])
             -> (t2 : Thin xs [y,y])
             -> CompGraph i1 t1 (Take Nil)
             -> CompGraph i2 t1 (Take Nil)
             -> CompGraph i1 t2 (Take $ Skip Nil)
             -> CompGraph i2 t2 (Skip $ Take Nil)
             -> Void
noCoproducts y []      i1  i2        t1         t2               cg11 cg21 cg12 cg22 = absurd i2
noCoproducts x (x::xs) i1  i2       (Take t1)  (Skip t2)         cg11 cg21 cg12 cg22 = absurd cg12
noCoproducts x [x]     i1 (Skip i2) (Take Nil) (Take (Skip Nil)) cg11 cg21 cg12 cg22 = absurd i2
noCoproducts x [x]     i1 (Take i2) (Take Nil) (Take (Skip Nil)) cg11 cg21 cg12 cg22 = absurd cg22

thinAppend : Thin ws ys -> Thin xs zs -> Thin (ws ++ xs) (ys ++ zs)
thinAppend  Nil       txz = txz
thinAppend (Skip twy) txz = Skip $ thinAppend twy txz
thinAppend (Take twy) txz = Take $ thinAppend twy txz

splitCoherence : (wxs : List a) -> Thin wxs (ys ++ zs)
               -> (ws : List a) -> Thin ws   ys
               -> (xs : List a) -> Thin xs   zs
               -> Type
splitCoherence wxs twxyz ws twy xs txz = DPair (wxs = ws ++ xs) (\prf => replace {p = \z=>Thin z (ys ++ zs)} prf twxyz = thinAppend twy txz)

uniqueCoherence : {twxyz : Thin wxs (ys ++ zs)}
               -> {twy : Thin ws   ys}
               -> {txz : Thin xs   zs}
               -> (c1, c2 : splitCoherence wxs twxyz ws twy xs txz)
               -> c1 = c2
uniqueCoherence (Refl ** Refl) (Refl ** Refl) = Refl

--     TODO report
--
-- Can't solve constraint between:
--         ?a [no locals in scope]
-- and
--         .a rec
--
--record Splitting (wxs : List a) (ys : List a) (zs : List a) (twxyz : Thin wxs (ys ++ zs)) where
--  constructor MkSplitting
--  {as, bs : List a}
--  thin1 : Thin as ys
--  thin2 : Thin bs zs
--  equiv : splitCoherence wxs twxyz as thin1 bs thin2

data Splitting : (wxs : List a) -> (ys : List a) -> (zs : List a) -> (twxyz : Thin wxs (ys ++ zs)) -> Type where
    MkSplitting : {as, bs : List a}
               -> (thin1 : Thin as ys)
               -> (thin2 : Thin bs zs)
               -> (equiv : splitCoherence wxs twxyz as thin1 bs thin2)
               -> Splitting wxs ys zs twxyz

alreadySplit : {ws, xs : List a} -> (twy : Thin ws ys) -> (txz : Thin xs zs) -> Splitting (ws ++ xs) ys zs (thinAppend twy txz)
alreadySplit twy txz =  MkSplitting twy txz (Refl ** Refl)

splitThin : {wxs : List a} -> (ys : List a) -> (twxyz : Thin wxs (ys ++ zs)) -> Splitting wxs ys zs twxyz
splitThin []       twxyz       = MkSplitting Nil twxyz (Refl ** Refl)
splitThin (y::ys) (Skip twxyz) =
  let MkSplitting th1 th2 (Refl ** eqv) = splitThin ys twxyz in
  MkSplitting (Skip th1) th2 (Refl ** cong Skip eqv)
splitThin (y::ys) (Take twxyz) =
  let MkSplitting th1 th2 (Refl ** eqv) = splitThin ys twxyz in
  MkSplitting (Take th1) th2 (Refl ** cong Take eqv)