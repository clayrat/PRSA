module Split

import Data.Nat
import Data.List

--%access public export
%default total

public export
data Split : List a -> List a -> List a -> Type where
  Nil   : Split [] [] []
  ConsR : Split xs ls rs -> Split (x::xs)     ls (x::rs)
  ConsL : Split xs ls rs -> Split (x::xs) (x::ls)    rs

export
splitComm : Split x l r -> Split x r l
splitComm  Nil      = Nil
splitComm (ConsR s) = ConsL $ splitComm s
splitComm (ConsL s) = ConsR $ splitComm s

export
splitLeft : {l : List a} -> Split l l []
splitLeft {l=[]}   = Nil
splitLeft {l=_::_} = ConsL splitLeft

export
splitRight : {l : List a} -> Split l [] l
splitRight = splitComm splitLeft

export
splitRInv : Split g [] d -> g = d
splitRInv  Nil          = Refl
splitRInv (ConsR {x} s) = cong (x ::) $ splitRInv s

export
splitLInv : Split g d [] -> g = d
splitLInv = splitRInv . splitComm

export
splitAssoc : {g : List a} -> Split lm l m -> Split g lm r -> (mr ** (Split g l mr, Split mr m r))
splitAssoc {g}  Nil             sp2            = (g ** (splitRight, sp2))
splitAssoc      sp1            (ConsR {x} sp2) =
  let (mr ** (sp3, sp4)) = splitAssoc sp1 sp2 in
  (x::mr ** (ConsR sp3, ConsR sp4))
splitAssoc     (ConsR {x} sp1) (ConsL     sp2) =
  let (mr ** (sp3, sp4)) = splitAssoc sp1 sp2 in
  (x::mr ** (ConsR sp3, ConsL sp4))
splitAssoc     (ConsL     sp1) (ConsL     sp2) =
  let (mr ** (sp3, sp4)) = splitAssoc sp1 sp2 in
  (mr ** (ConsL sp3, sp4))

export
splitUnassoc : {g : List a} -> Split g l mr -> Split mr m r -> (lm ** (Split lm l m, Split g lm r))
splitUnassoc sp1 sp2 =
  let (lm ** (sp3, sp4)) = splitAssoc (splitComm sp2) (splitComm sp1) in
  (lm ** (splitComm sp4, splitComm sp3))

export
splitLen : Split g l r -> length g = length l + length r
splitLen                Nil      = Refl
splitLen {l} {r=_::rs} (ConsR s) =
  rewrite plusAssociative (length l) 1 (length rs) in
  rewrite plusCommutative (length l) 1 in
  cong S $ splitLen s
splitLen               (ConsL s) = cong S $ splitLen s

export
splitMap : (f : a -> b) -> Split g l r -> Split (map f g) (map f l) (map f r)
splitMap f  Nil      = Nil
splitMap f (ConsR s) = ConsR $ splitMap f s
splitMap f (ConsL s) = ConsL $ splitMap f s