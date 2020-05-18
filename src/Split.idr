module Split

%access public export
%default total

data Split : List a -> List a -> List a -> Type where
  Nil   : Split [] [] []
  ConsR : Split xs ls rs -> Split (x::xs)     ls (x::rs)
  ConsL : Split xs ls rs -> Split (x::xs) (x::ls)    rs

splitComm : Split x l r -> Split x r l
splitComm  Nil      = Nil
splitComm (ConsR s) = ConsL $ splitComm s
splitComm (ConsL s) = ConsR $ splitComm s

splitLeft : Split l l []
splitLeft {l=[]}   = Nil
splitLeft {l=_::_} = ConsL splitLeft

splitRight : Split l [] l
splitRight = splitComm splitLeft

splitRInv : Split g [] d -> g = d
splitRInv  Nil      = Refl
splitRInv (ConsR s) = cong $ splitRInv s

splitLInv : Split g d [] -> g = d
splitLInv = splitRInv . splitComm

splitAssoc : Split lm l m -> Split g lm r -> (mr ** (Split g l mr, Split mr m r))
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

splitUnassoc : Split g l mr -> Split mr m r -> (lm ** (Split lm l m, Split g lm r))
splitUnassoc sp1 sp2 =
  let (lm ** (sp3, sp4)) = splitAssoc (splitComm sp2) (splitComm sp1) in
  (lm ** (splitComm sp4, splitComm sp3))

splitLen : Split g l r -> length g = length l + length r
splitLen                Nil      = Refl
splitLen {l} {r=_::rs} (ConsR s) =
  rewrite plusAssociative (length l) 1 (length rs) in
  rewrite plusCommutative (length l) 1 in
  cong $ splitLen s
splitLen               (ConsL s) = cong $ splitLen s

splitMap : (f : a -> b) -> Split g l r -> Split (map f g) (map f l) (map f r)
splitMap f  Nil      = Nil
splitMap f (ConsR s) = ConsR $ splitMap f s
splitMap f (ConsL s) = ConsL $ splitMap f s