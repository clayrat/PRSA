module Market

import Split
import Pred

%access public export
%default total

data Market a = Of (List a) | De (List a)

data MSplit : Market a -> Market a -> Market a -> Type where
  Demand : Split d dl dr -> MSplit (De d)  (De dl) (De dr)
  OfferL : Split o ol dr -> MSplit (Of ol) (Of o)  (De dr)
  OfferR : Split o dl or -> MSplit (Of or) (De dl) (Of o)

msplitComm : MSplit x l r -> MSplit x r l
msplitComm (Demand sp) = Demand $ splitComm sp
msplitComm (OfferL sp) = OfferR $ splitComm sp
msplitComm (OfferR sp) = OfferL $ splitComm sp

msplitAssoc : MSplit lm l m -> MSplit g lm r -> (mr ** (MSplit g l mr, MSplit mr m r))
msplitAssoc (Demand sp1) (Demand sp2) =
  let (mr ** (sp3, sp4)) = splitAssoc sp1 sp2 in
  (De mr ** (Demand sp3, Demand sp4))
msplitAssoc (Demand sp1) (OfferR sp2) =
  let (mr ** (sp3, sp4)) = splitAssoc (splitComm sp1) sp2 in
  (Of mr ** (OfferR sp4, OfferR sp3))
msplitAssoc (OfferL sp1) (OfferL sp2) =
  let (mr ** (sp3, sp4)) = splitAssoc sp2 sp1 in
  (De mr ** (OfferL sp3, Demand $ splitComm sp4))
msplitAssoc (OfferR sp1) (OfferL sp2) =
  let (mr ** (sp3, sp4)) = splitUnassoc sp1 sp2 in
  (Of mr ** (OfferR sp3, OfferL sp4))

msplitUnassoc : MSplit g l mr -> MSplit mr m r -> (lm ** (MSplit lm l m, MSplit g lm r))
msplitUnassoc sp1 sp2 =
  let (lm ** (sp3, sp4)) = msplitAssoc (msplitComm sp2) (msplitComm sp1) in
  (lm ** (msplitComm sp4, msplitComm sp3))

msplitLInv : MSplit g d (De []) -> g = d
msplitLInv (Demand sp) = cong $ splitLInv sp
msplitLInv (OfferL sp) = cong $ sym $ splitLInv sp

msplitLeft : MSplit l l (De [])
msplitLeft {l=De l} = Demand splitLeft
msplitLeft {l=Of l} = OfferL splitLeft

msplitRInv : MSplit g (De []) d -> g = d
msplitRInv (Demand sp) = cong $ splitRInv sp
msplitRInv (OfferR sp) = cong $ sym $ splitRInv sp

data Supplier : (List a -> Pred (List a)) -> Pred (Market a) where
  MkSupplier : p o d -> Split o o1 d -> Supplier p (Of o1)

data Consumer : Pred (List a) -> Pred (Market a) where
  MkConsumer : p d -> Consumer p (De d)