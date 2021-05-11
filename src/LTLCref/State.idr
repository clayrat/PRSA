module LTLCref.State

import Split
import Pred
import SepLogic
import SepLogicM
import LTy
import Market
import LTLCref.Term

%default total
%access public export

%hide Prelude.Monad.(>>=)

State : Pred (List Ty) -> Pred (List Ty)
State p a = (Supplier Store ~~* Consumer p ^**^ Supplier Store) (De a)

pure : All $ p :-> State p
pure px = MkWandM $ \sp, st => MkStarM (MkConsumer px) sp st

bind : All $ (p ~* State q) :-> (State p ~* State q)
bind w =
  MkWand $ \sp, s =>
  MkWandM $ \msp, (MkSupplier st sp0) =>
  let
    (_ ** (sp1, sp2)) = msplitAssoc (Demand sp) msp
    MkStarM (MkConsumer px) sp3 (MkSupplier st1 sp4) = appM s sp2 (MkSupplier st sp0)
    OfferR sp5 = sp1
    OfferR sp6 = sp3
    (_ ** (sp7, sp8)) = splitUnassoc sp6 sp5
   in
  appM (app w (splitComm sp7) px) (OfferR sp8) (MkSupplier st1 sp4)

(>>=) : State p t -> All (p :-> State q) -> State q t
(>>=) st f = app (bind $ MkWand $ \sp => rewrite splitRInv sp in f) splitRight st

str : All $ State p ^*^ q :-> State (p ^*^ q)
str {p} {q} (MkStar rd sp qr) = app (bind $ MkWand $ \sp1, pl => pure {p=p^*^q} $ MkStar pl (splitComm sp1) qr)
                                    (splitComm sp)
                                    rd

newref : All $ Val a :-> State (One a)
newref v =
  MkWandM $ \sp, (MkSupplier st sp1) =>
  let
    OfferR sp2 = sp
    (_ ** (sp3, sp4)) = splitAssoc (splitComm sp2) sp1
   in
  MkStarM (MkConsumer MkOne)
          (OfferR $ ConsL splitRight)
          (MkSupplier (Cons $ MkStar v sp4 st) (ConsL sp3))

read : All $ One a :-> State (Val a)
read MkOne =
  MkWandM $ \sp, (MkSupplier st sp1) =>
  let
    OfferR sp2 = sp
    (_ ** (sp3, sp4)) = splitAssoc sp2 sp1
    MkStar (Cons (MkStar v sp5 Nil)) sp6 st1 = repartition sp3 st
    (_ ** (sp7, sp8)) = splitAssoc (splitComm sp6) (splitComm sp4)
   in
  MkStarM (MkConsumer v)
          (OfferR $ rewrite sym $ splitLInv sp5 in sp8)
          (MkSupplier st1 (splitComm sp7))

write : All $ One a ^*^ Val b :-> State (One b ^*^ Val a)
write (MkStar MkOne sp1 v) =
  MkWandM $ \sp, (MkSupplier st sp2) =>
  let
    OfferR sp3 = sp
    (_ ** (sp4, sp5)) = splitAssoc (splitComm sp1) sp3
    (_ ** (sp6, sp7)) = splitAssoc (splitComm sp4) sp2
    (_ ** (sp8, sp9)) = splitAssoc sp5 sp6
    MkStar (Cons (MkStar vb sp10 Nil)) sp11 st1 = repartition sp8 st
    (_ ** (sp12, sp13)) = splitUnassoc sp7 (splitComm sp11)
    (_ ** (sp14, sp15)) = splitAssoc sp13 (splitComm sp9)
   in
  MkStarM (MkConsumer $ MkStar MkOne (ConsL splitRight) vb)
          (OfferR $ ConsL $ rewrite sym $ splitLInv sp10 in sp15)
          (MkSupplier (Cons $ MkStar v sp12 st1)
                      (ConsL $ splitComm sp14))

update : All $ One a :-> (Val a ~* State (Val b)) ~* State (One b)
update ptr = MkWand $ \sp, f =>
             do MkStar va sp1 f1 <- str $ MkStar (read ptr) sp f
                vb <- app f1 (splitComm sp1) va
                newref vb
