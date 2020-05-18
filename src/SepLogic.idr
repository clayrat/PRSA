module SepLogic

import Pred
import Split

%default total
%access public export

data Emp : Pred (List a) where
  MkEmp : Emp []

data Star : {a : Type} -> Pred (List a) -> Pred (List a) -> Pred (List a) where
  MkStar : {l, r : List a} -> p l -> Split g l r -> q r -> Star p q g

infixr 9 ^*^

(^*^) : Pred (List a) -> Pred (List a) -> Pred (List a)
(^*^) = Star

infixr 8 ~*

(~*) : Pred (List a) -> Pred (List a) -> Pred (List a)
(~*) {a} p q l = {g, r : List a} -> Split g l r -> p r -> q g

-- * is adjoint to -*

uncurryS : All (p ^*^ q :-> r) -> All (p :-> q ~* r)
uncurryS f pl = \sp, qr => f $ MkStar pl sp qr

curryS : All (p :-> q ~* r) -> All (p ^*^ q :-> r)
curryS f (MkStar pl sp qr) = f pl sp qr

starComm : All $ p ^*^ q :-> q ^*^ p
starComm (MkStar pl sp qr) = MkStar qr (splitComm sp) pl

-- Inductive separating forall over a list
data AllStar : {a, b : Type} -> (a -> Pred b) -> List a -> Pred b where
  Nil  : eps $ AllStar p []
  Cons : (p t ^*^ AllStar p ts) xs -> AllStar p (t::ts) xs

repartition : Split g l r -> All (AllStar p g :-> AllStar p l ^*^ AllStar p r)
repartition  Nil        Nil      = MkStar Nil Nil Nil
repartition (ConsL sp) (Cons (MkStar pt sp1 pts)) =
  let
    MkStar xs sp2 ys = repartition sp pts
    (_ ** (sp3, sp4)) = splitUnassoc sp1 sp2
   in
  MkStar (Cons $ MkStar pt sp3 xs) sp4 ys
repartition (ConsR sp) (Cons (MkStar pt sp1 pts)) =
  let
    MkStar xs sp2 ys = repartition sp pts
    (_ ** (sp3, sp4)) = splitUnassoc sp1 (splitComm sp2)
   in
  MkStar xs (splitComm sp4) (Cons $ MkStar pt sp3 ys)

concat : All $ AllStar p g1 ^*^ AllStar p g2 :-> AllStar p (g1 ++ g2)
concat (MkStar  Nil                       sp ras) = rewrite splitRInv sp in ras
concat (MkStar (Cons $ MkStar pt sp0 las) sp ras) =
  let (r ** (sp1, sp2)) = splitAssoc sp0 sp in
  Cons $ MkStar pt sp1 (concat $ MkStar las sp2 ras)