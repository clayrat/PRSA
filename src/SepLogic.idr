module SepLogic

import Pred
import Split

%default total
%access public export

-- separating connectives

data Star : {a : Type} -> Pred (List a) -> Pred (List a) -> Pred (List a) where
  MkStar : {L, R : List a} -> (px : p L) -> (split : Split g L R) -> (qx : q R) -> Star p q g

infixr 5 ^*^

(^*^) : Pred (List a) -> Pred (List a) -> Pred (List a)
(^*^) = Star

infixr 5 ~*

(~*) : Pred (List a) -> Pred (List a) -> Pred (List a)
(~*) {a} p q l = {g, r : List a} -> Split g l r -> p r -> q g

-- * is adjoint to -*

uncurryS : All (p ^*^ q :-> r) -> All (p :-> q ~* r)
uncurryS f pl = \sp, qr => f $ MkStar pl sp qr

curryS : All (p :-> q ~* r) -> All (p ^*^ q :-> r)
curryS f (MkStar pl sp qr) = f pl sp qr
