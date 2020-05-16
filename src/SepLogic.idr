module SepLogic

import Pred
import Split

%default total
%access public export

-- separating connectives

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

-- Inductive separating forall over a list
data AllStar : {a, b : Type} -> (a -> Pred b) -> List a -> Pred b where
  Nil  : eps $ AllStar p []
  Cons : All $ p x ^*^ AllStar p xs :-> AllStar p (x::xs)
