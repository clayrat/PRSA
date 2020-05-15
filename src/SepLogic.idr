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

Wand : (p, q : Pred (List a)) -> Pred (List a)
Wand {a} p q l = {g, r : List a} -> Split g l r -> p r -> q g

-- * is adjoint to -*

uncu : All (Star x y :-> z) -> All (x :-> Wand y z)
uncu f pl _ _ sp qr = f $ MkStar pl sp qr

cu : All (x :-> Wand y z) -> All (Star x y :-> z)
cu f (MkStar px sp qx) = f px sp qx
