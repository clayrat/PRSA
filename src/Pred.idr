module Pred

%default total
%access public export

Pred : Type -> Type
Pred a = a -> Type

infixr 1 :->
(:->) : Pred a -> Pred a -> Pred a
(:->) p q x = p x -> q x

All : Pred a -> Type
All {a} p = {x : a} -> p x

data Union : Pred a -> Pred a -> Pred a where
  Inj1 : All (p :-> Union p q)
  Inj2 : All (q :-> Union p q)

turn : (a -> b) -> Pred b -> Pred a
turn f pb = pb . f

data One : a -> Pred (List a) where
  MkOne : One x [x]
