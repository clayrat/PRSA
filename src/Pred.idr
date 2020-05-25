module Pred

%default total
--%access public export

public export
Pred : Type -> Type
Pred a = a -> Type

infixr 1 :->
public export
(:->) : Pred a -> Pred a -> Pred a
(:->) p q x = p x -> q x

public export
All : Pred a -> Type
All {a} p = {x : a} -> p x

public export
data Union : Pred a -> Pred a -> Pred a where
  Inj1 : All (p :-> Union p q)
  Inj2 : All (q :-> Union p q)

public export
turn : (a -> b) -> Pred b -> Pred a
turn f pb = pb . f

public export
data One : a -> Pred (List a) where
  MkOne : One x [x]
