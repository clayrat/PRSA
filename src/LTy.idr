module LTy

%default total
%access public export

data Ty = U
        | R Ty
        | Prod Ty Ty
        | Imp Ty Ty

infixr 5 ~@
(~@) : Ty -> Ty -> Ty
(~@) = Imp

ST : Type
ST = List Ty