module LTy

%default total
--%access public export

data Ty = U
        | Rf Ty
        | Prod Ty Ty
        | Imp Ty Ty

infixr 5 ~@
(~@) : Ty -> Ty -> Ty
(~@) = Imp

Ctx : Type
Ctx = List Ty

ST : Type
ST = List Ty