module LTLCses.Ty

%default total
%access public export

mutual
  data STy = Sd Ty STy
           | Rv Ty STy
           | End

  data Ty = U
          | Rf STy
          | Prod Ty Ty
          | Imp Ty Ty

infixr 5 ~@
(~@) : Ty -> Ty -> Ty
(~@) = Imp

inv : STy -> STy
inv (Sd t s) = Rv t (inv s)
inv (Rv t s) = Sd t (inv s)
inv End = End

Ctx : Type
Ctx = List Ty

data RTy = Endp STy
         | Chan STy STy

RCtx : Type
RCtx = List RTy