module LTLCref.Eval

import Split
import Pred
import SepLogic
import SepLogicM
import LTy
import Market
import LTLCref.Term
import LTLCref.State
import LTLCref.Reader

%default total
%access public export

{-
partial
eval : Term a g -> eps $ Reader g [] (Val a)
eval {a} (Var MkOne)                = do Cons (MkStar v sp Nil) <- ask
                                         case splitLInv sp of
                                           Refl => pure {p=Val a} v
eval (Lam {a} {b} t)                = do env <- ask
                                         pure {p=Val (a ~@ b)} $ VClos t env
eval (App (MkStar f sp t))          = do VClos {g} b env <- frame sp (eval f)
                                         ve <- str {q=Env g} $ MkStar (eval t) splitRight env
                                         MkEmp <- append $ Cons ve
                                         eval b
eval  TT                            = pure {p=Val U} VT
eval (LetT (MkStar u sp t))         = do VT <- frame sp (eval u)
                                         eval t
eval (Pair {a} {b} (MkStar x sp y)) = do v1 <- frame sp (eval x)
                                         ba <- str {q=Val a} $ MkStar (eval y) splitRight v1
                                         pure {p=Val $ Prod a b} $ VPair $ starComm ba
eval (LetP (MkStar pr sp t))        = do VPair (MkStar v1 sp0 v2) <- frame sp (eval pr)
                                         MkEmp <- prepend $ Cons $ MkStar v2 (splitComm sp0) (singleton v1)
                                         eval t
eval (Ref)
eval (Swap)
eval (Del)
-}