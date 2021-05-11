module LTLCses.Command

import Split
import Pred
import SepLogic
import LTLCses.Ty

--data Free : Pred a -> (cmd : Pred a) -> (cmd f -> Pred a) -> Pred a where
--  Pure   : p a -> Free p cmd d a
--  Impure : (DStar cmd (\c => d c ~* Free p cmd d)) a -> Free p cmd d a