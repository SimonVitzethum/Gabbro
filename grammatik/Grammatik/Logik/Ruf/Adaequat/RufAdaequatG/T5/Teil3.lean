module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T4
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T5.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SimRet
variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (rho : Env D (D.params fn))
  (s0 : World D) (log : List (RufEreignisF D)) (A : D.Lock → Prop)
variable (hnw : caller.wartend = false)
include hnw

end SimRet

end Gabbro.Grammatik
