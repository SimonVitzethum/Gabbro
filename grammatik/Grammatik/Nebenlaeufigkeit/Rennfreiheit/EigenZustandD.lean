/-
  File:      Grammatik/EigenZustandD.lean
  Subject:   **OWN-STATE PROJECTION** (lane 56, attempt D).

  A step fired by a thread `h` whose program text never names table `t`
  leaves every slot of `t` unchanged. The route is bottom-up: each writing
  leaf records a `zugriff t true ..` event (carried by `hcar` of the leaf
  rule of `PCSchritt`); a leaf whose recorded events carry no `Sum.inl t`
  keeps the slots of `t`; take/release steps keep memory by construction.
-/

import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T1
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T3
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T4
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T5
