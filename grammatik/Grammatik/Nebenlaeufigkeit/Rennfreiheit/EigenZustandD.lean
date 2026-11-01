/-
  File:      Grammatik/EigenZustandD.lean
  Subject:   **OWN-STATE PROJECTION** (lane 56, attempt D).

  A step fired by a thread `h` whose program text never names table `t`
  leaves every slot of `t` unchanged. The route is bottom-up: each writing
  leaf records a `zugriff t true ..` event (carried by `hcar` of the leaf
  rule of `PCSchritt`); a leaf whose recorded events carry no `Sum.inl t`
  keeps the slots of `t`; take/release steps keep memory by construction.
-/

module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T1
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T3
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T4
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T5
@[expose] public section

