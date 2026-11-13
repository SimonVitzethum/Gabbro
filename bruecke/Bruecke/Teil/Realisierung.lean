module
public import Bruecke.Teil.Ruf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Only carried functions of rank below `k` must have realizations. -/
def RealisiertC (u : UProg) (C : Fin u.fns.length → Prop)
    (rk : String → Nat) (k : Nat) (ρ : Gabbro.Body.Env) : Prop :=
  ∀ n c, C c → fnSuch u n = some (fnAt u c) → rk n < k →
    Gabbro.Body.Contract ρ n (preProp (wfU u) (fnAt u c)) (postP u (fnAt u c)) ∧
    Gabbro.Body.Frame ρ n (fnAt u c).puts

end Gabbro.Bruecke
