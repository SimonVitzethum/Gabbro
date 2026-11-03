/- Part 10 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T10.Teil1Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T10.Teil1Basis
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
/-- A step of thread `f` keeps its log or prepends one event. -/
theorem rufSchrittG_log {P : Programm D} {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O passes M f M') :
    (M'.faeden f).log = (M.faeden f).log ∨ ∃ e, (M'.faeden f).log = e :: (M.faeden f).log := by
  (rcases hs with hs | hs | hs | hs | hs | hs | hs <;> cases hs) <;> rw [faeden_upd] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl⟩
    | exact rufAntwortG_log (by assumption)

/-! ## 17. TARGET B: the converse for the value -/

/-- The run invariant of the converse: either the frame of `fn` is still on
    top with a covered residue whose frame result agrees (up to the trace)
    with the fixed result `S`, or it has popped, and the log, below any later
    events, holds a `rueck` whose world and value agree with `S`. -/
def InvB (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (f : Faden) (fn : D.Fn)
    (rho : Env D (D.params fn)) (s0 : World D) (stapel : List (RufRahmenG D))
    (log : List (RufEreignisF D)) (S : REnde (vertragVon D fn)) (M : RufMaschineG D) : Prop :=
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D fn) l Γ Λ) (sp : List (Ereignis D)),
      M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩, sp, log⟩ ∧
      RestG A r ∧ (semR O passes r (M.weltVon f) ρ).gleich S) ∨
  (∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)),
      (M.faeden f).log = ext ++ RufEreignisF.rueck fn rho v s0 s1 :: log ∧
      (REnde.zurueck (V := vertragVon D fn) s1 v).gleich S)

end Gabbro.Grammatik
