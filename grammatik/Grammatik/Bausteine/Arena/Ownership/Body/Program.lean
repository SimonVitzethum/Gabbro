import Grammatik.Bausteine.Arena.Ownership.Body.Sound

/-! **Checked programs.** A program is checked against an interface table
when every function body derives in the body judgment from its parameter
context. Then the bodies discharge `Bodies`, and `rufAt_ownership` gives the
ownership interface of every actual call at every depth, recursion and
calls through pointers included. The only premise besides the derivations is
`GutO`, the existing frame of foreign bodies among the hardware assumptions. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-- The loop context of a body outside every loop (never consulted). -/
def noLoop : Context := Context.empty []

/-- **Every body derives from its parameter context.** -/
def Checked (P : Programm D) (A : FreiForm D) (I : Interfaces A) : Prop :=
  ∀ f, OE A I (V := vertragVon D f) (I f).output noLoop (Flow.parameterContext (I f).parameters) (P.rumpf f)

/-- An end-block promise of a body is its interface's body postcondition. -/
theorem EPost.bodyPost {A : FreiForm D} {I : Interfaces A} {f : D.Fn} {frame : Frame} {s : State}
    {ρ : Env D (D.params f)} (o : EndAusgang (vertragVon D f) false (D.params f))
    (h : EPost A frame s (I f).output noLoop o) : (I.contracts f).bodyPost A frame s ρ o := by
  cases o with
  | zurueck σ v =>
    obtain ⟨s', ha, hf, hl, hp, hr⟩ := h
    exact ⟨s', ha, hf, hl, hp, hr⟩
  | why σ r =>
    obtain ⟨s', ha, hf, hl, hp, hr⟩ := h
    exact ⟨s', ha, hf, hl, hp, hr⟩
  | leave hl _ _ => exact Bool.noConfusion hl
  | next hl _ _ => exact Bool.noConfusion hl
  | logik _ => trivial
  | hardware _ => trivial

/-- **Checked bodies discharge the body obligation**, for every call handler
that respects the interface contracts. -/
theorem checked_bodies {P : Programm D} {A : FreiForm D} {I : Interfaces A} (hc : Checked P A I)
    {O : Orakel D} (hO : GutO O) (passes : Nat) : Bodies P A I.contracts O passes := by
  intro R hR f frame s σ ρ ha hf hpre
  have h := Holds.entry (I f) frame s σ ρ ha hf hpre
  exact EPost.bodyPost _ (oe_sound (fr := frame) (s0 := s) (passes := passes) hR hO (hc f) σ ρ
    (Nat.zero_le _) h)

/-- **Every actual call of a checked program keeps its ownership interface**:
fresh activations, owning and borrowed arguments handed over and given
back, an owning result returned under a new grant, nothing of another
activation touched, no older grant revived, at every depth. -/
theorem checked_calls {P : Programm D} {A : FreiForm D} {I : Interfaces A} (hc : Checked P A I)
    {O : Orakel D} (hO : GutO O) (passes : Nat) : ∀ n, Respects A I.contracts (rufAt P O passes n) :=
  rufAt_ownership P A I.contracts O passes (checked_bodies hc hO passes)

#print axioms checked_bodies
#print axioms checked_calls

end Gabbro.Grammatik.ArenaOwnership.Body
