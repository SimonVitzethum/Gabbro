import Grammatik.Bausteine.Arena.Ownership.Body.CallStep

/-! Calls through a function pointer. The target is chosen at run time among
the functions whose signature fits the pointer's signature number. Such a
call is admitted against ONE signature interface, and only when every
fitting function's interface has the same parameter modes and the same
result kind; the runtime target then meets the same handoff as a direct
call. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration} {A : FreiForm D}

def Flow.Output.isOwner {erg : Option Ty} : Flow.Output A erg → Bool
  | .plain => false
  | .owner => true

/-- The caller context with the result bound, by result kind. -/
def resultContextB (c : Context) (owner : Bool) : Context := if owner then c.bindFresh else c.bind none

theorem resultContext_isOwner (c : Context) {erg : Option Ty} (out : Flow.Output A erg) :
    resultContext c out = resultContextB c (Flow.Output.isOwner out) := by
  cases out <;> rfl

/-- The parameter context depends only on the modes by position. -/
theorem parameterContext_eq {P1 P2 : Ctx} (m1 : Modes P1) (m2 : Modes P2) (h : modeList m1 = modeList m2) :
    Flow.parameterContext m1 = Flow.parameterContext m2 := by
  have href : (Flow.parameterContext m1).references = (Flow.parameterContext m2).references :=
    List.ext_getElem? fun u => by rw [parameterContext_references, parameterContext_references, h]
  have hrights : (Flow.parameterContext m1).rights = (Flow.parameterContext m2).rights :=
    funext fun u => by rw [parameterContext_rights, parameterContext_rights, h]
  have hnext : (Flow.parameterContext m1).next = (Flow.parameterContext m2).next := by
    rw [(Flow.parameterContext_length m1).2, (Flow.parameterContext_length m2).2, ← modeList_length m1,
      ← modeList_length m2, h]
  generalize Flow.parameterContext m1 = a at *
  generalize Flow.parameterContext m2 = b at *
  cases a; cases b
  simp_all

theorem References.transport {c : Context} {g : Ghost} {P1 P2 : Ctx} (hP : P1 = P2)
    {ρ1 : Env D P1} {ρ2 : Env D P2} (he : HEq ρ1 ρ2) (h : References c g ρ1) : References c g ρ2 := by
  subst hP
  cases eq_of_heq he
  exact h

theorem umsig_heq {f : D.Fn} {n : Nat} (hf : D.passt f n = true) (ρ : Env D (D.sigNr n).params) :
    HEq (umsig hf ρ) ρ := by
  unfold umsig
  simp only [eq_mpr_eq_cast]
  exact cast_heq _ _

/-- Every function fitting the signature number has the signature interface. -/
def SigCompatible (I : Interfaces A) (n : Nat) (J : Modes (D.sigNr n).params) (owner : Bool) : Prop :=
  ∀ f, D.passt f n = true → modeList (I f).parameters = modeList J ∧ Flow.Output.isOwner (I f).output = owner

section Step

variable {fr : Frame} {s0 : State} {c : Context} {σ : World D} {Γ : Ctx} {ρ : Env D Γ}
variable (I : Interfaces A) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **An indirect call that returns a value**, whichever fitting function
the pointer names. -/
theorem callInd_value (hR : Respects A I.contracts R) {Λ : List (Res D)} {n : Nat}
    (J : Modes (D.sigNr n).params) (owner : Bool) (hJ : SigCompatible I n J owner)
    (args : Args D Γ Λ (D.sigNr n).params) (h : Holds A fr s0 c σ ρ)
    (hp : planFits c (modeList J) (originList c args) = true)
    (f : D.Fn) (hf : D.passt f n = true)
    {σ' : World D} {v : ErgVal D (D.erg f)}
    (hrun : R f σ (umsig hf (evalArgs σ args σ ρ)) = .ok σ' v) :
    ValueBound A fr s0 (c.afterCall (modeList J) (originList c args)) σ' ρ (I f).output v := by
  obtain ⟨g, s, hRz, hc, hl, hpr⟩ := h
  have hok := handoff_ok (ms := modeList J) (os := originList c args) hRz hp
  obtain ⟨href, hr, hcomp⟩ := handoff_requires J args rfl rfl hRz hp σ σ
  have hpc := parameterContext_eq (I f).parameters J (hJ f hf).1
  have hpre : (I.contracts f).requires (calleeFrame A s fr)
      (s.handoff (calleeFrame A s fr) (movedHandles g (modeList J) (originList c args))
        (lentHandles g (modeList J) (originList c args)))
      (umsig hf (evalArgs σ args σ ρ)) := by
    refine ⟨calleeGhost g (modeList J) (originList c args) s.next, ?_, ?_, ?_⟩
    · rw [hpc]
      exact References.transport (D.passt_sig hf).params.symm (umsig_heq hf _).symm href
    · rw [hpc]; exact hr
    · rw [hpc]; exact hcomp
  have hpost := (hR f _ _ σ _ (handoff_agrees hok hRz.1) hRz.2.1 hpre).1 σ' v hrun
  obtain ⟨s2, ha2, hf2, hloc, hprog, hres⟩ := hpost
  exact bound_of_result (I f).output v hRz hc hl hpr hp hloc hprog ha2 hf2 hres

end Step

#print axioms callInd_value

end Gabbro.Grammatik.ArenaOwnership.Body
