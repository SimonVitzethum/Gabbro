import Grammatik.Bausteine.Arena.Ownership.Source.ArgumentFlow
import Grammatik.Bausteine.Arena.Ownership.Source.Accounting
import Grammatik.Bausteine.Arena.Ownership.FreshFrame

/-! General ownership interfaces. They describe parameter modes and the
result's ownership, independently of any particular implementation shape.
The implementation's ordinary value/payload contracts remain user logic.
-/

namespace Gabbro.Grammatik.ArenaOwnership.Source.Flow

variable {D : Deklaration}

def parameterContext {params : Ctx} : Modes params → Context
  | .nil => Context.empty []
  | .cons mode rest =>
    let c := parameterContext rest
    ⟨c.references ++ [mode.map (fun _ => c.next)], fun i => if i = c.next then mode else c.rights i, c.next + 1⟩

def validParameters (A : FreiForm D) {params : Ctx} : Modes params → Bool
  | .nil => true
  | .cons (τ := τ) mode rest => (!mode.isSome || decide (τ = Ty.index (D.count A.tab))) && validParameters A rest

theorem parameterContext_length {params : Ctx} (modes : Modes params) :
    (parameterContext modes).references.length = params.length ∧ (parameterContext modes).next = params.length := by
  induction modes with
  | nil => exact ⟨rfl, rfl⟩
  | cons mode rest ih => simpa [parameterContext, ih.1, ih.2] using ih

theorem parameterContext_bounded {params : Ctx} (modes : Modes params) : (parameterContext modes).bounded := by
  induction modes with
  | nil =>
    refine ⟨fun _ _ => rfl, ?_⟩
    intro _ hm
    cases hm
  | cons mode rest ih =>
    constructor
    · intro i hi
      change (parameterContext rest).next + 1 ≤ i at hi
      have hn : i ≠ (parameterContext rest).next := by omega
      change (if i = (parameterContext rest).next then mode else (parameterContext rest).rights i) = none
      rw [ite_eq_right hn]
      exact ih.1 i (by omega)
    · intro ref hm i he
      rcases List.mem_append.mp hm with hm | hm
      · exact Nat.lt_succ_of_lt (ih.2 ref hm i he)
      · have href : ref = mode.map (fun _ => (parameterContext rest).next) := by simpa using hm
        rw [href] at he
        cases mode with
        | none => cases he
        | some m =>
          have hi : (parameterContext rest).next = i := Option.some.inj he
          subst i
          exact Nat.lt_succ_self _

inductive Output (A : FreiForm D) : Option Ty → Type where
  | plain {erg : Option Ty} : Output A erg
  | owner : Output A (some (Ty.index (D.count A.tab)))

def Output.result (A : FreiForm D) {erg : Option Ty} : Output A erg → Frame → State → ErgVal D erg → Prop
  | .plain, frame, s, _ => s.closed frame
  | .owner, frame, s, v => ∃ h, s.owns frame h ∧ h.slot = v.n ∧ s.single frame h

structure Interface (A : FreiForm D) (f : D.Fn) where
  parameters : Modes (D.params f)
  valid : validParameters A parameters = true
  output : Output A (D.erg f)

def Interface.contract (A : FreiForm D) {f : D.Fn} (spec : Interface A f) : Contract D f where
  requires := fun frame s ρ => ∃ g,
    References (parameterContext spec.parameters) g ρ ∧ Rights (parameterContext spec.parameters) g s frame ∧
      Complete (parameterContext spec.parameters) g s frame
  ensures := fun frame before _ after answer =>
    before.local after frame ∧ before.progress after ∧
      match answer with
      | .value v => spec.output.result A frame after v
      | .reason _ => after.closed frame

def checkErg (A : FreiForm D) (c : Context) {Γ : Ctx} {Λ : List (Res D)} {erg : Option Ty} :
    ErgExpr D Γ Λ erg → Bool
  | .empty => true
  | .val e => checkExpression A c e

def Output.check (A : FreiForm D) (c : Context) {Γ : Ctx} {Λ : List (Res D)} {erg : Option Ty} :
    Output A erg → ErgExpr D Γ Λ erg → Bool
  | .plain, e => checkErg A c e && finish c none
  | .owner, .val e => checkExpression A c e &&
      match origin c e with
      | none => false
      | some i => decide (c.rights i = some .owned) && finish c (some i)

theorem Output.check_sound (A : FreiForm D) (c : Context) (g : Ghost) (frame : Frame) (s : State)
    {Γ : Ctx} {Λ : List (Res D)} {erg : Option Ty}
    (output : Output A erg) (e : ErgExpr D Γ Λ erg) (σ0 σ : World D) (ρ : Env D Γ)
    (hb : c.bounded) (href : References c g ρ) (hr : Rights c g s frame)
    (hc : Complete c g s frame) (checked : output.check A c e = true) :
    output.result A frame s (evalErg σ0 e σ ρ) := by
  cases output with
  | plain =>
    exact finish_void hb hc (Bool.and_eq_true_iff.mp checked).2
  | owner =>
    cases e with
    | val e =>
      have ht := (Bool.and_eq_true_iff.mp checked).2
      cases ho : origin c e with
      | none => simp only [ho, Bool.false_eq_true] at ht
      | some i =>
        rw [ho] at ht
        obtain ⟨hmode, hfinish⟩ := Bool.and_eq_true_iff.mp ht
        have hi : c.rights i = some .owned := of_decide_eq_true hmode
        obtain ⟨h, hg, hown⟩ := hr.1 i .owned hi
        obtain ⟨k, hgk, hv⟩ := origin_sound c g ρ href e i ho σ0 σ
        rw [hg] at hgk
        cases hgk
        exact ⟨h, hown, (Option.some.inj hv).symm, finish_owned hb hc hg hfinish⟩

#print axioms parameterContext_bounded
#print axioms Output.check_sound

end Gabbro.Grammatik.ArenaOwnership.Source.Flow
