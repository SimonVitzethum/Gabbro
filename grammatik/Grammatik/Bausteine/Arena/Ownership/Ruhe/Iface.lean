import Grammatik.Bausteine.Arena.Ownership.Ruhe.Checks

/-! **Interfaces across the idle root.** A function `f` of `D` is `some f` of
`D.mitRuhe` with its parameter types shifted; its interface keeps its modes
by position and its result kind. The idle root has no parameter and a plain
result. -/

namespace Gabbro.Grammatik.ArenaOwnership.Ruhe

open Source Body

variable {D : Deklaration}

/-- Modes, by position, over the shifted parameter types. -/
def modesR : {Γ : Ctx} → Modes Γ → Modes (Γ.map tyR)
  | _, .nil => .nil
  | _, .cons m rest => .cons m (modesR rest)

theorem modeList_modesR : ∀ {Γ : Ctx} (m : Modes Γ), modeList (modesR m) = modeList m
  | _, .nil => rfl
  | _, .cons m rest => by simp only [modesR, modeList, modeList_modesR rest]

theorem tyR_eq_int {τ : Ty} {a b : Int} : tyR τ = .int a b ↔ τ = .int a b := by
  cases τ <;> simp only [tyR, Ty.int.injEq, reduceCtorEq]

theorem validParameters_modesR (A : FreiForm D) :
    ∀ {Γ : Ctx} (m : Modes Γ), Flow.validParameters (liftA A) (modesR m) = Flow.validParameters A m
  | _, .nil => rfl
  | _, .cons (τ := τ) mo rest => by
    simp only [modesR, Flow.validParameters, validParameters_modesR A rest]
    congr 2
    exact decide_eq_decide.mpr tyR_eq_int

theorem parameterContext_modesR {Γ : Ctx} (m : Modes Γ) :
    Flow.parameterContext (modesR m) = Flow.parameterContext m :=
  parameterContext_eq _ _ (modeList_modesR m)

/-- **The interfaces of `D.mitRuhe`.** -/
def liftI {A : FreiForm D} (I : Interfaces A) : Interfaces (liftA A)
  | none => ⟨.nil, rfl, .plain⟩
  | some f => ⟨modesR (I f).parameters, (validParameters_modesR A (I f).parameters).trans (I f).valid,
      outR A (I f).output⟩

end Gabbro.Grammatik.ArenaOwnership.Ruhe
