import Grammatik.Berechenbarkeit.Storage.GStack.Multi
import Grammatik.Berechenbarkeit.Brainfuck.Machine

/-! Brainfuck on G, part 1: the head byte. The Brainfuck head lives in a G local of type `int 0 255`; `+` and `-`
are one assignment each, `(h + 1) % 256` and `(h + 255) % 256` through the model's own `add` and `rem` (the range
rules give exactly `int 0 255`, no wrap-around form is assumed). Reading a carrier records the access and changes
no stack (`MultiRep.lese`). -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG

open Brainfuck ArenaKette Storage.GStack

variable {D : Deklaration}

/-- The G type of a byte. -/
abbrev ByteTy : Ty := .int 0 255

/-- A Brainfuck byte as a G value. -/
def kodiere (b : Brainfuck.Byte) : Wert D ByteTy := ⟨b.val, by omega, by omega⟩

theorem kodiere_n (b : Brainfuck.Byte) : (kodiere (D := D) b).n = b.val := rfl

/-- Two numbers of one range are equal when their values are. -/
theorem zahl_eq {lo hi : Int} {a b : Zahl lo hi} (h : a.n = b.n) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/-- **Several stacks survive a recorded read**: reading changes no slot, no head and no liveness. -/
theorem MultiRep.lese {A : FreiForm D} {K : Type} {L : LinkFeld A} {G : K → LinkKopf A} {σ : World D} {vals}
    (h : MultiRep L G σ vals) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob)) :
    MultiRep L G (σ.lese Λ orte) vals := by
  obtain ⟨ix, hix, hdis⟩ := h
  refine ⟨ix, fun k => ?_, hdis⟩
  obtain ⟨hc, hn, hl, hv⟩ := hix k
  exact ⟨hc, hn, fun i hi => (A.lebt_gleich (σ := σ) (σ' := σ.lese Λ orte) rfl (fun _ => rfl) rfl i).mpr (hl i hi), hv⟩

section Kopf

variable {Γ : Ctx} {Λ : List (Res D)}

/-- `(h + 1) % 256`. -/
def plusEins (x : Var Γ ByteTy) : Expr D Γ Λ ByteTy :=
  .rem (by decide) (by decide) (.add (.var x) (.lit 1)) (.lit 256)

/-- `(h + 255) % 256`. -/
def minusEins (x : Var Γ ByteTy) : Expr D Γ Λ ByteTy :=
  .rem (by decide) (by decide) (.add (.var x) (.lit 255)) (.lit 256)

theorem plusEins_eval (x : Var Γ ByteTy) (σ₀ σ : World D) (ρ : Env D Γ) (b : Brainfuck.Byte) (hb : (ρ.get x).n = b.val) :
    eval σ₀ (plusEins (Λ := Λ) x) σ ρ = kodiere (increment b) := by
  apply zahl_eq
  simp only [plusEins, eval, Zahl.rem, Zahl.add, kodiere, increment, hb]
  rw [Int.tmod_eq_emod_of_nonneg (by omega)]
  omega

theorem minusEins_eval (x : Var Γ ByteTy) (σ₀ σ : World D) (ρ : Env D Γ) (b : Brainfuck.Byte) (hb : (ρ.get x).n = b.val) :
    eval σ₀ (minusEins (Λ := Λ) x) σ ρ = kodiere (decrement b) := by
  apply zahl_eq
  simp only [minusEins, eval, Zahl.rem, Zahl.add, kodiere, decrement, hb]
  rw [Int.tmod_eq_emod_of_nonneg (by omega)]
  omega

end Kopf

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG
