module
public import Bruecke.Anweisung.Lokal.Ruf
@[expose] public section

/-!
# Scalar fitting facts used by positional statement simulations

The visible source-name projection is used only for the existing expression theorem.
The canonical state relation and all binder updates are positional (`Werte.lean`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The values -/

theorem lowBindWert_side {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {d : Option (Int × Int)} {v : USide} {ls : LowSide u Γ Λ}
    (h : lowBindWert u Γ Λ fn d v = .ok ls) : lowSideVal u Γ Λ fn v = .ok ls := by
  unfold lowBindWert at h
  split at h
  · cases h
  · rename_i s' hs'
    split at h
    · cases h
      exact hs'
    · split at h
      · cases h
        exact hs'
      · cases h

/-- Fitting a number into a range (`fitW`) keeps its number. -/
theorem fitW_int_val {Γ : Ctx} {Λ : List (Res (declOf u))} {a b lo hi : Int}
    (t : Expr (declOf u) Γ Λ (.int a b)) {e : Expr (declOf u) Γ Λ (.int lo hi)}
    (h : fitW (.int lo hi) (⟨.int a b, t⟩ : LowWert u Γ Λ) = .ok e)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) :
    valOf (.int lo hi) (eval σ₀ e σ ρ) = valOf (.int a b) (eval σ₀ t σ ρ) := by
  simp only [fitW] at h
  split at h
  · rename_i hty
    cases h
    have hty' : Ty.int a b = Ty.int lo hi := hty
    injection hty' with h1 h2
    subst h1
    subst h2
    rfl
  · repeat' split at h
    all_goals first
      | (cases h; rfl)
      | (cases h; done)

/-- **A side at the declared number type of a local** (`lowWertAtE` at `.int lo hi`, the checking
    mode of an assignment) keeps its number. -/
theorem lowWertAtE_int_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {lo hi : Int}
    {sd : USide} {e : Expr (declOf u) Γ Λ (.int lo hi)} {eB : Gabbro.Body.Expr}
    (h : lowWertAtE u Γ Λ fn none (.int lo hi) sd = .ok e) (hb : sideExprG u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (wW : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ wW) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨wW, β⟩ eB = some (valOf (.int lo hi) (eval σ₀ e σ ρ)) := by
  simp only [lowWertAtE, reduceCtorEq, false_implies, implies_true] at h
  split at h
  · rename_i lw hlw
    obtain ⟨ls, rfl, hev⟩ := lowWertE_sim (er := none) hlw hb hA hT σ₀ σ ρ wW β hW hL
    rw [hev, fitW_int_val ls.term h σ₀ σ ρ]
  · cases h

end Gabbro.Bruecke
