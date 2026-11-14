/-
  File:      stage0/Stage0/Senke/Bild/Gleich/RufAt.lean
  Subject:   **`rufAt` against `rufRumpf` up to read events** (package P2 of the closed calls of the image theorem,
             the short direction). `rufAt` is the call meaning of the model: it checks the callee's `requires`, runs
             the body, checks `ensures` and the owed invariants, and READS the places of all three into the trace.
             `rufRumpf` is what machine G realises: the bare body run. Under the oracle premise of the program
             (`LeseblindP`) the two
             agree up to `≈` (`WeltGleich`) EXCEPT where `rufAt` fails one of its own contract checks
             (`rufAt_rufRumpf_lg`, error set `VertragMarke`): an `ok` of `rufAt` is an `ok` of `rufRumpf` with the same
             value and a `≈` world (`rufAt_ok_rufRumpf`), likewise a reason (`rufAt_why_rufRumpf`), and every other
             outcome of `rufAt` that is not a contract mark is the same outcome of `rufRumpf`. No user duty is needed
             for this direction.

             The proof is one induction on the depth: the step unfolds `rufAt` once (`rufAt_succ_eq`, `rufSchritt`),
             relates the body runs by the handler substitution of P1 (`execEnd_lg`) with the induction hypothesis as
             the handler premise, and closes the three contract gates: a failing gate is an early failure of the
             `rufAt` side whose mark the closure premises put into the error set; a passing gate only reads, which
             `≈` absorbs (`weltGleich_lese`, `weltGleich_foldl_lese`). The generic form
             (`rufAt_rufRumpf_unter`) takes the error set and its three closure premises as parameters, so that the
             exact relation under valid contracts (`RufAtUmkehr.lean`) is the same induction.
-/
module
public import Stage0.Senke.Bild.Gleich.Ersetzung
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil2
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## 1. The contract marks and the monotonicity of the relation -/

/-- **The marks of `rufAt`'s own contract checks**: a failed `requires`, `ensures` or owed invariant. -/
inductive VertragMarke : Fehlermarke D → Prop
  | vor (f : D.Fn) : VertragMarke (.logik (.vorbedingung f))
  | nach (f : D.Fn) : VertragMarke (.logik (.nachbedingung f))
  | inv (i : D.Inv) : VertragMarke (.logik (.invariante i))

/-- The depth residue is not a contract mark. -/
theorem nicht_vertragMarke_abstieg (f : D.Fn) : ¬ VertragMarke (.logik (.abstieg f)) := by
  intro h
  cases h

/-- A larger error set keeps the relation of call outcomes. -/
theorem RufLG.mono {Er Er' : Fehlermarke D → Prop} (hE : ∀ m, Er m → Er' m) {f : D.Fn}
    {a b : RufAusgang f} (h : RufLG Er a b) : RufLG Er' a b := by
  cases h with
  | ok hw => exact .ok hw
  | why hw => exact .why hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hm => exact .frueh (hE _ hm)
  | fruehH hm => exact .fruehH (hE _ hm)

/-- A larger error set keeps the handler relation. -/
theorem HandlerLG.mono {Er Er' : Fehlermarke D → Prop} (hE : ∀ m, Er m → Er' m)
    {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} (h : HandlerLG Er R₁ R₂) :
    HandlerLG Er' R₁ R₂ :=
  fun g σ σ' ρ hσ => (h g σ σ' ρ hσ).mono hE

/-- A chain of reads is invisible up to `≈` (the owed-invariant reads of `rufAt`). -/
theorem weltGleich_foldl_lese {α : Type} (l : List α) (L : α → List (Res D))
    (os : α → List (D.Tab ⊕ D.Glob)) :
    ∀ σ : World D, WeltGleich σ (l.foldl (fun σ' i => σ'.lese (L i) (os i)) σ) := by
  induction l with
  | nil => intro σ; exact WeltGleich.refl σ
  | cons a l ih => intro σ; exact (weltGleich_lese σ (L a) (os a)).trans (ih (σ.lese (L a) (os a)))

/-! ## 2. The induction on the depth -/

section Tiefe

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **`rufAt` against `rufRumpf`, for an error set closed under the three contract checks.** Under `LeseblindP`,
    from `≈` worlds and the same arguments, `rufAt n` and `rufRumpf n` give related outcomes, or `rufAt`
    fails early with a mark in `Er`; `Er` must contain the mark of every failing `requires`, `ensures` and owed
    invariant test (`hvor`, `hnach`, `hinv`). -/
theorem rufAt_rufRumpf_unter (Er : Fehlermarke D → Prop) (hO : LeseblindP P O)
    (hvor : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)),
      wahr? (eval σ (P.requires g) σ ρ) = false → Er (.logik (.vorbedingung g)))
    (hnach : ∀ (g : D.Fn) (σ₀ σ : World D) (ρ : Env D (D.params g)) (v : ErgVal D (D.erg g)),
      wahr? (eval σ₀ (P.ensures g) σ (ergEnv (D.erg g) v ρ)) = false → Er (.logik (.nachbedingung g)))
    (hinv : ∀ (i : D.Inv) (σ : World D), wahr? (eval σ (P.invariante i) σ .nil) = false →
      Er (.logik (.invariante i))) :
    ∀ n, HandlerLG Er (rufAt P O passes n) (rufRumpf P O passes n)
  | 0 => fun g _ _ _ _ => .logik (.abstieg g)
  | n + 1 => fun g σ σ' ρ hσ => by
      rw [rufAt_succ_eq]
      simp only [rufSchritt, rufRumpf]
      by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
          (P.requires g) (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ) = false
      · rw [if_pos hq]
        exact .frueh (hvor g _ ρ hq)
      rw [if_neg hq]
      have he := execEnd_lg (passes := passes)
        (rufAt_rufRumpf_unter Er hO hvor hnach hinv n) hO.rs (P.rumpf g) (hO.rumpf g)
        ((weltGleich_lese σ (Signatur.anfang D (D.signatur g)) (P.requires g).orte).symm.trans hσ) ρ
      generalize execEnd (V := vertragVon D g) O passes (rufAt P O passes n) (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ = o₁ at he ⊢
      generalize execEnd (V := vertragVon D g) O passes (rufRumpf P O passes n) (P.rumpf g) σ' ρ = o₂
        at he ⊢
      cases he with
      | @zurueck σa σb v hw =>
          dsimp only
          split
          · rename_i hE
            exact .frueh (hnach g _ _ ρ v hE)
          · split
            · rename_i i hi
              have hp := List.find?_some hi
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
              exact .frueh (hinv i _ hp.2)
            · exact .ok ((weltGleich_foldl_lese (D.invs.filter (schuldet g)) (fun i => invSicht D i)
                (fun i => (P.invariante i).orte)
                (σa.lese (vertragVon D g).ende (P.ensures g).orte)).symm.trans
                ((weltGleich_lese σa (vertragVon D g).ende (P.ensures g).orte).symm.trans hw))
      | why hw => exact .why hw
      | @leave hl _ _ _ _ => exact absurd hl (by decide)
      | @next hl _ _ _ _ => exact absurd hl (by decide)
      | logik e => exact .logik e
      | hardware e => exact .hardware e
      | frueh hm => exact .frueh hm
      | fruehH hm => exact .fruehH hm

/-- **`rufAt ≈ rufRumpf` up to `rufAt`'s own contract failures** (P2, the short direction). Under a read-blind
    oracle, at every depth, `rufAt` and the body-running handler of machine G give related outcomes on `≈` worlds:
    the same shape, `≈` worlds, equal values and reasons -- unless `rufAt` fails a `requires`, `ensures` or owed
    invariant check. No user duty. -/
theorem rufAt_rufRumpf_lg (hO : LeseblindP P O) :
    ∀ n, HandlerLG VertragMarke (rufAt P O passes n) (rufRumpf P O passes n) :=
  rufAt_rufRumpf_unter VertragMarke hO (fun g _ _ _ => .vor g) (fun g _ _ _ _ _ => .nach g)
    (fun i _ _ => .inv i)

/-- The same with every early failure of `rufAt` allowed (the form of the P1 handler premise). -/
theorem rufAt_rufRumpf_lg_alle (hO : LeseblindP P O) (n : Nat) :
    HandlerLG (fun _ => True) (rufAt P O passes n) (rufRumpf P O passes n) :=
  (rufAt_rufRumpf_lg (P := P) (O := O) (passes := passes) hO n).mono (fun _ _ => True.intro)

/-- **An `ok` of `rufAt` is an `ok` of `rufRumpf`**, with the same value and a `≈` world. -/
theorem rufAt_ok_rufRumpf (hO : LeseblindP P O) {n : Nat} {g : D.Fn} {σ σ' σ₁ : World D}
    {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)} (hσ : WeltGleich σ σ')
    (h : rufAt P O passes n g σ ρ = .ok σ₁ v) :
    ∃ σ₂, rufRumpf P O passes n g σ' ρ = .ok σ₂ v ∧ WeltGleich σ₁ σ₂ := by
  have hl := rufAt_rufRumpf_lg (P := P) (O := O) (passes := passes) hO n g σ σ' ρ hσ
  rw [h] at hl
  exact hl.ok_inv

/-- **A reason of `rufAt` is the same reason of `rufRumpf`**, with a `≈` world. -/
theorem rufAt_why_rufRumpf (hO : LeseblindP P O) {n : Nat} {g : D.Fn} {σ σ' σ₁ : World D}
    {ρ : Env D (D.params g)} {r : Fin (D.gruende g)} (hσ : WeltGleich σ σ')
    (h : rufAt P O passes n g σ ρ = .why σ₁ r) :
    ∃ σ₂, rufRumpf P O passes n g σ' ρ = .why σ₂ r ∧ WeltGleich σ₁ σ₂ := by
  have hl := rufAt_rufRumpf_lg (P := P) (O := O) (passes := passes) hO n g σ σ' ρ hσ
  rw [h] at hl
  exact hl.why_inv

end Tiefe

#print axioms rufAt_rufRumpf_unter
#print axioms rufAt_rufRumpf_lg

end Gabbro.Stage0.Senke.BildLauf
