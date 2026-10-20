/-
  File:      Grammatik/ArenaSperreRuf.lean
  Subject:   A RECOGNIZED FUNCTION CALLED THROUGH THE PROGRAM SEMANTICS (PLAN-DYNAMIC.md section 8a.3, premises 2 and
             3): `rufAt` -- the sequential meaning of a call, which checks `requires`, runs the body (`execEnd`), checks
             `ensures` and the owed invariants, and answers -- answers in an arena-consistent world when the body is
             `ErkE` and the world it was called in was.

  `rufAt_erk` is the premise `RErhaelt` of the call-form section theorem (`abschnitt_rufe`) for `R := rufAt P O passes n`,
  and for the patched handler `rufFrei` (it only turns `logik` answers into `hardware`). Together with `erkE_koerperH`
  (`execEndH = execEnd` on recognized bodies) this is the form in which `InvGutS` reads the recognizer: the arena part
  of the owed invariant at a return, `erkE_invGutS`.
-/
import Grammatik.Bausteine.Arena.Struktur.Sperre.ArenaSperreAbschnitt

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

section Ruf
variable {A : FreiForm D} (K : Dekl A) (P : Programm D) (O : Orakel D) (passes : Nat)

/-- Recording the reads of a list of invariants keeps the arena invariant. -/
theorem Dekl.Ok.foldl_lese {σ : World D} (h : K.Ok σ) (is : List D.Inv) (f : D.Inv → List (Res D))
    (g : D.Inv → List (D.Tab ⊕ D.Glob)) : K.Ok (is.foldl (fun σ' i => σ'.lese (f i) (g i)) σ) := by
  induction is generalizing σ with
  | nil => exact h
  | cons i is ih => exact ih (Dekl.Ok.lese K (f i) (g i) h)

/-- **A recognized function answers in an arena-consistent world.** For every callee `f` whose body is `ErkE`: from a
    world where the arena invariant holds, `rufAt` returns (a value or a reason) in one where it holds. (An answer by
    `logik` or `hardware` promises nothing, as in `StrukturPost`.) -/
theorem rufAt_erk (W : D.Fn → Prop) (hW : ∀ f, W f → ErkE K Abs.leer (P.rumpf f)) :
    ∀ n : Nat, RErhaelt K W (rufAt P O passes n) := by
  intro n f hf σ ρ hS
  cases n with
  | zero => exact ⟨fun σ' v h => by simp [rufAt] at h, fun σ' r h => by simp [rufAt] at h⟩
  | succ n =>
    have hS1 := Dekl.Ok.lese K (Signatur.anfang D (D.signatur f)) (P.requires f).orte hS
    have hpost := erkE_koerper O passes (rufAt P O passes n) K (hW f hf) _ ρ hS1 Abs.leer
    constructor
    · intro σ' v h
      simp only [rufAt] at h
      split at h
      · cases h
      · revert h hpost
        generalize execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f) _ ρ = x
        cases x with
        | zurueck σ2 v2 =>
          intro hpost h
          simp only [EndAusgang.zuAusgang, StrukturPost] at hpost
          have hS2 := Dekl.Ok.lese K (vertragVon D f).ende (P.ensures f).orte hpost
          simp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · cases h
              exact Dekl.Ok.foldl_lese K hS2 _ _ _
        | why σ2 r => intro _ h; cases h
        | leave hh σ2 ρ2 => intro hpost _; exact absurd hh (by decide)
        | next hh σ2 ρ2 => intro hpost _; exact absurd hh (by decide)
        | logik e => intro _ h; cases h
        | hardware e => intro _ h; cases h
    · intro σ' r h
      simp only [rufAt] at h
      split at h
      · cases h
      · revert h hpost
        generalize execEnd (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f) _ ρ = x
        cases x with
        | zurueck σ2 v2 =>
          intro _ h
          simp only at h
          split at h
          · cases h
          · split at h <;> cases h
        | why σ2 r2 =>
          intro hpost h
          simp only [EndAusgang.zuAusgang, StrukturPost] at hpost
          cases h
          exact hpost
        | leave hh σ2 ρ2 => intro hpost _; exact absurd hh (by decide)
        | next hh σ2 ρ2 => intro hpost _; exact absurd hh (by decide)
        | logik e => intro _ h; cases h
        | hardware e => intro _ h; cases h

end Ruf

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.rufAt_erk
