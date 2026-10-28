/-
  File:      Grammatik/Logik/Terminierung/KlasseZeuge.lean
  Subject:   WITNESSES OF THE TERMINATION CLASSES (2026-10-22): every class is met by a program the algorithm
             computes it for (`decide`), on the one-function declaration of BudgetZeuge.lean.

  * `return;` -- `endet`;
  * `f(); f(); return;` with a measure on `f` -- `endet` (measured recursion), without one -- `abgelehnt` (a
    non-tail call on a cycle);
  * `f(); return;` without a measure -- `bedingt` (a tail-call cycle: a state machine);
  * `forever { } return;` -- `umgebung`; `forever { leave; } return;` and `forever { return; }` -- `bedingt`.
  And `ewigFrei` (the premise of `endet_satz`'s budget half) holds exactly for the `forever`-free ones.
-/
import Grammatik.Logik.Terminierung.Entscheidung
import Grammatik.Logik.Terminierung.Ausgang
import Grammatik.Zielsatz.Eigenschaften.BudgetZeuge

namespace Gabbro.Grammatik.Terminierung.KlasseZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz.BudgetZeuge

/-- The held set at entry. -/
abbrev Λ0 : List (Res bD) := Signatur.anfang bD (bD.signatur ())

theorem hpB : RufPasst bD (vertragVon bD ()) (bD.signatur ()) Λ0 where
  hw := fun t => t.elim
  hg := fun g => g.elim
  hk := ⟨[], List.Perm.refl [], by simp only [List.nil_sublist]⟩
  hh := fun L => L.elim

/-- `return;` -/
def rRet : Endblock bD (vertragVon bD ()) false (bD.params ()) Λ0 := .ret .empty (List.Perm.refl _)

/-- `f(); return;` -- a tail call. -/
def rEnd : Endblock bD (vertragVon bD ()) false (bD.params ()) Λ0 :=
  .cons (.call () .nil hpB rfl) (.ret .empty (List.Perm.refl _))

/-- `f(); f(); return;` -- the first call is not in tail position. -/
def rZwei : Endblock bD (vertragVon bD ()) false (bD.params ()) Λ0 :=
  .cons (.call () .nil hpB rfl) (.cons (.call () .nil hpB rfl) (.ret .empty (List.Perm.refl _)))

/-- `forever { leave; } return;` -/
def rLeave : Endblock bD (vertragVon bD ()) false (bD.params ()) Λ0 :=
  .cons (.forever () Expr.tru (.cons (.leave rfl) .nil)) (.ret .empty (List.Perm.refl _))

/-- `forever { return; }` -/
def rRueck : Endblock bD (vertragVon bD ()) false (bD.params ()) Λ0 :=
  .cons (.forever () Expr.tru (.cons (.ret .empty (List.Perm.refl _)) .nil)) (.ret .empty (List.Perm.refl _))

/-- The program with body `r`. -/
def prog (r : Endblock bD (vertragVon bD ()) false (bD.params ()) Λ0) : Programm bD :=
  { bP with rumpf := fun _ => r }

/-- No measure, and a measure. -/
def ohne : Unit → Bool := fun _ => false
def mit : Unit → Bool := fun _ => true

theorem kz_endet : klasse (prog rRet) [()] ohne () = .endet := by decide
theorem kz_endet_mass : klasse (prog rZwei) [()] mit () = .endet := by decide
theorem kz_abgelehnt : klasse (prog rZwei) [()] ohne () = .abgelehnt := by decide
theorem kz_bedingt_end : klasse (prog rEnd) [()] ohne () = .bedingt := by decide
theorem kz_umgebung : klasse bP [()] ohne () = .umgebung := by decide
theorem kz_bedingt_leave : klasse (prog rLeave) [()] ohne () = .bedingt := by decide
theorem kz_bedingt_rueck : klasse (prog rRueck) [()] ohne () = .bedingt := by decide

theorem kz_ewigFrei : ewigFrei (prog rZwei) [()] () = true := by decide
theorem kz_nicht_ewigFrei : ewigFrei bP [()] () = false := by decide

/-- **The exit condition on the witnesses**: `forever { }` (class `umgebung`) ends only at a logic or hardware
    stop, for every oracle, handler, grant of passes and start; `forever { leave; }` (class `bedingt`) completes after
    one pass. -/
theorem kz_umgebung_endet_nie (O : Orakel bD) (passes : Nat)
    (R : ∀ f : bD.Fn, World bD → Env bD (bD.params f) → RufAusgang f) (σ : World bD) (ρ : Env bD (bD.params ())) :
    (∃ e, execStmt (l := false) O passes R
        (.forever () Expr.tru (.nil : Block bD (vertragVon bD ()) true (bD.params ()) Λ0 Λ0)) σ ρ = .logik e) ∨
      ∃ e, execStmt (l := false) O passes R
        (.forever () Expr.tru (.nil : Block bD (vertragVon bD ()) true (bD.params ()) Λ0 Λ0)) σ ρ = .hardware e :=
  forever_umgebung O passes R () Expr.tru .nil rfl σ ρ

theorem kz_bedingt_endet (O : Orakel bD) (R : ∀ f : bD.Fn, World bD → Env bD (bD.params f) → RufAusgang f)
    (σ : World bD) (ρ : Env bD (bD.params ())) :
    ∃ σ', execStmt (l := false) O 1 R
      (.forever () Expr.tru (.cons (.leave rfl) .nil : Block bD (vertragVon bD ()) true (bD.params ()) Λ0 Λ0)) σ ρ =
        .ok σ' ρ :=
  ⟨_, rfl⟩

end Gabbro.Grammatik.Terminierung.KlasseZeuge
