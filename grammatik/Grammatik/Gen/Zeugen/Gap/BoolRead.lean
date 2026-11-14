/- A Boolean-memory read refused by the scalar observation fragment. -/
module

public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Fein.Zellen
public import Grammatik.Gen.Zeugen.M.ScalarRead
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap.BoolRead

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({ globs := [{ typ := .bool }] } : Spez).einzeln

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.glob ⟨0, by decide⟩ (by decide)) (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨n + 1, h⟩ => absurd h (by change n + 1 < 1 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨0, by decide⟩] (by decide) (by decide)

/-- Structural cells pass; the stricter scalar reifier refuses Boolean memory. -/
theorem e_strukturell : Adaequanz.akzeptiert Einsatz.Hat gutTafel e := by
  change ∀ x ∈ e.zellen, gutTafel x = true
  decide

def cause : Option Invarianten.Frag.Refusal :=
  match @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
      (fun _ => none) {} (fun _ => none) with
  | .error reason => some reason
  | .ok _ => none

theorem e_cause : cause = some (.unsupported "non-integer memory or string contents") := by decide

theorem e_refused : e.gueltig = false := by decide

def Input : Prop :=
  z.deklaration.gtyp ⟨0, by decide⟩ = .bool ∧
  (.inr ⟨0, by decide⟩ : z.deklaration.Tab ⊕ z.deklaration.Glob) ∈
    endblockOrteP P (P.rumpf ⟨0, by decide⟩)

theorem e_input : Input := by decide

theorem e_cause_link : Input → cause = some (.unsupported
    "non-integer memory or string contents") := fun _ => e_cause

theorem e_cause_link_zeuge : Input ∧ cause = some (.unsupported
    "non-integer memory or string contents") ∧ e.gueltig = false :=
  ⟨e_input, e_cause_link e_input, e_refused⟩

/-- The refused input still has the real memory-read constructor. -/
theorem e_hatF : e.HatF ⟨0, 0, 4, false, []⟩ := by decide

theorem e_hat : e.Hat ⟨0, 0, true, [true, false, false]⟩ := by decide

/-- The replacement changes the scalar representation, not its coarse coverage. -/
theorem scalar_replacement_zeuge : e.gueltig = false ∧ ScalarRead.e.gueltig = true ∧
    e.zellen = ScalarRead.e.zellen ∧ e.HatF ⟨0, 0, 4, false, []⟩ ∧
    ScalarRead.e.HatF ⟨0, 0, 4, false, []⟩ :=
  ⟨e_refused, ScalarRead.e_gueltig, by decide, e_hatF, ScalarRead.e_hatF⟩

#print axioms scalar_replacement_zeuge

end Gabbro.Grammatik.Gen.Zeugen.Gap.BoolRead

