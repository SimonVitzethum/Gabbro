/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module

public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Fein.Zellen
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap.F03_reg

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({ locks := [{ rang := 0 }],
    tabs := [{ count := 1, felder := [{ typ := .int 0 1 }], sperre := some 0 },
      { count := 1, felder := [{ typ := .int 0 1 }] },
      { count := 1, felder := [{ typ := .int 0 1 }], sperre := some 0 }],
    regs := [{ typ := .bool, klasse := .r, traeger := [0, 1, 2] }],
    sigs := [{ haelt := [0] }, { schreibt := [0], boden := some 0 }],
    fns := [0, 1] } : Spez).einzeln

/-- The ordinary read supplies the guarded footprint; the register is still read. -/
def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.slot ⟨0, by decide⟩ ⟨0, by decide⟩ (.lit 0) (by decide))
    (.regRead ⟨0, by decide⟩ (by decide) (.ret .empty (List.Perm.refl _)))

/-- A repeated root can write the first guarded carrier; the third stays separate. -/
def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .cons (.locks ⟨0, by decide⟩ (by decide)
    (.cons (.call ⟨0, by decide⟩ .nil (by decide) (by decide)) .nil))
    (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by change n + 2 < 2 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨1, by decide⟩, ⟨1, by decide⟩] (by decide) (by decide)

def requested : List Zelle := [
  ⟨2, 0, true, [true, false, true, false]⟩,
  ⟨2, 1, true, [true, false]⟩,
  ⟨2, 1, true, [false, true]⟩,
  ⟨2, 1, true, [true, true]⟩]

/-- The model cells pass; register reads still lack a contract-VC rule. -/
theorem e_strukturell : Adaequanz.akzeptiert Einsatz.Hat gutTafel e := by
  change ∀ x ∈ e.zellen, gutTafel x = true
  decide

def cause : Option Invarianten.Frag.Refusal :=
  match @Vertraege.Pruefer.checkContracts e.D e.P e.S e.fs
      e.lockSources {} (fun _ => none) with
  | .error reason => some reason
  | .ok _ => none

theorem e_cause : cause = some (.unsupported
    "contract end block is outside the checked control fragment") := by decide +kernel

theorem e_refused : e.gueltig = false := by decide +kernel

/-- The intended footprint vectors exist even though the checker refuses the body. -/
theorem requested_present : ∀ x ∈ requested, e.Hat x := by decide

theorem requested_refusal_zeuge : ⟨2, 0, true, [true, false, true, false]⟩ ∈ requested ∧
    e.Hat ⟨2, 0, true, [true, false, true, false]⟩ ∧ e.gueltig = false :=
  ⟨by decide, requested_present _ (by decide), e_refused⟩

/-- Input-side evidence, independent of the diagnostic evaluator. -/
def RegInput : Prop :=
  (⟨0, by decide⟩ : z.deklaration.Reg) ∈ (P.rumpf ⟨0, by decide⟩).regs ∧
  e.HatF ⟨0, 6, 10, false, []⟩

theorem e_input : RegInput := by decide

theorem e_cause_link : RegInput → cause = some (.unsupported
    "contract end block is outside the checked control fragment") := fun _ => e_cause

theorem e_cause_link_zeuge : RegInput ∧ cause = some (.unsupported
    "contract end block is outside the checked control fragment") ∧ e.gueltig = false :=
  ⟨e_input, e_cause_link e_input, e_refused⟩

-- Diagnostic output only; the final cell assertions are kernel checked.
#eval e.gueltig
#eval (requested.filter (fun x => !e.zellen.contains x)).map (·.lean)
#eval e.zellen.eraseDups.map (·.lean)

end Gabbro.Grammatik.Gen.Zeugen.Gap.F03_reg
