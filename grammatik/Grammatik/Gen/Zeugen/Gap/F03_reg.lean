/- Checked coverage fixture; requested cells remain explicit even when absent. -/
module



public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1
public import Grammatik.Gen.Fein.Zellen
public import Grammatik.Gen.Zeugen.Gap.Audit
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

set_option maxRecDepth 4096

namespace Gabbro.Grammatik.Gen.Zeugen.Gap.F03_reg

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := ({
    locks := [{ rang := 0 }],
    tabs := [{ count := 1, felder := [{ typ := .int 0 1 }], sperre := some 0 },
      { count := 1, felder := [{ typ := .int 0 1 }] },
      { count := 1, felder := [{ typ := .int 0 1 }], sperre := some 0 }],
    regs := [{ typ := .bool, klasse := .r, traeger := [0, 1, 2] }],
    sigs := [{ haelt := [0] }, { schreibt := [0], boden := some 0 }],
    fns := [0, 1] } : Spez).einzeln

/-- The ordinary read supplies the guarded footprint; the register is still read. -/
def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  .bind (.slot (D := z.deklaration) (⟨0, by decide⟩ : z.deklaration.Tab) (⟨0, by decide⟩ : z.deklaration.Feld ⟨0, by decide⟩) (.lit 0) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl))
    (.regRead (D := z.deklaration) ⟨0, by decide⟩ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (.ret .empty (List.Perm.refl _)))

/-- A repeated root can write the first guarded carrier; the third stays separate. -/
def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  .cons (.locks (D := z.deklaration) (⟨0, by decide⟩ : z.deklaration.Lock) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)
    (.cons (.call (D := z.deklaration) ⟨0, by decide⟩ .nil (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)) .nil))
    (.ret .empty (List.Perm.refl _))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by change n + 2 < 2 at h; omega)

def P : Programm z.deklaration := (⟨r, fun _ => false⟩ : Haut z.deklaration).programm

def e : Einsatz := z.einsatz P [⟨1, by decide⟩, ⟨1, by decide⟩] (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)

def requested : List Zelle := [
  ⟨2, 0, true, [true, false, true, false]⟩,
  ⟨2, 1, true, [true, false]⟩,
  ⟨2, 1, true, [false, true]⟩,
  ⟨2, 1, true, [true, true]⟩]

/-- The structural model cells pass independently of the contract certificate. -/
theorem e_strukturell : Adaequanz.akzeptiert Einsatz.Hat gutTafel e := by
  change ∀ x ∈ e.zellen, gutTafel x = true
  decide

def cause : Option Invarianten.Frag.Refusal := GateAudit.contractCause e

theorem e_cause : cause = none := by decide +kernel

theorem e_gueltig : e.gueltig = true := by decide +kernel

/-- The intended footprint vectors exist and the checked register body is accepted. -/
theorem requested_present : ∀ x ∈ requested, e.Hat x := by decide

theorem requested_checked_zeuge : ⟨2, 0, true, [true, false, true, false]⟩ ∈ requested ∧
    e.Hat ⟨2, 0, true, [true, false, true, false]⟩ ∧ e.gueltig = true :=
  ⟨by decide, requested_present _ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl), e_gueltig⟩

/-- Input-side evidence, independent of the diagnostic evaluator. -/
def RegInput : Prop :=
  (⟨0, by decide⟩ : z.deklaration.Reg) ∈ (P.rumpf ⟨0, by decide⟩).regs ∧
  e.HatF ⟨0, 6, 10, false, []⟩

theorem e_input : RegInput := by
  constructor
  · change (⟨0, by decide⟩ : z.deklaration.Reg) ∈ [⟨0, by decide⟩]
    exact List.mem_cons_self
  · decide

theorem e_cause_link : RegInput → cause = none := fun _ => e_cause

theorem e_cause_link_zeuge : RegInput ∧ cause = none ∧ e.gueltig = true :=
  ⟨e_input, e_cause_link e_input, e_gueltig⟩

/-- Exact cell set, including every companion cell of this fixture. -/
def zellen : List Zelle := [
  ⟨0, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [true, false, true]⟩,
  ⟨1, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [false, true, true]⟩,
  ⟨1, 0, true, [false, false, false]⟩,
  ⟨1, 0, true, [true, true, true]⟩,
  ⟨2, 0, true, [true, false, true, false]⟩,
  ⟨2, 2, false, [false, true, true]⟩,
  ⟨2, 3, false, [false, false, true]⟩,
  ⟨2, 1, true, [true, false]⟩,
  ⟨2, 1, true, [false, true]⟩,
  ⟨2, 2, false, [false, true, false]⟩,
  ⟨2, 1, true, [true, true]⟩,
  ⟨3, 0, true, [false, false]⟩,
  ⟨3, 0, true, [true, true]⟩,
  ⟨4, 0, true, [true, true]⟩,
  ⟨4, 0, true, [false, false]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [true, false, false]⟩,
  ⟨6, 1, true, [true, true, false, true]⟩,
  ⟨6, 1, true, [true, true, false, false]⟩,
  ⟨6, 1, true, [true, true, true, true]⟩,
  ⟨7, 0, true, [true, true]⟩,
  ⟨7, 1, false, [true, true, true]⟩,
  ⟨7, 0, true, [false, true]⟩,
  ⟨7, 1, false, [true, false, true]⟩,
  ⟨8, 0, true, [true, false, true]⟩,
  ⟨8, 0, true, [false, false, true]⟩,
  ⟨9, 0, true, [false, true, false, false]⟩,
  ⟨9, 0, true, [false, false, true, false]⟩,
  ⟨9, 0, true, [false, true, true, false]⟩,
  ⟨10, 0, true, [true]⟩]

theorem zellen_exact : e.zellen.eraseDups = zellen := by decide +kernel

theorem e_hat : ∀ x ∈ zellen, e.Hat x := by
  intro x member
  rw [← zellen_exact] at member
  exact List.mem_eraseDups.1 member

theorem e_zeuge : e.gueltig = true ∧ e.Hat ⟨0, 0, true, [true, false, false]⟩ :=
  ⟨e_gueltig, e_hat _ (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)⟩

/-- Missing requested cells are findings, never an altered checker verdict. -/
def missing : List Zelle := requested.filter (fun x => !zellen.contains x)

end Gabbro.Grammatik.Gen.Zeugen.Gap.F03_reg
