/-
  Structural cell fixture with its current checker characterization and
  concrete cell occurrences. Generated-space completeness is not asserted.
-/
module
public import Grammatik.Gen.Abdeckung.Satz.Raum
public import Grammatik.Gen.Erzeuger.Entscheidung
public import Grammatik.Korpus.Zeugnis.Zeugnis.T1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Gabbro.Grammatik.Gen.Zeugen.M103_131

open Gabbro.Grammatik Gabbro.Grammatik.Gen

abbrev z : Spez := mitglieder.getD 103 {}

def b0 : Rumpf z.deklaration ⟨0, by decide⟩ :=
  (.cons (.locks (⟨0, by decide⟩ : Fin z.locks.length) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) .nil) (.ret .empty (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)))

def b1 : Rumpf z.deklaration ⟨1, by decide⟩ :=
  (.cons (.traverse (⟨0, by decide⟩ : Fin z.tabs.length) .tru (.regRead (⟨0, by decide⟩ : Fin z.regs.length) (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl) .nil)) (.ret .empty (by first | rfl | decide +revert | exact @of_decide_eq_true _ (decGdarf _ _ _) rfl | exact @of_decide_eq_true _ (decDarf _ _ _) rfl | exact @of_decide_eq_true _ (decRufPasst _ _ _) rfl)))

def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨n + 2, h⟩ => absurd h (by have : z.fns.length = 2 := (by decide); omega)

def h0 : Haut z.deklaration := ⟨r, fun f => [false, false].getD f.val false⟩

def ws : List z.deklaration.Fn := [(⟨0, by decide⟩ : Fin z.fns.length)]

def P : Programm z.deklaration := h0.programm


/-- The test as a program of the source. -/
def e : Einsatz := z.einsatz P ws (by decide) (by decide)

/-- Every structural cell is admitted; full checker acceptance is separate. -/
theorem e_strukturell : Adaequanz.akzeptiert Einsatz.Hat gutTafel e := by
  change ∀ z ∈ e.zellen, gutTafel z = true
  decide

/-- Full acceptance additionally requires the invariant and contract gates. -/
theorem e_gueltig_iff_gates : e.gueltig = true ↔
    @Invarianten.Pruefer.programInvariantsB e.D e.P e.S e.fs e.lockSources {} e.ls = true ∧
    @Vertraege.Pruefer.KontrakteGeprueftB e.D e.P e.S e.fs e.lockSources {} (fun _ => none) = true := by
  rw [einsatz_akzeptiert e]
  simp only [e_strukturell, true_and]

/-- Both gates compute their certificates from the preserved source formulas. -/
theorem e_gueltig : e.gueltig = true :=
  e_gueltig_iff_gates.mpr (by decide +kernel)

theorem e_hat : ∀ x ∈ ([⟨0, 0, true, [true, false, false]⟩, ⟨1, 0, true, [true, false, true]⟩, ⟨1, 0, true, [true, false, false]⟩, ⟨1, 0, true, [false, false, true]⟩, ⟨1, 0, true, [false, false, false]⟩, ⟨2, 1, true, [true, true]⟩, ⟨2, 2, false, [true, false, true]⟩, ⟨3, 0, true, [true, true]⟩, ⟨3, 0, true, [false, true]⟩, ⟨3, 0, true, [false, false]⟩, ⟨4, 0, true, [false, false]⟩, ⟨4, 0, true, [true, true]⟩, ⟨5, 0, true, [false, false]⟩, ⟨6, 0, true, [false, false, false]⟩, ⟨6, 1, true, [false, true, false, false]⟩, ⟨6, 1, true, [false, true, true, true]⟩, ⟨6, 1, true, [false, true, false, true]⟩, ⟨6, 1, true, [false, false, false, false]⟩, ⟨6, 1, true, [false, false, true, true]⟩, ⟨6, 1, true, [false, false, false, true]⟩, ⟨7, 0, true, [false, true]⟩, ⟨7, 1, false, [true, false, false]⟩, ⟨7, 0, true, [true, true]⟩, ⟨7, 1, false, [true, true, true]⟩, ⟨8, 0, true, [false, false, true]⟩, ⟨8, 0, true, [false, false, false]⟩, ⟨8, 0, true, [true, false, true]⟩, ⟨9, 0, true, [false, true, true, false]⟩, ⟨9, 0, true, [false, true, false, true]⟩, ⟨9, 0, true, [false, false, false, false]⟩, ⟨9, 0, true, [false, false, false, true]⟩, ⟨9, 0, true, [false, false, true, false]⟩, ⟨9, 0, true, [false, true, false, false]⟩] : List Zelle), e.Hat x := by decide

end Gabbro.Grammatik.Gen.Zeugen.M103_131
