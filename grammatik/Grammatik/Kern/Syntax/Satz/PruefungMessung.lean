/- C16 inventory item 11: actual measurement samples and floor results.

   A report (`CheckReport`, `Satz/Pruefung.lean`) is the retained data of one
   completed probe run: the samples, the evaluated floor outcomes and the
   verdict. This file gives that data its meaning:

   * `messWert`: the actual sample at a place and observation point -- the first
     read entry, never a guessed value. A missing value on an early returning
     path is explicit absence (`none`), never zero.
   * `bodenHalten`: every evaluated floor outcome holds.
   * `berichtDeckt`: the report covers the declared measured places -- every
     place has a read sample at some point.

   The admission Bool and the goal leg live on the Zielsatz side
   (`Zielsatz/Kern/Akzeptiert/CheckDecide`, `Zielsatz/Kern/Spec/Teil4`), where the
   call-graph closure and the machine are in scope. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung

@[expose] public section

namespace Gabbro.Grammatik

/-- The actual sample at a place and observation point: the first read entry.
    Absence (no read entry) is `none` -- an early return before a local sample
    stays an explicit absent sample, never zero. -/
def messWert (r : CheckReport) (ort : String) (punkt : Nat) : Option Int :=
  (r.proben.find? fun p => decide (p.ort = ort ∧ p.punkt = punkt ∧ p.gelesen = true)).map
    (·.wert)

/-- Every evaluated floor outcome holds. -/
def bodenHalten (r : CheckReport) : Prop :=
  ∀ b ∈ r.boeden, b = true

/-- The report covers the declared measured places: every place has a read
    sample at some observation point. -/
def berichtDeckt (misst : List String) (r : CheckReport) : Prop :=
  ∀ m ∈ misst, ∃ p ∈ r.proben, p.ort = m ∧ p.gelesen = true

/-- No measured place is vacuously covered. -/
theorem berichtDeckt_leer (r : CheckReport) : berichtDeckt [] r :=
  fun m hm => absurd hm List.not_mem_nil

/-! ## The fixture: one read sample, one held floor, both verdicts -/

/-- A completed measurement with a positive verdict: the sample was read and the
    floor holds. -/
def messBerichtWahr : CheckReport :=
  { proben := [{ ort := "x", punkt := 0, wert := 3, gelesen := true }],
    boeden := [true], urteil := true }

/-- A completed measurement with a negative verdict: the sample was read, the
    floor failed, and the verdict records it -- distinguishable report data,
    never a missing run. -/
def messBerichtFalsch : CheckReport :=
  { proben := [{ ort := "x", punkt := 0, wert := 3, gelesen := true }],
    boeden := [false], urteil := false }

/-- The read sample is found by its place and point. -/
theorem messWert_zeuge : messWert messBerichtWahr "x" 0 = some 3 := rfl

/-- Another place has no sample: explicit absence, never zero. -/
theorem messWert_anderer_zeuge : messWert messBerichtWahr "y" 0 = none := rfl

/-- An unread entry is no sample either. -/
theorem messWert_ungelesen_zeuge :
    messWert { proben := [{ ort := "x", punkt := 0, wert := 3, gelesen := false }],
      boeden := [], urteil := true } "x" 0 = none := rfl

/-- The held floor holds. -/
theorem bodenHalten_zeuge : bodenHalten messBerichtWahr := by decide

/-- The failed floor does not hold. -/
theorem bodenFehlt_zeuge : ¬ bodenHalten messBerichtFalsch := by decide

/-- The read sample covers its place. -/
theorem berichtDeckt_zeuge : berichtDeckt ["x"] messBerichtWahr := by decide

/-- An unread entry covers nothing: the early-returning path before a local
    sample stays an explicit gap. -/
theorem berichtLuecke_zeuge :
    ¬ berichtDeckt ["x"] { proben := [{ ort := "x", punkt := 0, wert := 3,
      gelesen := false }], boeden := [], urteil := true } := by decide

/-- An incomplete report: a report with an unread sample is not complete. -/
theorem berichtUnvollstaendig_zeuge :
    ¬ CheckReport.vollstaendig { proben := [{ ort := "x", punkt := 0, wert := 3,
      gelesen := false }], boeden := [], urteil := true } := by decide

end Gabbro.Grammatik
