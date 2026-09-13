/-
  File:      Grammatik/Uebersetzung.lean
  Subject:   TRANSLATION STAGE, FIRST CUT (PLAN-ERWEITUNG.md section 6,
             lane E5) -- the checker runs the translator at translation
             time and checks the payload; the certificate is the payload's
             typing derivation, so Lean checks the OUTPUT and never needs
             the translator.
-/

namespace Gabbro.Grammatik.Uebersetzung

/-- Payload certificate (encoding N): every entry of the payload table
    lies in the field range `lo .. hi`. -/
def nutzlastZert (t : List Nat) (lo hi : Nat) : Bool :=
  t.all fun v => decide (lo ≤ v ∧ v ≤ hi)

/-- The example payload of `beispiele/106`: the region `{ 10 20 30 40 }`
    as a table of four integers. -/
def sumPayload : List Nat := [10, 20, 30, 40]

/-- The certificate closes by `decide`: every entry is in `0 .. 100`. -/
theorem sumPayload_zert : nutzlastZert sumPayload 0 100 = true := by
  decide

/-
  CUTS: the generic certificate lemma (closed certificate yields every
  entry's range), the joint witness, and the `#print axioms` lines.
  The translator itself is NOT verified (PLAN-ERWEITUNG.md section 0:
  the output is checked, never the expander) -- running it is the
  checker's job (`crates/gabbro-check/src/uebersetzung.rs`), printing
  the values is trust base exactly as in `Konstanten.lean`.
-/

#print axioms sumPayload_zert
