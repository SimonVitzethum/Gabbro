/-
  File:      Grammatik/Uebersetzung.lean
  Subject:   TRANSLATION STAGE, FIRST CUT (PLAN-ERWEITUNG.md section 6,
             lane E5) -- the checker runs the translator at translation
             time and checks the payload; the certificate is the payload's
             typing derivation, so Lean checks the OUTPUT and never needs
             the translator.

  The three definition lines below (`sumPayloadVals`, `sumPayloadOk`,
  `sumPayload_zert`) stand verbatim in the checker's printer
  (`crates/gabbro-check/src/uebersetzung.rs`, `payload_certificate`);
  `tests/uebersetzung.rs` holds the two against each other.
-/

namespace Gabbro.Grammatik.Uebersetzung

/-- Payload certificate predicate (encoding N of the certificate
    measurement): every entry of the payload table lies in the field
    range `lo .. hi`. The range proofs stay attached to the entries --
    the measurement's recommendation -- and `decide` walks them entry
    by entry, never as one definitional table comparison. -/
def nutzlastZert (t : List Nat) (lo hi : Nat) : Bool :=
  t.all fun v => decide (lo ≤ v ∧ v ≤ hi)

/-- Generic certificate lemma: a closed certificate yields every
    entry's range. Every premise is used: `h` supplies the closed
    `List.all`, `hm` locates the entry. -/
theorem nutzlastZert_mem {t : List Nat} {lo hi j v : Nat}
    (h : nutzlastZert t lo hi = true)
    (hm : t[j]? = some v) : lo ≤ v ∧ v ≤ hi := by
  unfold nutzlastZert at h
  rw [List.all_eq_true] at h
  have hmem : v ∈ t := List.mem_of_getElem? hm
  have hdec := h v hmem
  exact of_decide_eq_true hdec

/-- The example payload of `beispiele/106`: the region `{ 10 20 30 40 }`
    as a table of four integers. -/
def sumPayloadVals : List Nat := [10, 20, 30, 40]

/-- The payload's typing as a certificate over that table. -/
def sumPayloadOk : Bool := nutzlastZert sumPayloadVals 0 100

/-- The certificate closes by `decide`: every entry is in `0 .. 100`. -/
theorem sumPayload_zert : sumPayloadOk = true := by decide

/-- Joint witness for `nutzlastZert_mem`: the closed certificate, the
    entry lookup, and the concluded range, all at entry 3 (`40`). -/
theorem nutzlastZert_mem_zeuge :
    nutzlastZert sumPayloadVals 0 100 = true ∧
    sumPayloadVals[3]? = some 40 ∧ (0 ≤ 40 ∧ 40 ≤ 100) :=
  ⟨by decide, rfl, by decide, by decide⟩

/-
  CUTS: what is not proved here.

  * The translator itself is NOT verified (PLAN-ERWEITUNG.md section 0:
    the output is checked, never the expander). Running it is the
    checker's job (`uebersetzung::versuch`); printing the values is trust
    base exactly as in `Konstanten.lean` -- what Lean checks is that the
    printed values are well-typed, not that the translator printed them.
  * The call's Hoare triple is not here either: the program-logic Lean
    channel (`lean.rs`) still maps every library call to
    `CallStatement`. What this file carries is the payload's TYPING, the
    one thing the translation certificate promises.
  * `nutzlastZert` covers one integer field. Tree payloads and
    multi-field tables (PLAN-ERWEITUNG.md section 2) need one predicate
    per field, not a wider theorem here.
-/

#print axioms nutzlastZert_mem
#print axioms sumPayload_zert
#print axioms nutzlastZert_mem_zeuge
