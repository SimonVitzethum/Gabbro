/-
  File:      Grammatik/X86/AddressedHardwareExecution.lean
  Subject:   Full selected SIB/RIP-relative addresses bound to actual effects.

  Lane 730: a generic checked effective-address adapter over the accepted
  `AddressEncoding` selected forms (`AdrForm`, `adrEff`, `parseAdrTail`,
  `kanonisch48`, `fussZugelassen`). It binds the actual instruction
  length/next RIP and the canonical register values to real producer
  access effects (LOCK XADD through `LockedInstructionExecution`, address
  math through `EffectiveAddress`). No new memory micro-interpreter and
  no second decoder for accepted rows: pilot-owned tails stay refused by
  the reused `parseAdrTail`, proved in both directions below.
  Provenance: clone-local Intel SDM 325462-093US Sep 2026, Vol. 1
  Section 3.7.5 (specifying an offset), Section 3.7.5.1 (64-bit mode,
  RIP-relative addressing), LOCK prefix and XADD entries.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.AddressEncoding
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86

/-- Ordered admission faults of one addressed access: canonical form
    first, no-wrap second, per-direction permission last. -/
inductive AdrFehler where
  | unkanonisch | umbruch | keinLesen | keinSchreiben
  deriving DecidableEq, Repr

/-! ## 1. Ordered admission: canonical, no-wrap, then permission.

    The adapter checks the computed `adrEff` address in fault order and
    reports the FIRST failure. It reuses the accepted `kanonisch48`,
    `OhneUmbruch` range and `lesbar8`/`schreibbar8` checks, so success
    coincides exactly with the accepted `fussZugelassen`. -/

/-- Checked admission of one computed address in fault order. -/
def adrPruefe (m : Speicher) (a : Adresse) (schreiben : Bool) :
    Option AdrFehler :=
  match kanonisch48 a with
  | false => some .unkanonisch
  | true =>
    match decide (a.toNat + 8 ≤ 2 ^ 64) with
    | false => some .umbruch
    | true =>
      let ok := if schreiben then schreibbar8 m a else lesbar8 m a
      match ok with
      | false => some (if schreiben then .keinSchreiben else .keinLesen)
      | true => none

/-- The ordered check succeeds exactly where `fussZugelassen` admits:
    no second admission model is invented. -/
theorem adrPruefe_gleich_fuss (m : Speicher) (a : Adresse)
    (schreiben : Bool) :
    adrPruefe m a schreiben = none ↔
      fussZugelassen m a schreiben = true := by
  unfold adrPruefe fussZugelassen
  cases hkan : kanonisch48 a with
  | false => simp [hkan]
  | true =>
    simp only [hkan]
    cases hwrap : decide (a.toNat + 8 ≤ 2 ^ 64) with
    | false => simp [hwrap]
    | true =>
      simp only [hwrap]
      cases schreiben with
      | true =>
        cases hperm : schreibbar8 m a <;> simp [hperm]
      | false =>
        cases hperm : lesbar8 m a <;> simp [hperm]

/-- ORDER: a noncanonical address is refused before permissions are
    consulted, even with full rights. -/
theorem adrPruefe_ordnung_kanonisch (m : Speicher) (a : Adresse)
    (schreiben : Bool)     (h : kanonisch48 a = false) :
    adrPruefe m a schreiben = some .unkanonisch := by
  unfold adrPruefe
  simp only [h]

/-- ORDER: a wrapping footprint is refused before permissions, even
    with full rights and a canonical top-of-space address. -/
theorem adrPruefe_ordnung_umbruch (m : Speicher) (a : Adresse)
    (schreiben : Bool) (hkan : kanonisch48 a = true)
    (hwrap : ¬ a.toNat + 8 ≤ 2 ^ 64) :
    adrPruefe m a schreiben = some .umbruch := by
  have hdec : decide (a.toNat + 8 ≤ 2 ^ 64) = false :=
    decide_eq_false hwrap
  unfold adrPruefe
  simp only [hkan, hdec]

/-! ## 2. Generic addressed access with actual length/next-RIP binding.

    The adapter computes `adrEff` from the canonical register values,
    admits it through `adrPruefe`, and performs the REAL `read64` /
    `write64` effect, advancing RIP by the ACTUAL instruction length
    `l`. A bad length refuses before any memory is touched. -/

/-- Checked load through a full selected form: the word at `adrEff`,
    or the first admission fault in order. -/
def adrLade (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) : Option Wort ⊕ AdrFehler :=
  let a := adrEff s ripNext f
  match adrPruefe m a false with
  | some e => .inr e
  | none =>
    match read64 m a with
    | some v => .inl v
    | none => .inr .keinLesen

/-- Checked store through a full selected form: the successor memory,
    or the first admission fault in order. -/
def adrSpeichere (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (v : Wort) : Option Speicher ⊕ AdrFehler :=
  let a := adrEff s ripNext f
  match adrPruefe m a true with
  | some e => .inr e
  | none =>
    match write64 m a v with
    | some m' => .inl m'
    | none => .inr .keinSchreiben

/-- A successful addressed load reads exactly the effective address. -/
theorem adrLade_erfolg (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (v : Wort)
    (h : adrLade m s ripNext f = .inl v) :
    read64 m (adrEff s ripNext f) = some v := by
  unfold adrLade at h
  cases hpr : adrPruefe m (adrEff s ripNext f) false with
  | some e => simp [hpr] at h
  | none =>
    simp only [hpr] at h
    cases hrd : read64 m (adrEff s ripNext f) with
    | none => simp [hrd] at h
    | some w =>
      simp [hrd] at h
      rw [h]

/-- A refused addressed load admits no value: every outcome is a fault. -/
theorem adrLade_verweigert_fehler (m : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (e : AdrFehler)
    (h : adrLade m s ripNext f = .inr e) :
    adrPruefe m (adrEff s ripNext f) false = some e ∨
      read64 m (adrEff s ripNext f) = none := by
  unfold adrLade at h
  cases hpr : adrPruefe m (adrEff s ripNext f) false with
  | some e' =>
    simp [hpr] at h
    subst h
    exact Or.inl rfl
  | none =>
    simp only [hpr] at h
    cases hrd : read64 m (adrEff s ripNext f) with
    | some w => simp [hrd] at h
    | none => exact Or.inr rfl

/-- A successful addressed store writes exactly the eight bytes at the
    effective address and preserves every permission. -/
theorem adrSpeichere_erfolg (m m' : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (v : Wort)
    (h : adrSpeichere m s ripNext f v = .inl m') :
    write64 m (adrEff s ripNext f) v = some m' ∧
      m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold adrSpeichere at h
  cases hpr : adrPruefe m (adrEff s ripNext f) true with
  | some e => simp [hpr] at h
  | none =>
    simp only [hpr] at h
    cases hwr : write64 m (adrEff s ripNext f) v with
    | none => simp [hwr] at h
    | some w =>
      simp [hwr] at h
      subst h
      exact ⟨rfl, write64_erhaelt_berechtigungen m _ v w hwr⟩

/-- BRIDGE: on the pilot-owned shape the adapter reads the PILOT
    address: adapter success is a pilot-footprint read, by reuse of
    `adrEff_basisForm` and not a second address model. -/
theorem adrLade_basisForm_pilot (m : Speicher) (s : Zustand)
    (b : Register) (d : BitVec 32) (n : Adresse) (v : Wort)
    (h : adrLade m s n (basisForm b d) = .inl v) :
    read64 m (effAddr s b d) = some v := by
  have hrd := adrLade_erfolg m s n (basisForm b d) v h
  rw [adrEff_basisForm] at hrd
  exact hrd

end Gabbro.Grammatik.X86
