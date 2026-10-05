/-
  File:      Grammatik/X86/ValidatorKapDecoder.lean
  Subject:   valX86 decode coverage over the capstone decoder chain.

  Lane 1323: coverage check over `kapDecode` from `HwKapsteinDecoder`
  (accepted, reused unchanged). Every byte of every executable section
  either decodes through the chain or is refused with a named reason
  (`KapGrund`). Chain ties keep the stated priority (first match wins
  in `kapDecode`); the extension interface tries the chain first.
-/
import Grammatik.X86.Hw.Kapstein.HwKapsteinDecoder
import Grammatik.X86.Kern.Bild
namespace Gabbro.Grammatik.X86

/-- Named refusal reasons: every covered byte decodes through the
    chain; anything else is refused with exactly one of these. -/
inductive KapGrund where
  | keinDekoder
  | keinFortschritt
  | keinBrennstoff
  deriving DecidableEq, Repr

/-- Greedy full decode under fuel through the capstone chain
    (`kapDecode`, first match wins). A step that decodes zero bytes
    refuses with `keinFortschritt` instead of looping. -/
def kapDecktFuel : Nat → List Byte → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] => true
  | n + 1, b :: bs =>
    match kapDecode (b :: bs) with
    | none => false
    | some (_, rest) =>
      if rest.length < (b :: bs).length then kapDecktFuel n rest else false

/-- Row-returning traversal: the same walk, collecting the decoded
    rows. `kapDecktFuel` is its Bool shadow. -/
def kapKetteFuel : Nat → List Byte → Option (List KapDekodiert × List Byte)
  | 0, [] => some ([], [])
  | 0, _ :: _ => none
  | _ + 1, [] => some ([], [])
  | n + 1, b :: bs =>
    match kapDecode (b :: bs) with
    | none => none
    | some (d, rest) =>
      if rest.length < (b :: bs).length then
        match kapKetteFuel n rest with
        | none => none
        | some (ds, rest') => some (d :: ds, rest')
      else none

/-! ## 1. Soundness: coverage implies a chain derivation. -/

/-- Unfolding of one Bool-check step (definitional). -/
theorem kapDecktFuel_schritt (n : Nat) (b : Byte) (bs : List Byte) :
    kapDecktFuel (n + 1) (b :: bs) =
      match kapDecode (b :: bs) with
      | none => false
      | some (_, rest) =>
        if rest.length < (b :: bs).length then kapDecktFuel n rest
        else false := rfl

/-- Unfolding of one row-traversal step (definitional). -/
theorem kapKetteFuel_schritt (n : Nat) (b : Byte) (bs : List Byte) :
    kapKetteFuel (n + 1) (b :: bs) =
      match kapDecode (b :: bs) with
      | none => none
      | some (d, rest) =>
        if rest.length < (b :: bs).length then
          match kapKetteFuel n rest with
          | none => none
          | some (ds, rest') => some (d :: ds, rest')
        else none := rfl

/-- SOUNDNESS: if the Bool check covers the bytes, the chain derives
    them into rows with no remainder. Every premise is used: `h`
    drives the induction and feeds each step. -/
theorem valKap_deckung (fuel : Nat) (bs : List Byte)
    (h : kapDecktFuel fuel bs = true) :
    ∃ rows, kapKetteFuel fuel bs = some (rows, []) := by
  induction fuel generalizing bs with
  | zero =>
    cases bs with
    | nil =>
      simp [kapDecktFuel] at h
      exact ⟨[], rfl⟩
    | cons b bs' =>
      simp [kapDecktFuel] at h
  | succ n ih =>
    cases bs with
    | nil =>
      simp [kapDecktFuel] at h
      exact ⟨[], rfl⟩
    | cons b bs' =>
      rw [kapDecktFuel_schritt] at h
      cases hdec : kapDecode (b :: bs') with
      | none =>
        simp [hdec] at h
      | some pr =>
        obtain ⟨d, rest⟩ := pr
        simp only [hdec] at h
        by_cases hprog : rest.length < (b :: bs').length
        · rw [if_pos hprog] at h
          obtain ⟨rows, ihr⟩ := ih rest h
          refine ⟨d :: rows, ?_⟩
          rw [kapKetteFuel_schritt, hdec]
          simp only [if_pos hprog, ihr]
        · rw [if_neg hprog] at h
          simp at h

/-! ## 2. Extension and chain monotonicity. -/

/-- Future decoder row: tried ONLY where the capstone chain refuses.
    The extension never overrides, duplicates, or re-evaluates any
    chain row: `kapDecodeErw` tries `kapDecode` first. -/
structure KapErw where
  ext : List Byte → Option (KapDekodiert × List Byte)

/-- Extended chain decode: the chain first, the new row only where
    the chain refuses. Chain ties keep the stated priority. -/
def kapDecodeErw (e : KapErw) (bs : List Byte) :
    Option (KapDekodiert × List Byte) :=
  match kapDecode bs with
  | some r => some r
  | none => e.ext bs

/-- The extension agrees with the chain on every byte string the
    chain accepts: no chain row is shadowed. -/
theorem kapDecodeErw_kanonisch (e : KapErw) (bs : List Byte)
    (r : KapDekodiert × List Byte)
    (h : kapDecode bs = some r) :
    kapDecodeErw e bs = some r := by
  unfold kapDecodeErw
  rw [h]

/-- Coverage under the extended chain: the same walk, more rows. -/
def kapDecktErwFuel (e : KapErw) : Nat → List Byte → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] => true
  | n + 1, b :: bs =>
    match kapDecodeErw e (b :: bs) with
    | none => false
    | some (_, rest) =>
      if rest.length < (b :: bs).length then kapDecktErwFuel e n rest
      else false

/-- Unfolding of one extended-check step (definitional). -/
theorem kapDecktErwFuel_schritt (e : KapErw) (n : Nat) (b : Byte)
    (bs : List Byte) :
    kapDecktErwFuel e (n + 1) (b :: bs) =
      match kapDecodeErw e (b :: bs) with
      | none => false
      | some (_, rest) =>
        if rest.length < (b :: bs).length then kapDecktErwFuel e n rest
        else false := rfl

/-- MONOTONICITY: adding a decoder row cannot turn a covered byte
    list into an uncovered one. The chain steps replay through
    `kapDecodeErw_kanonisch`; the new row only fires where the chain
    refused, which never happens on a covered walk. -/
theorem valKap_monoton (e : KapErw) (fuel : Nat) (bs : List Byte)
    (h : kapDecktFuel fuel bs = true) :
    kapDecktErwFuel e fuel bs = true := by
  induction fuel generalizing bs with
  | zero =>
    cases bs with
    | nil => rfl
    | cons b bs' =>
      simp [kapDecktFuel] at h
  | succ n ih =>
    cases bs with
    | nil => rfl
    | cons b bs' =>
      rw [kapDecktFuel_schritt] at h
      cases hdec : kapDecode (b :: bs') with
      | none =>
        simp [hdec] at h
      | some pr =>
        obtain ⟨d, rest⟩ := pr
        simp only [hdec] at h
        have herw : kapDecodeErw e (b :: bs') = some (d, rest) :=
          kapDecodeErw_kanonisch e _ _ hdec
        by_cases hprog : rest.length < (b :: bs').length
        · rw [if_pos hprog] at h
          have ihr := ih rest h
          rw [kapDecktErwFuel_schritt, herw]
          simp only [if_pos hprog, ihr]
        · rw [if_neg hprog] at h
          simp at h

/-! ## 3. Image coverage and named refusals. -/

/-- Decode coverage of one section: executable sections must fully
    decode through the capstone chain under explicit fuel; data
    sections carry arbitrary bytes and are not decoded. -/
def kapAbschnittDeckt (bild : Bild) (s : Abschnitt) : Bool :=
  if s.ausfuehrbar then
    kapDecktFuel (s.dateiLen + 1)
      ((bild.datei.drop s.dateiOff).take s.dateiLen)
  else true

/-- Decode coverage of the whole image: every section covered. -/
def kapBildDeckt (bild : Bild) : Bool :=
  bild.abschnitte.all (kapAbschnittDeckt bild)

/-- Chain admission: checked mapping AND full capstone-chain decode
    coverage of every executable section. -/
def valKap (p : Profil) (bild : Bild) : Bool :=
  wohlgeformt p bild && kapBildDeckt bild

/-- Chain admission implies the checked mapping. -/
theorem valKap_wohlgeformt (p : Profil) (bild : Bild)
    (h : valKap p bild = true) :
    wohlgeformt p bild = true := by
  unfold valKap at h
  exact (Bool.and_eq_true_iff.mp h).1

/-- Chain admission implies capstone-chain decode coverage. -/
theorem valKap_deckt (p : Profil) (bild : Bild)
    (h : valKap p bild = true) :
    kapBildDeckt bild = true := by
  unfold valKap at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- Named refusal of one walk: `none` exactly where the Bool check
    passes, `some` reason where it fails. -/
def kapGrundFuel : Nat → List Byte → Option KapGrund
  | 0, [] => none
  | 0, _ :: _ => some .keinBrennstoff
  | _ + 1, [] => none
  | n + 1, b :: bs =>
    match kapDecode (b :: bs) with
    | none => some .keinDekoder
    | some (_, rest) =>
      if rest.length < (b :: bs).length then kapGrundFuel n rest
      else some .keinFortschritt

/-- Unfolding of one refusal-classification step (definitional). -/
theorem kapGrundFuel_schritt (n : Nat) (b : Byte) (bs : List Byte) :
    kapGrundFuel (n + 1) (b :: bs) =
      match kapDecode (b :: bs) with
      | none => some KapGrund.keinDekoder
      | some (_, rest) =>
        if rest.length < (b :: bs).length then kapGrundFuel n rest
        else some KapGrund.keinFortschritt := rfl

/-- CLASSIFICATION: every byte list either decodes through the chain
    or is refused with a named reason, never silently. -/
theorem kapGrund_klassifiziert (fuel : Nat) (bs : List Byte) :
    (kapDecktFuel fuel bs = true ∧ kapGrundFuel fuel bs = none) ∨
      (kapDecktFuel fuel bs = false ∧
        ∃ g, kapGrundFuel fuel bs = some g) := by
  induction fuel generalizing bs with
  | zero =>
    cases bs with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons b bs' =>
      exact Or.inr ⟨rfl, ⟨.keinBrennstoff, rfl⟩⟩
  | succ n ih =>
    cases bs with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons b bs' =>
      cases hdec : kapDecode (b :: bs') with
      | none =>
        refine Or.inr ⟨?_, ⟨.keinDekoder, ?_⟩⟩
        · rw [kapDecktFuel_schritt, hdec]
        · rw [kapGrundFuel_schritt, hdec]
      | some pr =>
        obtain ⟨d, rest⟩ := pr
        by_cases hprog : rest.length < (b :: bs').length
        · cases ih rest with
          | inl hpos =>
            obtain ⟨hcov, hgrund⟩ := hpos
            refine Or.inl ⟨?_, ?_⟩
            · rw [kapDecktFuel_schritt, hdec]
              simp only [if_pos hprog, hcov]
            · rw [kapGrundFuel_schritt, hdec]
              simp only [if_pos hprog, hgrund]
          | inr hneg =>
            obtain ⟨hcov, g, hgrund⟩ := hneg
            refine Or.inr ⟨?_, ⟨g, ?_⟩⟩
            · rw [kapDecktFuel_schritt, hdec]
              simp only [if_pos hprog, hcov]
            · rw [kapGrundFuel_schritt, hdec]
              simp only [if_pos hprog, hgrund]
        · refine Or.inr ⟨?_, ⟨.keinFortschritt, ?_⟩⟩
          · rw [kapDecktFuel_schritt, hdec]
            simp only [if_neg hprog]
          · rw [kapGrundFuel_schritt, hdec]
            simp only [if_neg hprog]

/-! ## 4. Witnesses: LOCK+VEX covered, stray byte refused. -/

/-- Witness file: the LOCK XADD row then the VEX VPADDQ row. VEX is
    last: the accepted VEX decoder matches exact lists only, so a VEX
    row admits no trailing bytes. -/
def kapZeugeDatei : List Byte := kapW_lock ++ kapW_avx2

/-- Witness code section: 14 bytes, readable and executable, never
    writable, alignment 1 (divides every base). -/
def kapZeugeCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 14, vaddr := 0x1000, memLen := 14,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 1 }

/-- Witness image: LOCK row plus VEX row, entry at the code base. -/
def kapZeugeBild : Bild :=
  { datei := kapZeugeDatei
    abschnitte := [kapZeugeCode]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The witness image maps cleanly. -/
theorem kapZeuge_wohlgeformt :
    wohlgeformt .p48 kapZeugeBild = true := by
  decide

/-- ACCEPTANCE: the LOCK+VEX image is covered through the chain. -/
theorem kapZeuge_gedeckt : kapBildDeckt kapZeugeBild = true := by
  decide

/-- ACCEPTANCE: the LOCK+VEX image passes chain admission. -/
theorem kapZeuge_valKap : valKap .p48 kapZeugeBild = true := by
  decide

/-- Stray-byte image: one unsupported opcode byte (0x06: no chain
    row, cf. `decode_nichts_opcode_falsch` for the pilot). -/
def kapStreuBild : Bild :=
  { datei := [natByte 6]
    abschnitte :=
      [{ dateiOff := 0, dateiLen := 1, vaddr := 0x1000, memLen := 1,
         lesbar := true, schreibbar := false, ausfuehrbar := true,
         ausr := 1 }]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The stray image maps cleanly: the refusal below is a decode
    refusal, never a mapping refusal. -/
theorem kapStreu_wohlgeformt :
    wohlgeformt .p48 kapStreuBild = true := by
  decide

/-- Chain-level refusal matrix for the stray byte: every chain level
    refuses it (closed evaluations). -/
theorem kapStreu_breit_verweigert :
    decodeMulDivWidth [natByte 6] = none := by decide
theorem kapStreu_s32_verweigert :
    s32Decode [natByte 6] = none := by decide
theorem kapStreu_mxcsr_verweigert :
    mxcsrDecode [natByte 6] = none := by decide
theorem kapStreu_lock_verweigert :
    decodeLock [natByte 6] = none := by decide
theorem kapStreu_lockAdr_verweigert :
    decodeLockAdr [natByte 6] = none := by decide
theorem kapStreu_kompakt_verweigert :
    decodeC [natByte 6] = none := by decide
theorem kapStreu_kern_verweigert :
    decodeCore [natByte 6] = none := by decide
theorem kapStreu_avx2_verweigert :
    Avx2Join.dekodiereAvx2 [natByte 6] = none := by decide

/-- The chain refuses the stray byte (named levels above). -/
theorem kapStreu_kette : kapDecode [natByte 6] = none :=
  kapDecode_nichts _ kapStreu_breit_verweigert kapStreu_s32_verweigert
    kapStreu_mxcsr_verweigert kapStreu_lock_verweigert
    kapStreu_lockAdr_verweigert kapStreu_kompakt_verweigert
    kapStreu_kern_verweigert kapStreu_avx2_verweigert

/-- REFUSAL: the stray image fails chain admission. -/
theorem kapStreu_verweigert : valKap .p48 kapStreuBild = false := by
  decide

/-- REFUSAL with named reason: the stray walk stops at `keinDekoder`. -/
theorem kapStreu_grund :
    kapGrundFuel 2 [natByte 6] = some KapGrund.keinDekoder := by
  rw [kapGrundFuel_schritt, kapStreu_kette]

/-- JOINT WITNESS: LOCK+VEX covered and admitted, stray refused with
    its named reason. -/
theorem kapZeuge_gelenk :
    valKap .p48 kapZeugeBild = true ∧
      valKap .p48 kapStreuBild = false ∧
      kapBildDeckt kapZeugeBild = true ∧
      kapGrundFuel 2 [natByte 6] = some KapGrund.keinDekoder :=
  ⟨kapZeuge_valKap, kapStreu_verweigert, kapZeuge_gedeckt,
    kapStreu_grund⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    decoder lifted from `HwKapsteinDecoder`, never redefined; image
    mapping from `Bild`):
    - greedy fuel-bounded full decode `kapDecktFuel` through the
      capstone chain `kapDecode` (first match wins: the stated
      priority), with the row-returning traversal `kapKetteFuel`
      as its derivation;
    - soundness `valKap_deckung`: a covered byte list derives into
      chain rows with no remainder;
    - extension interface `KapErw`/`kapDecodeErw` (chain first, the
      new row only where the chain refuses;
      `kapDecodeErw_kanonisch`: no chain row is shadowed) with
      monotonicity `valKap_monoton`: adding a decoder row cannot
      turn a covered byte list into an uncovered one;
    - image admission `valKap` (checked mapping AND capstone-chain
      decode coverage of every executable section), with
      `valKap_wohlgeformt` and `valKap_deckt`;
    - named-refusal classification `kapGrund_klassifiziert`: every
      byte list either decodes through the chain or is refused with
      `keinDekoder`, `keinFortschritt` or `keinBrennstoff`;
    - witnesses: a LOCK XADD + VEX VPADDQ image covered and admitted
      (`kapZeuge_gedeckt`, `kapZeuge_valKap`); one stray opcode byte
      refused at every chain level (`kapStreu_kette`), at admission
      (`kapStreu_verweigert`), with its named reason
      (`kapStreu_grund`); joint witness `kapZeuge_gelenk`.
    NOT proved here, and not claimed:
    - `valX86_sound_full` stays OPEN: no claim is made that
      `valKap = true` implies any source correspondence, refinement,
      TSO/GX bridge, concurrency, contract, entry, budget, cost/time,
      FP, flag-undefinedness, or hardware behaviour. Admission is
      syntactic chain coverage plus the checked mapping, nothing more.
    - VEX rows admit no trailing bytes: the accepted `dekodiereAvx2`
      matches exact lists only, so coverage sees a VEX row at a
      section tail and a mid-section VEX row refuses with
      `keinDekoder`. Inherited limitation of the accepted decoder,
      documented not repaired.
    - No per-row consumed-length theorem: the walk guards progress
      (`keinFortschritt`) instead of proving every chain row consumes
      at least one byte; a zero-consuming chain row would refuse
      rather than loop, but its absence is not proved.
    - No chain-tie facts beyond `kapDecode`'s definition: priority
      (first match wins) is inherited from the accepted chain, not
      re-proved; overlap winners live in `HwKapsteinDecoder`.
    - No silicon re-check: encodings, fault classes and ordering
      rules are inherited unchanged from the accepted decoders; no
      new hardware fact is stated, Intel or AMD. Undefined or
      model-specific behaviour stays out of the model (rule 17).
    - No loader, entry-legality, relocation, control-flow, or
      patched-byte re-decode claim beyond section-byte coverage.
-/

#print axioms valKap_deckung
#print axioms kapDecodeErw_kanonisch
#print axioms valKap_monoton
#print axioms valKap_wohlgeformt
#print axioms valKap_deckt
#print axioms kapGrund_klassifiziert
#print axioms kapZeuge_wohlgeformt
#print axioms kapZeuge_gedeckt
#print axioms kapZeuge_valKap
#print axioms kapStreu_wohlgeformt
#print axioms kapStreu_kette
#print axioms kapStreu_verweigert
#print axioms kapStreu_grund
#print axioms kapZeuge_gelenk

end Gabbro.Grammatik.X86
