/-
  File:      Grammatik/X86/ComposeWidthLedger.lean
  Subject:   Width-ledger closing: every width conversion to its exactness lemma.

  Lane 841: skeleton only. Composes accepted NarrowOps/NarrowCodec rows over
  the canonical Wort/Speicher/Ausfuehrung vocabulary. No new machine.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.NarrowOps
import Grammatik.X86.NarrowCodec

namespace Gabbro.Grammatik.X86

/-- Width conversion ledger: every known conversion names its width;
    unknown widths carry a code and fall back loudly (`none`). -/
inductive WidthConv where
  | zeroExt (b : Breite)
  | signExt (b : Breite)
  | truncTo (b : Breite)
  | mergeTo (b : Breite)
  | unknown (code : Nat)
  deriving DecidableEq, Repr

/-- Ledger application reusing the canonical `trunc`/`sext` and the
    accepted `mergeRegNarrow`. Unknown widths answer `none`. -/
def convApply (c : WidthConv) (oldVal newVal : Wort) : Option Wort :=
  match c with
  | .zeroExt b => some (trunc b newVal)
  | .signExt b => some (sext b newVal)
  | .truncTo b => some (trunc b newVal)
  | .mergeTo b => some (mergeRegNarrow b oldVal newVal)
  | .unknown _ => none

/-- Ledger admission: known conversions are admitted, unknown widths
    refuse loudly (no silent default extension). -/
def ledgerAdmitted (c : WidthConv) : Bool :=
  match c with
  | .unknown _ => false
  | _ => true

/-- Unknown signedness keeps the loud narrow guard (reused by name). -/
def convNeedsGuard (c : WidthConv) : Bool :=
  match c with
  | .unknown _ => true
  | _ => false

/-- Unknown widths answer `none`: no value is invented. -/
theorem convApply_unknown (code : Nat) (oldVal newVal : Wort) :
    convApply (.unknown code) oldVal newVal = none := rfl

/-- Unknown widths are refused admission. -/
theorem ledger_unknown_verweigert (code : Nat) :
    ledgerAdmitted (.unknown code) = false := rfl

/-- Unknown widths demand the loud guard. -/
theorem convNeedsGuard_unknown (code : Nat) :
    convNeedsGuard (.unknown code) = true := rfl

/-- Known conversions are admitted (zero-extension row). -/
theorem ledger_zero_admitted (b : Breite) :
    ledgerAdmitted (.zeroExt b) = true := rfl

/-! ## Exactness: every ledger row is its accepted lemma. -/

/-- Zero extension is truncation (reuses `extendNarrow_zero`). -/
theorem convApply_zero_exact (b : Breite) (oldVal newVal : Wort) :
    convApply (.zeroExt b) oldVal newVal =
      some (extendNarrow .zero b newVal) := by
  simp [convApply, extendNarrow_zero]

/-- Sign extension reuses the canonical `sext`
    (reuses `extendNarrow_sign`). -/
theorem convApply_sign_exact (b : Breite) (oldVal newVal : Wort) :
    convApply (.signExt b) oldVal newVal =
      some (extendNarrow .sign b newVal) := by
  simp [convApply, extendNarrow_sign]

/-- Truncation rows carry exactly the low bits. -/
theorem convApply_trunc_exact (b : Breite) (oldVal newVal : Wort) :
    convApply (.truncTo b) oldVal newVal = some (trunc b newVal) := rfl

/-- Merge rows are the accepted architectural merge. -/
theorem convApply_merge_exact (b : Breite) (oldVal newVal : Wort) :
    convApply (.mergeTo b) oldVal newVal =
      some (mergeRegNarrow b oldVal newVal) := rfl

/-- No truncation lie at 64 bits: the merge is the full word
    (reuses `mergeRegNarrow_b64`). -/
theorem convApply_merge_b64 (oldVal newVal : Wort) :
    convApply (.mergeTo .b64) oldVal newVal = some newVal := by
  simp [convApply, mergeRegNarrow_b64]

/-- 32-bit merges clear the upper half by construction
    (reuses `mergeRegNarrow_b32`). -/
theorem convApply_merge_b32 (oldVal newVal : Wort) :
    convApply (.mergeTo .b32) oldVal newVal =
      some (trunc .b32 newVal) := by
  simp [convApply, mergeRegNarrow_b32]

/-- Zero extension at full width is the identity: no truncation lie
    (reuses `trunc_b64`). -/
theorem convApply_zero_b64 (oldVal newVal : Wort) :
    convApply (.zeroExt .b64) oldVal newVal = some newVal := by
  simp [convApply, trunc_b64]

/-! ## Closing connection: decoded narrow steps land in the ledger.

    Producer: the accepted `NarrowCodec` decoder coverage shape
    (`narrowDecktAb`, proved decoder-side) with the checked length,
    executed by the accepted `stepNarrow` on the same `Zustand`.
    Consumer: this ledger (`convApply`) with its exactness lemmas
    above. The theorem covers all four accepted rows generically over
    arbitrary admitted inputs: every register result is the accepted
    merge of the accepted extension, every store carries exactly the
    truncated word, and every ledger application on the step equals
    its `some` exactness value (never `none`, never a second
    evaluator). -/

/-- WIDTH-LEDGER CLOSING: every admitted decoded narrow step lands in
    the ledger at its exactness value. The 32-bit move lands the
    architectural merge (which is the truncation); both extensions
    land the source-extended merge with the source conversion exact;
    the store carries exactly the truncated word into the canonical
    width-indexed write. Flags follow the MOV discipline and RIP
    advances past the decoded length. -/
theorem ComposeWidthLedger_verbindung (d : NarrowDec) (s s' : Zustand)
    (hok : laengeOk d.laenge = true)
    (hdeck : narrowDecktAb d)
    (hstep : stepNarrow d s = some s') :
    (∃ dst src, d.op = .mov32rr dst src ∧
      s'.register dst = mergeRegNarrow .b32 (s.register dst) (s.register src) ∧
      convApply (.mergeTo .b32) (s.register dst) (s.register src) =
        some (s'.register dst) ∧
      s'.register dst = trunc .b32 (s.register src) ∧
      s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge) ∨
    (∃ dst src, d.op = .movzx8 dst src ∧
      s'.register dst = mergeRegNarrow .b32 (s.register dst)
        (extendNarrow .zero .b8 (s.register src)) ∧
      convApply (.zeroExt .b8) 0 (s.register src) =
        some (trunc .b8 (s.register src)) ∧
      convApply (.mergeTo .b32) (s.register dst)
        (extendNarrow .zero .b8 (s.register src)) = some (s'.register dst) ∧
      s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge) ∨
    (∃ dst src, d.op = .movsx8 dst src ∧
      s'.register dst = mergeRegNarrow .b32 (s.register dst)
        (extendNarrow .sign .b8 (s.register src)) ∧
      convApply (.signExt .b8) 0 (s.register src) =
        some (sext .b8 (s.register src)) ∧
      convApply (.mergeTo .b32) (s.register dst)
        (extendNarrow .sign .b8 (s.register src)) = some (s'.register dst) ∧
      s'.flags = s.flags ∧ s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip d.laenge) ∨
    (∃ base src disp m, d.op = .store32 base src disp ∧
      writeBreite s.speicher .b32 (effAddr s base disp)
        (trunc .b32 (s.register src)) = some m ∧
      convApply (.truncTo .b32) 0 (s.register src) =
        some (trunc .b32 (s.register src)) ∧
      s'.speicher = m ∧ s'.flags = s.flags ∧
      s'.rip = ripNach s.rip d.laenge) := by
  rcases hdeck with ⟨dst, src, hop, -⟩ | ⟨dst, src, hop, -⟩ |
    ⟨dst, src, hop, -⟩ | ⟨base, src, disp, hop, -⟩
  · have hst := stepNarrow_mov32_rahmen d s s' dst src hok hop hstep
    obtain ⟨hreg, hfl, hmem, hrip⟩ := hst
    exact Or.inl ⟨dst, src, hop, hreg,
      by rw [convApply_merge_exact, hreg],
      by rw [hreg, mergeRegNarrow_b32], hfl, hmem, hrip⟩
  · have hst := stepNarrow_movzx8_rahmen d s s' dst src hok hop hstep
    obtain ⟨hreg, hfl, hmem, hrip⟩ := hst
    exact Or.inr (Or.inl ⟨dst, src, hop, hreg, rfl,
      by rw [convApply_merge_exact, hreg], hfl, hmem, hrip⟩)
  · have hst := stepNarrow_movsx8_rahmen d s s' dst src hok hop hstep
    obtain ⟨hreg, hfl, hmem, hrip⟩ := hst
    exact Or.inr (Or.inr (Or.inl ⟨dst, src, hop, hreg, rfl,
      by rw [convApply_merge_exact, hreg], hfl, hmem, hrip⟩))
  · obtain ⟨m, hwr⟩ :
        ∃ m, writeBreite s.speicher .b32 (effAddr s base disp)
          (trunc .b32 (s.register src)) = some m := by
      cases hwr : writeBreite s.speicher .b32 (effAddr s base disp)
        (trunc .b32 (s.register src)) with
      | none =>
        have hnone : storeNarrow s .b32 (effAddr s base disp) src = none :=
          storeNarrow_refused _ _ _ _ hwr
        have hcontra :=
          stepNarrow_store_verweigert d s base src disp hok hop hnone
        rw [hcontra] at hstep
        cases hstep
      | some m => exact ⟨m, rfl⟩
    have hsn := storeNarrow_success s .b32 (effAddr s base disp) src m hwr
    have hst := stepNarrow_store_erfolg d s base src disp m hok hop hsn
    rw [hst] at hstep
    cases hstep
    exact Or.inr (Or.inr (Or.inr ⟨base, src, disp, m, hop, hwr, rfl,
      rfl, rfl, rfl⟩))

/-! ## Pinned ledger values and planted refusals. -/

/-- Pinned zero extension: `0xFF` stays `0xFF`. -/
theorem pin_conv_zero :
    convApply (.zeroExt .b8) 0 0xFF = some 0xFF := by
  decide

/-- Pinned sign extension: `0x80` fills to `0xFFFFFF80`. -/
theorem pin_conv_sign :
    convApply (.signExt .b8) 0 0x80 = some 0xFFFFFFFFFFFFFF80 := by
  decide

/-- Pinned 32-bit merge: over an all-ones destination the low byte
    `0x80` lands with the upper half cleared (no truncation lie). -/
theorem pin_conv_merge32 :
    convApply (.mergeTo .b32) 0xFFFFFFFFFFFFFFFF 0x80 =
      some 0x80 := by
  decide

/-- PLANTED REFUSAL (ledger): the unknown width `7` has no value. -/
theorem pin_conv_unknown :
    convApply (.unknown 7) 0 0 = none := by
  decide

/-- PLANTED REFUSAL (ledger admission): the unknown width `7` is
    refused admission. -/
theorem pin_ledger_unknown_admission :
    ledgerAdmitted (.unknown 7) = false := rfl

/-! ## Joint witness: reached memory-changing run plus refusals. -/

/-- JOINT WITNESS for `ComposeWidthLedger_verbindung`: the decoded
    32-bit store through the accepted witness state reaches a
    successor (checked length, coverage shape and step premises hold
    jointly), the store observably changes memory (data cell `8192`
    goes `0 -> 4`, so the run is non-degenerate and memory-changing),
    the ledger truncation on the step is exact, the unknown width has
    no value, and both planted step refusals (bad length, denied
    permission) hold. -/
theorem ComposeWidthLedger_verbindung_zeuge :
    ∃ (d : NarrowDec) (s s' : Zustand),
      laengeOk d.laenge = true ∧ narrowDecktAb d ∧
      stepNarrow d s = some s' ∧
      s'.speicher.bytes (BitVec.ofNat 64 8192) ≠
        s.speicher.bytes (BitVec.ofNat 64 8192) ∧
      convApply (.truncTo .b32) 0 (s.register .rax) =
        some (trunc .b32 (s.register .rax)) ∧
      convApply (.unknown 7) 0 0 = none ∧
      stepNarrow ⟨.mov32rr .rax .rcx, 0⟩ narrowWitExtState = none ∧
      stepNarrow ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩
        narrowWitKeinSchreib = none := by
  have hsome := narrow_store_witness.1
  have hne : stepNarrow
      ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩ narrowWitState ≠ none := by
    intro hcon
    rw [hcon] at hsome
    simp at hsome
  obtain ⟨s', hs'⟩ :
      ∃ s', stepNarrow
        ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩
        narrowWitState = some s' := by
    cases hst : stepNarrow
      ⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩ narrowWitState with
    | none => exact absurd hst hne
    | some s' => exact ⟨s', rfl⟩
  have hbyte : s'.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 4 := by
    simpa [hs'] using hsome
  have hpre := narrow_store_witness.2.2
  have hdiff : s'.speicher.bytes (BitVec.ofNat 64 8192) ≠
      narrowWitState.speicher.bytes (BitVec.ofNat 64 8192) := by
    rw [hbyte, hpre]
    decide
  refine ⟨⟨.store32 .rbx .rax (BitVec.ofNat 32 0), 7⟩, narrowWitState, s',
    by decide, ?_, hs', hdiff, rfl, pin_conv_unknown,
    narrow_schritt_laenge_null, narrow_schritt_speicher_verweigert⟩
  exact Or.inr (Or.inr (Or.inr
    ⟨.rbx, .rax, (BitVec.ofNat 32 0), rfl, Or.inl rfl⟩))

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Typen` Breite/Register,
   `Wort.trunc`/`sext`/`trunc_b64`, `NarrowOps.mergeRegNarrow`/`extendNarrow`/
   `mergeRegNarrow_b64`/`mergeRegNarrow_b32`/`extendNarrow_zero`/`extendNarrow_sign`/
   `storeNarrow`/`storeNarrow_success`/`storeNarrow_refused`,
   `NarrowCodec.NarrowDec`/`narrowDecktAb`/`stepNarrow`/
   `stepNarrow_mov32_rahmen`/`stepNarrow_movzx8_rahmen`/
   `stepNarrow_movsx8_rahmen`/`stepNarrow_store_erfolg`/
   `stepNarrow_store_verweigert`/`narrow_store_witness`/
   `narrow_schritt_laenge_null`/`narrow_schritt_speicher_verweigert`,
   `Ausfuehrung.laengeOk`/`ripNach`/`effAddr`, `Speicher.writeBreite`): the
   width ledger (`WidthConv`/`convApply`/`ledgerAdmitted`/`convNeedsGuard`)
   with every known row closed to its exactness lemma (zero is truncation,
   sign is the canonical sext, merge is the accepted architectural merge;
   64-bit identity and 32-bit clearing, so no truncation lie), unknown
   widths answering `none` with refused admission and a loud guard, the
   closing connection `ComposeWidthLedger_verbindung` over all four
   accepted narrow rows generically (register results are the accepted
   merge of the accepted extension, stores carry exactly the truncated
   word, flags MOV-preserved, RIP advanced past the decoded length),
   pinned values, planted ledger/step refusals, and the joint
   non-degenerate memory-changing witness
   `ComposeWidthLedger_verbindung_zeuge`.
   NOT proved here, and not claimed:
   - No new decoder, encoder, execution or memory fact: every step,
     memory, flag and coverage lemma is reused by name from
     NarrowOps/NarrowCodec; nothing here re-proves their internals and
     no second evaluator or interpreter is duplicated.
   - No 16-bit extension rows (opcodes 183/191 refuse in NarrowCodec,
     lane 562, OPEN), no narrow loads, no narrow ALU flag snapshots
     (MOV discipline only, see NarrowOps CUTS).
   - No fetch wiring: `Byteschritt` still fetches with the pilot decode
     only (see NarrowCodec CUTS).
   - No TSO/GX bridge, no source correspondence, no ABI/image, entry,
     relocation, cost, termination or timing claim; `none`/`false` is
     the absence of a transition or admission, never a halt claim.
   - No hardware verification: masks, extensions and admission are
     STATED executable semantics, not verified against silicon.
   - Missing producer legs are owned elsewhere: wider integer/scalar-FP
     row coverage by lanes 562-566, fetched execution by lane 567-569,
     source-memory representation by lane 570; none is assumed here.
-/

#print axioms convApply_unknown
#print axioms ledger_unknown_verweigert
#print axioms convNeedsGuard_unknown
#print axioms ledger_zero_admitted
#print axioms convApply_zero_exact
#print axioms convApply_sign_exact
#print axioms convApply_trunc_exact
#print axioms convApply_merge_exact
#print axioms convApply_merge_b64
#print axioms convApply_merge_b32
#print axioms convApply_zero_b64
#print axioms ComposeWidthLedger_verbindung
#print axioms pin_conv_zero
#print axioms pin_conv_sign
#print axioms pin_conv_merge32
#print axioms pin_conv_unknown
#print axioms pin_ledger_unknown_admission
#print axioms ComposeWidthLedger_verbindung_zeuge

end Gabbro.Grammatik.X86
