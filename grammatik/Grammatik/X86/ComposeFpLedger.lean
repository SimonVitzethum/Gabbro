/-
  File:      Grammatik/X86/ComposeFpLedger.lean
  Subject:   FP-ledger closing: every FP operation runs under its site ledger.

  Lane 839: compose the accepted FP producers (Gleitprofil ledger data,
  ScalarFloat step, ScalarFloatCodec fetched bytes, FpControlHardwareForms
  control-word change) into one checked closing step. The ledger entry of a
  scope is its admitted control word; a step runs only when the state word
  matches the ledger entry and the ledger admits it (RNE, masks, no FTZ/DAZ).
  Scope crossing refuses. Nothing here re-proves producer internals and no
  interpreter or executor is duplicated: all facts travel through the
  accepted definitions by name.
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.Gleitprofil
import Grammatik.X86.FpControlHardwareForms

namespace Gabbro.Grammatik.X86

/-- The control-state ledger of one scope: the admitted word every FP
    operation at this site runs under. The state word must equal it. -/
abbrev FpLedger := FPKontext

/-- Ledger-guarded single step: admit (RNE, masks, no FTZ/DAZ) AND scope
    match at entry, the accepted `fpSchritt`, then ledger still holds.
    `none` is an explicit refusal (bad ledger, scope crossing, or the
    accepted step's own refusal). -/
def fpLedgerSchritt (k : FpLedger) (d : FpDecodiert)
    (t : FpZustand) : Option FpZustand :=
  match fpEintritt t.fp with
  | false => none
  | true =>
    match decide (t.fp = k) with
    | false => none
    | true =>
      match fpSchritt d t with
      | none => none
      | some t' =>
        match decide (t'.fp = k) with
        | false => none
        | true => some t'

/-! ## 1. Ledger-step equations: what each guard refuses. -/

/-- A refused ledger word refuses every guarded form (RNE, masks,
    FTZ/DAZ checked at the site, never trusted from the caller). -/
theorem fpLedgerSchritt_ledger_verweigert (k : FpLedger)
    (d : FpDecodiert) (t : FpZustand)
    (h : fpEintritt t.fp = false) :
    fpLedgerSchritt k d t = none := by
  unfold fpLedgerSchritt
  simp [h]

/-- Scope crossing refuses: the state word is not this scope's ledger
    entry, although the ledger admits it. -/
theorem fpLedgerSchritt_kreuzung_verweigert (k : FpLedger)
    (d : FpDecodiert) (t : FpZustand)
    (hfp : fpEintritt t.fp = true) (hne : t.fp ≠ k) :
    fpLedgerSchritt k d t = none := by
  unfold fpLedgerSchritt
  simp [hfp, hne]

/-- Guarded success: admission, scope match, the accepted step,
    and the ledger still holding afterwards. -/
theorem fpLedgerSchritt_erfolg (k : FpLedger)
    (d : FpDecodiert) (t t' : FpZustand)
    (hfp : fpEintritt t.fp = true) (hled : t.fp = k)
    (hstep : fpSchritt d t = some t') (hbleibt : t'.fp = k) :
    fpLedgerSchritt k d t = some t' := by
  have e1 : decide (t.fp = k) = true := by simp [hled]
  have e2 : decide (t'.fp = k) = true := by simp [hbleibt]
  unfold fpLedgerSchritt
  simp [hfp, e1, hstep, e2]

/-- A guarded success runs the accepted `fpSchritt`: nothing is
    redefined here, the producer equation is reused by name. -/
theorem fpLedgerSchritt_schritt (k : FpLedger)
    (d : FpDecodiert) (t t' : FpZustand)
    (hout : fpLedgerSchritt k d t = some t') :
    fpSchritt d t = some t' := by
  unfold fpLedgerSchritt at hout
  cases he : fpEintritt t.fp with
  | false => simp [he] at hout
  | true =>
    simp only [he] at hout
    cases hd : decide (t.fp = k) with
    | false => simp [hd] at hout
    | true =>
      simp only [hd] at hout
      cases hs : fpSchritt d t with
      | none => simp [hs] at hout
      | some u =>
        simp only [hs] at hout
        cases hb : decide (u.fp = k) with
        | false => simp [hb] at hout
        | true =>
          simp only [hb] at hout
          exact hout

/-! ## 2. Byte-facing composition: fetched bytes under the ledger.

  Fetch reads actual executable memory through the accepted
  `fpFetchDekodiert` (never a caller-supplied decoded value); the
  decoded form then runs through the §1 ledger guard. -/

/-- One ledger-guarded byte step from actual memory: fetch, decode,
    then the §1 ledger step under the scope entry `k`. -/
def fpLedgerByteschritt (k : FpLedger) (t : FpZustand) : FpByteAusgang :=
  match fpFetchDekodiert t with
  | none => .verweigert
  | some (d, _) =>
    match fpLedgerSchritt k d t with
    | none => .verweigert
    | some t' => .weiter t'

/-- Fetch refusal is byte-step refusal. -/
theorem fpLedgerByteschritt_hol_verweigert (k : FpLedger)
    (t : FpZustand) (hf : fpFetchDekodiert t = none) :
    fpLedgerByteschritt k t = .verweigert := by
  unfold fpLedgerByteschritt
  rw [hf]

/-- A successful ledger byte-step runs the §1 ledger step on the
    fetched form. -/
theorem fpLedgerByteschritt_schritt (k : FpLedger)
    (t t' : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hout : fpLedgerByteschritt k t = .weiter t') :
    fpLedgerSchritt k d t = some t' := by
  unfold fpLedgerByteschritt at hout
  rw [hf] at hout
  simp only at hout
  cases hs : fpLedgerSchritt k d t with
  | none => simp [hs] at hout
  | some u =>
    simp only [hs] at hout
    have h2 : u = t' := by injection hout
    subst h2
    rfl

/-! ## 3. The closing connection.

  Producer/consumer interface closed here: input is the scope ledger
  entry `k` plus the fetched site (`fpFetchDekodiert` from actual
  bytes); output is the accepted `fpSchritt` successor with the ledger
  still holding. Every premise is used. -/

/-- The FP-ledger closing: a guarded byte step from actual bytes runs
    the accepted step on the fetched form, and the scope ledger still
    holds afterwards (admitted word, still this scope). -/
theorem ComposeFpLedger_verbindung (k : FpLedger)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (hfp : fpEintritt t.fp = true)
    (hledger : t.fp = k)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hout : fpLedgerByteschritt k t = .weiter t1) :
    fpSchritt d t = some t1 ∧ t1.fp = k ∧ fpEintritt t1.fp = true := by
  have hschritt : fpLedgerSchritt k d t = some t1 :=
    fpLedgerByteschritt_schritt k t t1 d rest hf hout
  have hst : fpSchritt d t = some t1 :=
    fpLedgerSchritt_schritt k d t t1 hschritt
  have e1 : decide (t.fp = k) = true := by simp [hledger]
  have hbleibt : t1.fp = k := by
    unfold fpLedgerSchritt at hschritt
    simp only [hfp, e1] at hschritt
    rw [hst] at hschritt
    simp only at hschritt
    cases hb : decide (t1.fp = k) with
    | false => simp [hb] at hschritt
    | true => exact of_decide_eq_true hb
  refine ⟨hst, hbleibt, ?_⟩
  rw [hbleibt, ← hledger]
  exact hfp

/-! ## 4. No contraction: one guarded step is exactly one model op.

  The guarded byte step applies a single `FpBefehl`: the arithmetic
  instance below pins exactly one `fpRechne` application (one rounding)
  for a fetched ADDSD -- no fused second op, no FMA contraction. -/

/-- No contraction through the ledger: a guarded ADDSD byte step
    computes exactly one model addition into the low half. -/
theorem ComposeFpLedger_keineKontraktion (k : FpLedger)
    (t t1 : FpZustand) (d : FpDecodiert) (rest : List Byte)
    (dst src : XmmReg)
    (hfp : fpEintritt t.fp = true)
    (hledger : t.fp = k)
    (hf : fpFetchDekodiert t = some (d, rest))
    (hform : d.befehl = .addsdRR dst src)
    (hout : fpLedgerByteschritt k t = .weiter t1) :
    xmmTief t1.xmm dst =
      fpRechne .add (xmmTief t.xmm dst) (xmmTief t.xmm src) := by
  have hok := (fpFetchDekodiert_erfolg t d rest hf).2.2.1
  have hconn := ComposeFpLedger_verbindung k t t1 d rest hfp hledger hf hout
  have heq := fpSchritt_addsdRR d t dst src hok hfp hform
  rw [hconn.1] at heq
  obtain rfl := Option.some_inj.mp heq
  exact xmmSchreibeTief_tief _ _ _

/-! ## 5. Planted refusals: one varied ledger leg each.

  Every refusal below varies exactly one leg of the admitted run and
  is decided on actual words, never trusted. -/

/-- FTZ word (bit 15): the ledger refuses, although fetch and scope
    match hold. -/
theorem ComposeFpLedgerNeg_ftz :
    fpLedgerSchritt kontextReset ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
      { fpCodecT with fp := (⟨0x9F80⟩ : FPKontext) } = none :=
  fpLedgerSchritt_ledger_verweigert _ _ _ (by decide)

/-- DAZ word (bit 6): the ledger refuses. -/
theorem ComposeFpLedgerNeg_daz :
    fpLedgerSchritt kontextReset ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
      { fpCodecT with fp := (⟨0x1FC0⟩ : FPKontext) } = none :=
  fpLedgerSchritt_ledger_verweigert _ _ _ (by decide)

/-- Round-down word (RC = 01): the RNE ledger leg refuses. -/
theorem ComposeFpLedgerNeg_runde :
    fpLedgerSchritt kontextReset ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
      { fpCodecT with fp := (⟨0x3F80⟩ : FPKontext) } = none :=
  fpLedgerSchritt_ledger_verweigert _ _ _ (by decide)

/-- Cleared precision mask: the mask ledger leg refuses. -/
theorem ComposeFpLedgerNeg_maske :
    fpLedgerSchritt kontextReset ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
      { fpCodecT with fp := (⟨0x0F80⟩ : FPKontext) } = none :=
  fpLedgerSchritt_ledger_verweigert _ _ _ (by decide)

/-- Scope crossing with an admitted word: sticky flags set (`0x1FBF`
    is admitted) but the word is not this scope's ledger entry. -/
theorem ComposeFpLedgerNeg_kreuzung :
    fpLedgerSchritt kontextReset ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
      { fpCodecT with fp := (⟨0x1FBF⟩ : FPKontext) } = none :=
  fpLedgerSchritt_kreuzung_verweigert _ _ _ (by decide) (by decide)

/-- Control change forces re-ledgering: the reached LDMXCSR load
    (`mxcsrWit_schritt1`) installs `0x1FBF` -- a real control change
    (`mxcsrWit_kontrolle_aendert`) -- so the old scope entry
    `kontextReset` no longer matches and the guarded step refuses. -/
theorem ComposeFpLedgerNeg_nachLaden :
    fpLedgerSchritt kontextReset ⟨.movsdSpeichere .rax .xmm0 0, 8⟩
      mxcsrWitT1 = none :=
  fpLedgerSchritt_kreuzung_verweigert _ _ _ mxcsrWit_eintritt (by decide)

/- CUTS: skeleton only; closing theorems follow.
-/

#print axioms fpEintritt_reset

end Gabbro.Grammatik.X86
