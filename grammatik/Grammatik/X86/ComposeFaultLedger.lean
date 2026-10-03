/-
  File:      Grammatik/X86/ComposeFaultLedger.lean
  Subject:   Fault/refusal/stop-order closing across the whole image.

  Lane 842: compose already-accepted modules into one checked closing
  step over the REUSED canonical vocabulary (`valX86`,
  `extByteschritt`/`stepExt`/`decodeExt`, `klassifiziereExt`/`ArchFehler`,
  `stoppReihenfolge`/`beobachtung_stopp_sichtbar`). No new machine, no new
  decoder row, no new instruction, no source/checker/Spec/emitter change.
-/
import Grammatik.X86.HardwareFaults
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.BudgetExecution

namespace Gabbro.Grammatik.X86

/-- Ledger outcome: success carries the successor, halt carries its
    architectural fault class, refusal is explicit. -/
inductive LedgerOut where
  | weiter : FpZustand → LedgerOut
  | halt : ArchFehler → LedgerOut
  | verweigert : LedgerOut

/-- One ledger step: checked mapping AND decode coverage first, then the
    byte step from actual executable memory; the divide trap reports #DE,
    every refusal reports no fault. -/
def ledgerSchritt (p : Profil) (bild : Bild) (t : FpZustand)
    (b : BereitProfil) : LedgerOut :=
  match valX86 p bild with
  | false => .verweigert
  | true =>
    match extByteschritt t b with
    | .weiter t' => .weiter t'
    | .halt => .halt .de
    | .verweigert => .verweigert

/-- Refused mapping refuses the ledger. -/
theorem ledger_verweigert_bei_mapping (p : Profil) (bild : Bild)
    (t : FpZustand) (b : BereitProfil)
    (h : valX86 p bild = false) :
    ledgerSchritt p bild t b = .verweigert := by
  unfold ledgerSchritt
  rw [h]

/-- Halt leg: an admitted image with a trapping byte step reports #DE,
    through the reused classifier (halt IS #DE). -/
theorem ledger_halt_klasse (p : Profil) (bild : Bild)
    (t : FpZustand) (b : BereitProfil)
    (hval : valX86 p bild = true)
    (hhalt : extByteschritt t b = .halt) :
    ledgerSchritt p bild t b = .halt .de ∧
      klassifiziereExt (extByteschritt t b) = some .de := by
  have h1 : ledgerSchritt p bild t b = .halt .de := by
    unfold ledgerSchritt
    rw [hval, hhalt]
  refine ⟨h1, ?_⟩
  rw [hhalt]
  rfl

/-- Success leg: an admitted image with a continuing byte step continues
    with the same successor and reports no fault. -/
theorem ledger_weiter_ohne_fehler (p : Profil) (bild : Bild)
    (t t' : FpZustand) (b : BereitProfil)
    (hval : valX86 p bild = true)
    (hstep : extByteschritt t b = .weiter t') :
    ledgerSchritt p bild t b = .weiter t' ∧
      klassifiziereExt (extByteschritt t b) = none := by
  have h1 : ledgerSchritt p bild t b = .weiter t' := by
    unfold ledgerSchritt
    rw [hval, hstep]
  refine ⟨h1, ?_⟩
  rw [hstep]
  rfl

/-- Step-refusal leg: an admitted image with a refusing byte step refuses
    the ledger and reports no fault (refusal is not hardware). -/
theorem ledger_verweigert_bei_schritt (p : Profil) (bild : Bild)
    (t : FpZustand) (b : BereitProfil)
    (hval : valX86 p bild = true)
    (href : extByteschritt t b = .verweigert) :
    ledgerSchritt p bild t b = .verweigert ∧
      klassifiziereExt (extByteschritt t b) = none := by
  have h1 : ledgerSchritt p bild t b = .verweigert := by
    unfold ledgerSchritt
    rw [hval, href]
  refine ⟨h1, ?_⟩
  rw [href]
  rfl

/-- Two ledger steps in sequence; refusal or trap stops the run, so a
    refused or trapping head is never reordered behind later success. -/
def ledgerSchritt2 (p : Profil) (bild : Bild) (t : FpZustand)
    (b : BereitProfil) : LedgerOut :=
  match ledgerSchritt p bild t b with
  | .weiter t1 => ledgerSchritt p bild t1 b
  | x => x

/-- ORDER (head-first, fail-closed): a refusing head stops the two-step
    ledger; a trapping head stops it with the same #DE class. Both
    premises are used: the head equation selects the match arm. -/
theorem ledger_ordnung_kopf (p : Profil) (bild : Bild)
    (t : FpZustand) (b : BereitProfil)
    (h : ledgerSchritt p bild t b = .verweigert) :
    ledgerSchritt2 p bild t b = .verweigert := by
  unfold ledgerSchritt2
  rw [h]

/-- ORDER (trap head): a trapping head stops the two-step ledger with the
    same fault class; the trap is never reordered behind later success. -/
theorem ledger_ordnung_halt (p : Profil) (bild : Bild)
    (t : FpZustand) (b : BereitProfil) (k : ArchFehler)
    (h : ledgerSchritt p bild t b = .halt k) :
    ledgerSchritt2 p bild t b = .halt k := by
  unfold ledgerSchritt2
  rw [h]

/-- FAULTS NEVER OPTIMISED AWAY: every trapping division is impure
    (reused motion refusal), and the same division halts under a zero
    divisor yet answers under `17 / 5` (reused observable pair), so no
    motion/DCE may remove or hoist it silently. -/
theorem ledger_falle_nie_optimiert (src : Register) :
    rein (.divRax src) = false ∧ rein (.idivRax src) = false ∧
      istHalt (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = true ∧
        okWerte (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandDiv) =
          some (3, 2, false) := by
  obtain ⟨hdiv, hidiv⟩ := bewegung_verweigert_fuer_falle src
  obtain ⟨hhalt, hok⟩ := bewegen_aendert_beobachtung
  exact ⟨hdiv, hidiv, hhalt, hok⟩

/-- STOPS REPORTED BY KIND, ORDER PRESERVED: an over-budget head op names
    the source budget breach, a refused head form refuses the target
    aggregation (reused joint stopping order), and a byte-step refusal
    projects observably apart from success (reused projection), so no
    stop is silent and exhaustion is never reordered behind success. -/
theorem ledger_stopp_nach_art (bound left : Nat) (op : Op)
    (rest : List Op) (p : HardwareProfil) (d : Decodiert)
    (tl : List Decodiert) (V : Sichtbar) (s : Zustand)
    (hSrc : ¬ op.cost ≤ left)
    (hTgt : schrittKosten p d = none)
    (hBeob : beobAusgang V (byteschritt s) = .fehler) :
    (∃ needed, runOps bound left (op :: rest) =
      .budget "per_pass.ops" needed bound) ∧
      laufKosten p (d :: tl) = none ∧
      byteschritt s = .verweigert := by
  obtain ⟨hsrc, htgt⟩ :=
    stoppReihenfolge bound left op rest p d tl hSrc hTgt
  exact ⟨hsrc, htgt, beobachtung_stopp_sichtbar V s hBeob⟩

/-- CLOSING COMPOSITION (producer/consumer interface): the admitted image
    (`valX86`, consumer of `wohlgeformt` + decode coverage) feeds the byte
    step from actual executable memory (`extByteschritt`, producer of
    `weiter`/`halt`/`verweigert`); the fault classifier (`klassifiziereExt`)
    reports the kind; the two-step ledger (`ledgerSchritt2`) keeps the
    order; trapping divisions stay impure (motion/DCE refusal, producer
    `DecodeFault`). Every premise is used: `hval` + `hstep` give the
    ledger success and its class, `hstep` gives the sequencing, `src`
    gives the impurity pair. -/
theorem ComposeFaultLedger_verbindung (p : Profil) (bild : Bild)
    (t t' : FpZustand) (b : BereitProfil) (src : Register)
    (hval : valX86 p bild = true)
    (hstep : extByteschritt t b = .weiter t') :
    ledgerSchritt p bild t b = .weiter t' ∧
      klassifiziereExt (extByteschritt t b) = none ∧
      ledgerSchritt2 p bild t b = ledgerSchritt p bild t' b ∧
      rein (.divRax src) = false ∧ rein (.idivRax src) = false := by
  obtain ⟨hled, hklasse⟩ :=
    ledger_weiter_ohne_fehler p bild t t' b hval hstep
  obtain ⟨hdiv, hidiv⟩ := bewegung_verweigert_fuer_falle src
  refine ⟨hled, ?_, ?_, hdiv, hidiv⟩
  · exact hklasse
  · unfold ledgerSchritt2
    rw [hled]

/-- JOINT WITNESS: every premise of `ComposeFaultLedger_verbindung`
    holds jointly on concrete values -- the admitted minimal image with
    the reached one-step store run from actual bytes (cell 8192 moves
    observably from zero to 42) -- beside two planted refusals (mutated
    validator byte, truncated fetch) and the zero-divisor trap with its
    #DE class. Non-degenerate: a store-changing reached execution. -/
theorem ComposeFaultLedger_verbindung_zeuge :
    ∃ (p : Profil) (bild : Bild) (t t' : FpZustand) (b : BereitProfil)
      (src : Register),
      valX86 p bild = true ∧
      extByteschritt t b = .weiter t' ∧
      ledgerSchritt p bild t b = .weiter t' ∧
      klassifiziereExt (extByteschritt t b) = none ∧
      t.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      t'.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 42 ∧
      t.kern.speicher.bytes (BitVec.ofNat 64 8192) ≠
        t'.kern.speicher.bytes (BitVec.ofNat 64 8192) ∧
      valX86 .p48 { valZeuge with datei := [natByte 0] } = false ∧
      extByteschritt (einByteStart (natByte 233)) extWitBereit =
        .verweigert ∧
      mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull = .hardwareHalt ∧
      klassifiziereMulDiv
        (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = some .de ∧
      rein (.divRax src) = false ∧ rein (.idivRax src) = false := by
  have hcell : extZelle (extByteschritt extWitStart extWitBereit)
      (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) :=
    extWit_erster_speichert
  cases h : extByteschritt extWitStart extWitBereit with
  | weiter t1 =>
    have hcell2 : extZelle (.weiter t1 : ExtAusgang)
        (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) := by
      rw [← h]
      exact extWit_erster_speichert
    have hsome : some (t1.kern.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42) := by
      simpa [extZelle] using hcell2
    have h42 : t1.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 42 :=
      Option.some_inj.mp hsome
    have hnull : extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 :=
      extWit_anfang_null.1
    have hdiff : extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) ≠
        t1.kern.speicher.bytes (BitVec.ofNat 64 8192) := by
      rw [hnull, h42]
      decide
    have hhalt := fehler_div_null_haelt_zeuge.1
    have hde : klassifiziereMulDiv
        (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = some .de := by
      simp [klassifiziereMulDiv, hhalt]
    obtain ⟨hdiv, hidiv⟩ := bewegung_verweigert_fuer_falle Register.rcx
    obtain ⟨hled, hklasse, _, _, _⟩ :=
      ComposeFaultLedger_verbindung .p48 valZeuge extWitStart t1
        extWitBereit .rcx valZeuge_akzeptiert h
    exact ⟨.p48, valZeuge, extWitStart, t1, extWitBereit, .rcx,
      valZeuge_akzeptiert, h, hled, hklasse, hnull, h42, hdiff,
      valZeuge_mutiert_verweigert, fetch_abgeschnitten_verweigert,
      hhalt, hde, hdiv, hidiv⟩
  | halt =>
    rw [h] at hcell
    simp [extZelle] at hcell
  | verweigert =>
    rw [h] at hcell
    simp [extZelle] at hcell

/- CUTS:
   Proved here, over the REUSED canonical vocabulary only (no new
   machine, no new decoder row, no new instruction, no source claim):
   - one ledger step (`ledgerSchritt`: admitted mapping AND decode
     coverage first, then the byte step from actual executable memory;
     the divide trap reports #DE, every refusal reports no fault) with
     its four legs (`ledger_verweigert_bei_mapping`,
     `ledger_halt_klasse`, `ledger_weiter_ohne_fehler`,
     `ledger_verweigert_bei_schritt`, all through the reused
     `klassifiziereExt` equations);
   - stop order (`ledgerSchritt2` with `ledger_ordnung_kopf` and
     `ledger_ordnung_halt`: a refusing or trapping head stops the run,
     never reordered behind later success) and stops reported by kind
     (`ledger_stopp_nach_art`: reused joint source/target stopping
     order plus the observably distinct byte-step refusal projection);
   - faults never optimised away (`ledger_falle_nie_optimiert`: reused
     motion refusal plus the concrete observable halt/answer pair);
   - the closing composition (`ComposeFaultLedger_verbindung`: admitted
     image plus one byte step give the ledger success, its no-fault
     class, the two-step sequencing and the impurity pair) with its
     joint witness (`ComposeFaultLedger_verbindung_zeuge`: reached
     one-step store run moving cell 8192 observably from zero to 42,
     two planted refusals, the zero-divisor trap with its #DE class).
   NOT proved here, and not claimed:
   - No fault PRIORITY between pending classes and no #UD/#XM/#AC/#NM
     membership beyond the reused classifier: priority, paging
     disambiguation and delivery stay with lanes 670/672 (see
     `HardwareFaults` CUTS).
   - No whole-image soundness (`valX86_sound`): no claim that an
     admitted image is the emitted form of any source program; no
     source correspondence, no TSO/GX bridge, no concurrency, contract,
     budget-transfer, cost/time or FP claim beyond the reused legs.
   - No new target semantics: the one `extByteschritt`, the one
     `valX86` and the one `klassifiziereExt` are reused untouched; no
     duplicated evaluator, decoder or cost model.
   - No checker/source/Spec/goal/emitter change; no new diagnostic,
     gift, example or CLI numbers; no MARKE_EMIT change.
-/

#print axioms ledgerSchritt
#print axioms ledgerSchritt2
#print axioms ledger_verweigert_bei_mapping
#print axioms ledger_halt_klasse
#print axioms ledger_weiter_ohne_fehler
#print axioms ledger_verweigert_bei_schritt
#print axioms ledger_ordnung_kopf
#print axioms ledger_ordnung_halt
#print axioms ledger_falle_nie_optimiert
#print axioms ledger_stopp_nach_art
#print axioms ComposeFaultLedger_verbindung
#print axioms ComposeFaultLedger_verbindung_zeuge

end Gabbro.Grammatik.X86
