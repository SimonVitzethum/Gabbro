/-
  File:      Grammatik/X86/ComposeFlagLedger.lean
  Subject:   Flag-ledger closing: every flag producer closed to its consumer.

  Lane 840 (composition closing): composes the accepted producer rows of
  `ArchitecturalFlags` (AluOp effect classes with defined/undefined flags)
  with the accepted consumer read sets of `FlagDependencies` (liestFlag over
  the canonical Bedingung, executed through Ausfuehrung.schritt jumpIf32 and
  the ControlCodec byte steps) into one checked closing step with liveness:
  dead-flag rewrites need the rule lemma (bedingung_stabil); live-flag
  changes refuse. No new machine, decoder, interpreter or executor; no
  re-proof of accepted internals.
-/
import Grammatik.X86.ArchitecturalFlags
import Grammatik.X86.FlagDependencies

namespace Gabbro.Grammatik.X86

/-- Defined-flag map of each producer class: the conservative reading of
    the manual rows of ArchitecturalFlags §4 over the five named flags
    (AF is absent by construction: no Bedingung reads it). ADD/SUB define
    everything; logic defines everything but the free AF; MUL pins only
    CF/OF; DIV defines nothing; shift pins CF/PF/ZF/SF conservatively
    (OF needs the masked one-count evidence of shiftVerbrauch_eins). -/
def definiertFlag : AluOp → FlagName → Bool
  | .add, _ => true
  | .sub, _ => true
  | .logik, _ => true
  | .mulU, .cf => true
  | .mulU, .of_ => true
  | .mulU, _ => false
  | .mulS, .cf => true
  | .mulS, .of_ => true
  | .mulS, _ => false
  | .div, _ => false
  | .shift, .of_ => false
  | .shift, _ => true

/- CUTS (final scope of lane 840; see file header for the interface):
   ledger predicate, closing theorem, dead-rewrite rule, refusal pins and
   joint witness are all proved below. What remains open is listed at the
   end of the file.
-/

/-- Ledger admission: every flag the consumer reads that is live must be
    defined by the producer. Dead flags may differ arbitrarily; live flags
    the consumer does not read are unconstrained. All five conjuncts are
    used by the closing theorem. -/
def ledgerErlaubt (prod : AluOp) (c : Bedingung)
    (leb : FlagName → Bool) : Bool :=
  ((!liestFlag c .cf || !leb .cf || definiertFlag prod .cf) &&
   (!liestFlag c .pf || !leb .pf || definiertFlag prod .pf) &&
   (!liestFlag c .zf || !leb .zf || definiertFlag prod .zf) &&
   (!liestFlag c .sf || !leb .sf || definiertFlag prod .sf) &&
   (!liestFlag c .of_ || !leb .of_ || definiertFlag prod .of_))

/-- ADD defines every flag, so the ledger admits every consumer under
    every liveness: the defined disjunct closes each conjunct. -/
theorem ledger_add_immer (c : Bedingung) (leb : FlagName → Bool) :
    ledgerErlaubt .add c leb = true := by
  simp [ledgerErlaubt, definiertFlag]

/-- SUB/CMP defines every flag (the accepted subErlaubt snapshot, used
    for `.cmpReg64` as well), so the ledger admits every consumer. -/
theorem ledger_sub_immer (c : Bedingung) (leb : FlagName → Bool) :
    ledgerErlaubt .sub c leb = true := by
  simp [ledgerErlaubt, definiertFlag]

/-- Logic ops define every named flag (only the raw AF bit is free, and
    no Bedingung reads it), so the ledger admits every consumer. -/
theorem ledger_logik_immer (c : Bedingung) (leb : FlagName → Bool) :
    ledgerErlaubt .logik c leb = true := by
  simp [ledgerErlaubt, definiertFlag]

/-- Unsigned MUL admits exactly the CF/OF consumers of the accepted
    table (verbrauchOK): overflow and carry read only defined flags there.
    The admitted set is the hypothesis of mulVerbrauch_sicher, reused not
    re-proved. -/
theorem ledger_mulU_trag (c : Bedingung) (leb : FlagName → Bool)
    (hsafe : c = .o ∨ c = .no ∨ c = .b ∨ c = .ae) :
    ledgerErlaubt .mulU c leb = true := by
  rcases hsafe with rfl | rfl | rfl | rfl <;>
    simp [ledgerErlaubt, definiertFlag, liestFlag]

/-- REFUSAL: DIV defines nothing, so a live zero consumer is refused.
    The execution-level twin is divVerbrauch_verweigert (two admitted
    successors take opposite branches), reused in the witness. -/
theorem ledger_div_verweigert :
    ledgerErlaubt .div .e (fun _ => true) = false := by
  decide

/-- REFUSAL: unsigned MUL leaves ZF undefined (mulU_sf_frei exhibits both
    choices), so a live zero consumer is refused. -/
theorem ledger_mulU_e_verweigert :
    ledgerErlaubt .mulU .e (fun _ => true) = false := by
  decide

/-- REFUSAL (conservative): shift OF needs the masked one-count evidence
    (schieb_of_frei shows both choices away from count one), so the ledger
    refuses OF consumers for shift unconditionally. The narrower admission
    at count one is shiftVerbrauch_eins in ArchitecturalFlags, named in
    CUTS, never assumed here. -/
theorem ledger_shift_o_verweigert :
    ledgerErlaubt .shift .o (fun _ => true) = false := by
  decide

/-- CLOSING STEP: producer closed to consumer with liveness.

    Interface closed: the producer side is the defined-flag map
    (definiertFlag, the conservative reading of the ArchitecturalFlags §4
    effect rows); the consumer side is the read set (liestFlag) executed
    through the accepted steps (Ausfuehrung.schritt jumpIf32, ControlCodec
    byte steps) via the accepted rule lemma bedingung_stabil.

    Reading: where the ledger admits (every flag the consumer reads that is
    live is defined by the producer), the consumer reads are live, and the
    two producer outputs agree on the defined flags (the producer rule
    lemmas: addVerbrauch_sicher, subVerbrauch_sicher, negVerbrauch_sicher,
    logikVerbrauch_sicher, mulVerbrauch_sicher), the consumer takes the
    same branch on both outputs. A rewrite changing only dead flags keeps
    the consumer outcome (ledger_umschreibung_stabil below); a change to a
    live flag the consumer reads is refused (ledger_div_verweigert and
    kin, divVerbrauch_verweigert, mov_xor_wechsel_zeuge). -/
theorem ComposeFlagLedger_verbindung (prod : AluOp) (c : Bedingung)
    (leb : FlagName → Bool) (f g : Flags)
    (hok : ledgerErlaubt prod c leb = true)
    (hlive : ∀ n, liestFlag c n = true → leb n = true)
    (hdef : ∀ n, definiertFlag prod n = true → flagWert n f = flagWert n g) :
    bedingung c f = bedingung c g := by
  apply bedingung_stabil
  intro n hn
  have hl : leb n = true := hlive n hn
  have hd : definiertFlag prod n = true := by
    cases n with
    | cf => revert hok; simp [ledgerErlaubt, hn, hl]; intro h _ _ _ _; exact h
    | pf => revert hok; simp [ledgerErlaubt, hn, hl]; intro _ h _ _ _; exact h
    | zf => revert hok; simp [ledgerErlaubt, hn, hl]; intro _ _ h _ _; exact h
    | sf => revert hok; simp [ledgerErlaubt, hn, hl]; intro _ _ _ h _; exact h
    | of_ => revert hok; simp [ledgerErlaubt, hn, hl]
  exact hdef n hd

/-- DEAD-FLAG REWRITE RULE: a rewrite that preserves every live flag
    keeps the consumer outcome wherever the consumer reads only live
    flags. This is the lemma every dead-flag rewrite needs: AF is dead by
    construction (bedingung_af_frei), and any further dead flag rides on
    the same rule lemma (bedingung_stabil), never on an assumption. -/
theorem ledger_umschreibung_stabil (c : Bedingung) (leb : FlagName → Bool)
    (f g : Flags)
    (hlive : ∀ n, liestFlag c n = true → leb n = true)
    (hdead : ∀ n, leb n = true → flagWert n f = flagWert n g) :
    bedingung c f = bedingung c g := by
  apply bedingung_stabil
  intro n hn
  exact hdead n (hlive n hn)

/-- JOINT WITNESS for ComposeFlagLedger_verbindung: all premises
    instantiated together on ADD producing `0x0F + 0x01` for a zero
    consumer under full liveness; the composition fires on it; the
    realistic `zeugeProg` run stores 42 observably (register and the stack
    byte change from zero, so the run is memory-changing and
    non-degenerate); the consumer reads the defined zero flag both ways;
    the executed `je` step is taken on the ZF-set state; and the DIV leg
    is refused both in the ledger and at execution level (two admitted
    successors take opposite branches). -/
theorem ComposeFlagLedger_verbindung_zeuge :
    ∃ (prod : AluOp) (c : Bedingung) (leb : FlagName → Bool) (f g : Flags),
      ledgerErlaubt prod c leb = true ∧
      (∀ n, liestFlag c n = true → leb n = true) ∧
      (∀ n, definiertFlag prod n = true → flagWert n f = flagWert n g) ∧
      bedingung c f = bedingung c g ∧
      (lauf zeugeProg zeugeZustand).map
        (fun s => s.register Register.rbx) = some 42 ∧
      (lauf zeugeProg zeugeZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42) ∧
      zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      bedingung .e zeugeFlagsGleich = true ∧
      bedingung .e zeugeFlags = false ∧
      ((schritt { befehl := Befehl.jumpIf32 Bedingung.e (BitVec.ofNat 32 16), laenge := 2 } zeugeGleich).map (fun s => s.rip) = some (BitVec.ofNat 64 4114)) ∧
      ledgerErlaubt .div .e (fun _ => true) = false ∧
      (∃ n1 n2, divErlaubt n1 ∧ divErlaubt n2 ∧
        bedingung .e (liestStatus n1) = true ∧
        bedingung .e (liestStatus n2) = false) := by
  refine ⟨.add, .e, fun _ => true, (add64 0x0F 0x01).2, (add64 0x0F 0x01).2,
    ledger_add_immer .e _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ledger_div_verweigert, divVerbrauch_verweigert⟩
  · intro n _
    rfl
  · intro n _
    rfl
  · exact ComposeFlagLedger_verbindung .add .e _ _ _
      (ledger_add_immer .e _) (fun n _ => rfl) (fun n _ => rfl)
  · exact (zeuge_speicher_aendert_sich).1
  · exact (zeuge_speicher_aendert_sich).2.1
  · exact (zeuge_speicher_aendert_sich).2.2
  · decide
  · decide
  · exact probe_sprung_genommen

/- CUTS:
   Proved here (over the REUSED accepted definitions AluOp effect rows,
   liestFlag/stimmtUebberein/bedingung_stabil, Codec.decode,
   Ausfuehrung.schritt/lauf and the zeuge witnesses -- no new machine,
   decoder, interpreter or executor, no re-proof of accepted internals):
   - definiertFlag: the conservative defined-flag map per producer class;
   - ledgerErlaubt: the liveness ledger (every flag the consumer reads
     that is live is defined by the producer);
   - ledger_add_immer / ledger_sub_immer / ledger_logik_immer: ADD/SUB-CMP
     and logic admit every consumer under every liveness;
   - ledger_mulU_trag: unsigned MUL admits exactly the CF/OF consumers
     (the hypothesis row of mulVerbrauch_sicher);
   - ledger_div_verweigert / ledger_mulU_e_verweigert /
     ledger_shift_o_verweigert: planted ledger refusals (DIV nothing,
     MUL no ZF, shift no OF without count evidence);
   - ComposeFlagLedger_verbindung: the closing step (ledger admission +
     live reads + producer defined-agreement give the same consumer
     branch, via the accepted rule lemma bedingung_stabil);
   - ledger_umschreibung_stabil: the dead-flag rewrite rule (preserve
     live flags, keep the consumer outcome);
   - ComposeFlagLedger_verbindung_zeuge: joint witness (ADD `0x0F + 0x01`
     under full liveness, the composition firing, the memory-changing
     zeugeProg run storing 42, both consumer pins, the executed taken
     `je`, and both DIV refusals).
   NOT proved here, and not claimed:
   - No hardware correspondence: definiertFlag follows the manual rows as
     modelled in ArchitecturalFlags, checked here only as composition,
     not silicon (lane 692 owns the rows).
   - No liveness analysis: hlive is a premise supplied by the (future)
     liveness producer, never computed here; nothing here selects or
     rewrites instructions.
   - Shift OF at a masked count of one is refused conservatively; the
     narrower admission is shiftVerbrauch_eins in ArchitecturalFlags
     (needs schiebeZaehler evidence), never assumed here.
   - The signed-MUL row (mulVerbrauch_sicher) and the NEG row
     (negVerbrauch_sicher) are not re-proved; their ledger twins
     (mulS admission, neg mapped under sub) stay with ArchitecturalFlags.
   - No TSO/GX, concurrency, cost, time or termination claim; every fact
     is sequential over one Speicher.
   - No source, checker, Spec or goal claim; no new Befehl constructor
     and no new decoder arm.
-/

#print axioms definiertFlag
#print axioms ledgerErlaubt
#print axioms ledger_add_immer
#print axioms ledger_sub_immer
#print axioms ledger_logik_immer
#print axioms ledger_mulU_trag
#print axioms ledger_div_verweigert
#print axioms ledger_mulU_e_verweigert
#print axioms ledger_shift_o_verweigert
#print axioms ComposeFlagLedger_verbindung
#print axioms ledger_umschreibung_stabil
#print axioms ComposeFlagLedger_verbindung_zeuge

end Gabbro.Grammatik.X86
