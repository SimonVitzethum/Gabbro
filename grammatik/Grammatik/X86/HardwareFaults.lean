/-
  File:      Grammatik/X86/HardwareFaults.lean
  Subject:   Precise admitted-profile architectural fault classification.

  Lane 670: architectural fault classes (#DE/#UD/#GP/#SS/#PF/#AC/#NM/#XM)
  over the accepted byte-facing dispatcher (`ExtendedExecution.stepExt` /
  `extByteschritt`), the accepted divide trap (`MulDiv.mulDivSchritt`) and
  the accepted permission-checked memory (`Speicher.read64`/`write64`).
  Validator refusal (`Option.none` / `ExtAusgang.verweigert`) is never a
  fault by construction. Fault delivery (stack/handler) stays with lane
  672; no handler call is modelled here.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  - exception vectors Table 6-1, Intel SDM Vol. 1 Ch. 6 (txt lines 9641-9671):
    #DE vec 0 DIV/IDIV, #UD vec 6, #GP vec 13, #PF vec 14, #AC vec 17,
    #XM vec 19, #NM vec 7, #SS vec 12.
  - canonical addressing, Vol. 1 §3.3.7.1 (txt line 4220): bits 63..48 must
    match bit 47; other linear references raise #GP, stack references #SS.
  - DIV entry (txt line 31795) and IDIV entry (txt line 31887): zero divisor
    or unrepresentable quotient traps as #DE; destinations are undefined.
-/
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.DecodeFault
import Grammatik.X86.OverlapRefusal

namespace Gabbro.Grammatik.X86

/-- Architectural fault class: the admitted-profile subset of Table 6-1.
    A value of this type is a hardware behaviour, never a validator
    verdict: `Option.none` / `ExtAusgang.verweigert` map to `none`. -/
inductive ArchFehler where
  | de
  | ud
  | gp
  | ss
  | pf
  | ac
  | nm
  | xm
  deriving DecidableEq, Repr

/-- The divide trap IS #DE: the accepted halt maps to its class. -/
def klassifiziereMulDiv : MulDivErgebnis → Option ArchFehler
  | .hardwareHalt => some .de
  | _ => none

/-- Halt classifies as #DE. -/
theorem halt_ist_de : klassifiziereMulDiv .hardwareHalt = some .de := rfl

/-- A successful divide step is no fault. -/
theorem ok_kein_fehler (s : Zustand) :
    klassifiziereMulDiv (.ok s) = none := rfl

/-- Decode-length refusal is no fault: validator verdict, not hardware. -/
theorem misslungen_kein_fehler :
    klassifiziereMulDiv .misslungen = none := rfl

/-- Unified-outcome classifier for the 660 consumer: the divide trap IS
    #DE; success and explicit refusal are no fault. -/
def klassifiziereExt : ExtAusgang → Option ArchFehler
  | .halt => some .de
  | _ => none

/-- The 660 adapter entry point: same classifier under its consumer name. -/
def adapter660_klasse : ExtAusgang → Option ArchFehler := klassifiziereExt

/-- Adapter soundness on the trap: 660 sees #DE for the halt. -/
theorem adapter660_halt (o : ExtAusgang) (h : o = .halt) :
    adapter660_klasse o = some .de := by
  simp [adapter660_klasse, klassifiziereExt, h]

/-- Adapter soundness on refusal: 660 never reads a fault from refusal. -/
theorem adapter660_verweigert_kein_fehler :
    adapter660_klasse .verweigert = none := rfl

/-- Adapter soundness on success: no fault where execution continued. -/
theorem adapter660_weiter_kein_fehler (t : FpZustand) :
    adapter660_klasse (.weiter t) = none := rfl

/-! ## Canonical addresses (§3.3.7.1): #SS for stack references, #GP else. -/

/-- Canonical address at the implemented 48-bit width: low half below
    `2 ^ 47`, high half at or above `2 ^ 64 - 2 ^ 47`. -/
def istKanonisch (a : Adresse) : Bool :=
  decide (a.toNat < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ a.toNat)

/-- Canonical-address fault class: noncanonical stack references fault
    as #SS, all other noncanonical linear references as #GP. Canonical
    addresses carry no fault. -/
def adrKlasse (a : Adresse) (istStapel : Bool) : Option ArchFehler :=
  if istKanonisch a then none
  else if istStapel then some .ss else some .gp

/-- Address zero is canonical. -/
theorem kanonisch_null : istKanonisch 0 = true := by decide

/-- The witness data cell 8192 is canonical. -/
theorem kanonisch_daten : istKanonisch (BitVec.ofNat 64 8192) = true := by
  decide

/-- The witness code base 4096 is canonical. -/
theorem kanonisch_code : istKanonisch (BitVec.ofNat 64 4096) = true := by
  decide

/-- Bit 47 alone set is the first noncanonical address. -/
theorem nichtkanonisch_bit47 :
    istKanonisch (BitVec.ofNat 64 (2 ^ 47)) = false := by
  decide

/-- A noncanonical data reference faults as #GP. -/
theorem adrKlasse_daten_gp :
    adrKlasse (BitVec.ofNat 64 (2 ^ 47)) false = some .gp := by
  decide

/-- The same noncanonical address through a stack register faults as #SS. -/
theorem adrKlasse_stapel_ss :
    adrKlasse (BitVec.ofNat 64 (2 ^ 47)) true = some .ss := by
  decide

/-- A canonical address carries no fault on either path. -/
theorem adrKlasse_kanonisch_kein_fehler (a : Adresse)
    (h : istKanonisch a = true) (stapel : Bool) :
    adrKlasse a stapel = none := by
  simp [adrKlasse, h]

/-! ## Data-memory faults: #GP vs #PF is explicit nondeterminism.

  The canonical `Speicher` has permission fields but no paging
  structure, so a faulting data access cannot decide between #GP and
  #PF from model state alone. The classifier therefore answers the
  permitted SET: `#SS/#PF` for stack references, `#GP/#PF` else.
  A single pinned member (`.pf`) is the executable witness; the set
  membership is what the consumer may rely on. -/

/-- Permitted data-fault classes: stack references may fault as #SS,
    all other data references as #GP; either may fault as #PF. -/
def datenFehlerKlassen : Bool → List ArchFehler
  | true => [.ss, .pf]
  | false => [.gp, .pf]

/-- Data-read classifier on the real check: success is no fault, a
    refused `read64` is observed as #PF (one permitted member). -/
def leseKlasse (m : Speicher) (a : Adresse) : Option ArchFehler :=
  match read64 m a with
  | some _ => none
  | none => some .pf

/-- Data-write classifier on the real check: success is no fault, a
    refused `write64` is observed as #PF (one permitted member). -/
def schreibKlasse (m : Speicher) (a : Adresse) (v : Wort) :
    Option ArchFehler :=
  match write64 m a v with
  | some _ => none
  | none => some .pf

/-- A faulting read observes a permitted class. -/
theorem leseFehler_in_klassen (m : Speicher) (a : Adresse)
    (stapel : Bool) (h : read64 m a = none) :
    ∃ k ∈ datenFehlerKlassen stapel, leseKlasse m a = some k := by
  cases stapel with
  | true =>
    exact ⟨.pf, by decide, by simp [leseKlasse, h]⟩
  | false =>
    exact ⟨.pf, by decide, by simp [leseKlasse, h]⟩

/-- A faulting write observes a permitted class. -/
theorem schreibFehler_in_klassen (m : Speicher) (a : Adresse) (v : Wort)
    (stapel : Bool) (h : write64 m a v = none) :
    ∃ k ∈ datenFehlerKlassen stapel, schreibKlasse m a v = some k := by
  cases stapel with
  | true =>
    exact ⟨.pf, by decide, by simp [schreibKlasse, h]⟩
  | false =>
    exact ⟨.pf, by decide, by simp [schreibKlasse, h]⟩

/-- A successful read is no fault. -/
theorem leseErfolg_kein_fehler (m : Speicher) (a : Adresse) (v : Wort)
    (h : read64 m a = some v) : leseKlasse m a = none := by
  simp [leseKlasse, h]

/-- A successful write is no fault. -/
theorem schreibErfolg_kein_fehler (m : Speicher) (a : Adresse) (v : Wort)
    (m' : Speicher) (h : write64 m a v = some m') :
    schreibKlasse m a v = none := by
  simp [schreibKlasse, h]

/-! ## Divide faults on real canonical execution (DIV/IDIV entries).

  The DIV entry (txt line 31795) and IDIV entry (txt line 31887) trap
  as #DE on a zero divisor or an unrepresentable quotient; the
  destinations are architecturally undefined. The model step reports
  `hardwareHalt` with NO successor, so the observation is the
  pre-state itself: RIP still names the faulting instruction and
  memory is unchanged by construction. Registers RAX/RDX carry no
  preserved claim (explicit nondeterminism for the undefined result). -/

/-- Unsigned divide-by-zero on real execution classifies as #DE. -/
theorem div_null_ist_de (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hnull : (s.register src).toNat = 0) :
    klassifiziereMulDiv (mulDivSchritt d s) = some .de := by
  have hh := fehler_div_null_haelt d s src hok h hnull
  simp [klassifiziereMulDiv, hh]

/-- Unsigned quotient overflow on real execution classifies as #DE. -/
theorem div_ueberlauf_ist_de (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hpos : (s.register src).toNat ≠ 0)
    (hgross : ¬ u128 (s.register Register.rdx) (s.register Register.rax) /
      (s.register src).toNat < 2 ^ 64) :
    klassifiziereMulDiv (mulDivSchritt d s) = some .de := by
  have hh := fehler_div_ueberlauf_haelt d s src hok h hpos hgross
  simp [klassifiziereMulDiv, hh]

/-- Signed divide-by-zero on real execution classifies as #DE. -/
theorem idiv_null_ist_de (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .idivRax src)
    (hnull : sVal .b64 (s.register src) = 0) :
    klassifiziereMulDiv (mulDivSchritt d s) = some .de := by
  have hh := fehler_idiv_null_haelt d s src hok h hnull
  simp [klassifiziereMulDiv, hh]

/-- The unified dispatcher carries the same #DE: halt IS the trap. -/
theorem stepExt_halt_ist_de (m : MulDivDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : mulDivSchritt m t.kern = .hardwareHalt) :
    klassifiziereExt (stepExt (.muldiv m) t b) = some .de := by
  have hs := stepExt_muldiv_halt m t b h
  simp [klassifiziereExt, hs]

/-- The unified dispatcher never faults from refusal: admission stays
    distinct from hardware on every arm. -/
theorem stepExt_verweigert_kein_de (i : ExtInstr) (t : FpZustand)
    (b : BereitProfil) (h : stepExt i t b = .verweigert) :
    klassifiziereExt (stepExt i t b) = none := by
  simp [klassifiziereExt, h]

/-! ## Preserved observations: RIP names the fault, memory is unchanged.

  Fetch/decode/data faults have no successor by construction, so the
  faulting RIP and the pre-fault memory ARE the observation. Divide
  faults additionally leave RAX/RDX undefined: no register claim is
  made for them. No handler is invoked and no RIP is advanced here;
  delivery stays with lane 672. -/

/-- The fault observation: the pre-state RIP plus the pre-state memory.
    What the manual guarantees (fault address, unchanged memory) is
    exactly what is kept; nothing else is promised. -/
structure FehlerBeobachtung where
  fehlerRip : Adresse
  speicherVor : Speicher

/-- Observe a faulting state: RIP still names the faulting instruction. -/
def beobachte (s : Zustand) : FehlerBeobachtung :=
  ⟨s.rip, s.speicher⟩

/-- A refused store changes no byte: the observation keeps memory. -/
theorem storeVerweigert_erhaelt (m : Speicher) (a : Adresse) (v : Wort)
    (h : write64 m a v = none) :
    (∀ m' : Speicher, write64 m a v ≠ some m') ∧
      schreibKlasse m a v = some .pf := by
  refine ⟨?_, by simp [schreibKlasse, h]⟩
  intro m' hm
  rw [h] at hm
  cases hm

/-- NO-SPECULATION (adapter fact): a faulting CMOV-memory source with a
    false condition admits NO successful transition. Any adapter that
    silently makes the untaken operand fault-free contradicts the
    accepted step equation. -/
theorem untaken_kein_stiller_erfolg (d : Decodiert) (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hread : read64 s.speicher (effAddr s base disp) = none)
    (hbed : bedingung c s.flags = false)
    (hstep : cmovMemSchritt d s dst base disp c = some s') : False := by
  obtain ⟨href, _⟩ :=
    fehler_cmov_mem_untaken_haelt d s dst base disp c hok hread hbed
  rw [href] at hstep
  cases hstep

/-! ## Fetch faults on actual bytes: illegal, truncated, non-executable.

  Fetch reads execute permission only (`geholt`); a short or refused
  window is `fetchExt = none` and `extByteschritt = .verweigert` --
  validator refusal, never a fault claim. In particular an illegal
  byte (`0xFF`, refused by the whole unified chain) is NOT silently
  labelled #UD: the model covers a subset, so `decodeExt = none` may
  be a truly illegal encoding OR a legal-but-unmodelled one. Only the
  refusal is proved; the #UD membership stays OPEN. -/

/-- Illegal byte: the whole unified chain refuses `0xFF`. -/
theorem fehlbyte_kette_verweigert :
    decodeExt [natByte 255] = none :=
  pin_ext_nichts_unbekannt

/-- No silent #UD: the refused illegal byte yields refusal, not a fault. -/
theorem fehlbyte_kein_stiller_ud :
    decodeExt [natByte 255] = none ∧
      klassifiziereExt .verweigert = none :=
  ⟨pin_ext_nichts_unbekannt, rfl⟩

/-- Single-byte code memory holding one byte `b` at 4096. -/
def einByteSpeicher (b : Byte) : Speicher :=
  { bytes := fun a => if a.toNat = 4096 then b else BitVec.ofNat 8 0
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := fun a => decide (a.toNat = 4096) }

/-- Single-byte core state at 4096 over `einByteSpeicher`. -/
def einByteKern (b : Byte) : Zustand :=
  { register := fun _ => BitVec.ofNat 64 0
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher := einByteSpeicher b }

/-- Single-byte extended state (reset control word). -/
def einByteStart (b : Byte) : FpZustand :=
  ⟨einByteKern b, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- TRUNCATED FETCH: one executable `jump32` opcode byte without its
    displacement refuses the byte step. -/
theorem fetch_abgeschnitten_verweigert :
    extByteschritt (einByteStart (natByte 233)) extWitBereit =
      .verweigert := by
  rfl

/-- ILLEGAL FETCH: one executable `0xFF` byte refuses the byte step. -/
theorem fetch_fehlbyte_verweigert :
    extByteschritt (einByteStart (natByte 255)) extWitBereit =
      .verweigert := by
  rfl

/-- EXECUTE-DENIED FETCH: a readable but non-executable `ret` byte
    refuses the byte step; readability grants nothing. -/
def ohneExecSpeicher : Speicher :=
  { bytes := fun a =>
      if a.toNat = 4096 then natByte 195 else BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- EXECUTE-DENIED refuses at the unified dispatcher too. -/
theorem fetch_ohne_exec_verweigert :
    extByteschritt
      ⟨{ einByteKern (natByte 195) with speicher := ohneExecSpeicher },
        fun _ => BitVec.ofNat 128 0, kontextReset⟩
      extWitBereit = .verweigert := by
  rfl

/-! ## Enabled-state and alignment honesty.

  Without OS vector state the packed-integer arm refuses at the
  unified dispatcher (validator admission, never a fault claim): the
  would-be hardware #NM stays OPEN, exactly as the task demands --
  refusal is not equated with #UD/#GP/#PF/#NM. Ordinary accesses
  impose NO alignment check (matching silicon, where #AC needs
  flag setup): an unaligned address with full permissions reads and
  writes. The flag-gated #AC itself stays OPEN. -/

/-- Without OS vector state the packed-integer arm refuses, in the
    reached start state too: control-state refusal, never a fault. -/
theorem steuerung_vec_ohne_os_verweigert :
    stepExt (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩) extWitStart
        extWitUnbereit = .verweigert :=
  extWit_vec_ohne_os_verweigert extWitStart

/-- The control-state refusal is no fault for the 660 adapter. -/
theorem steuerung_kein_fehler :
    klassifiziereExt
      (stepExt (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩) extWitStart
        extWitUnbereit) = none := by
  simp [steuerung_vec_ohne_os_verweigert, klassifiziereExt]

/-- UNALIGNED WITHOUT #AC: address 8193 is not 8-aligned, yet with
    full permissions it reads zero and stores. -/
theorem zugriff_ohne_ac :
    addrAusgerichtet (BitVec.ofNat 64 8193) 8 = false ∧
      read64 zeugenSpeicher (BitVec.ofNat 64 8193) = some 0 ∧
      ∃ m' : Speicher,
        write64 zeugenSpeicher (BitVec.ofNat 64 8193) 42 = some m' := by
  have hsch : schreibbar8 zeugenSpeicher (BitVec.ofNat 64 8193) = true := by
    decide
  have hwr : write64 zeugenSpeicher (BitVec.ofNat 64 8193) (42 : Wort) =
      some { zeugenSpeicher with
        bytes := writeBytes zeugenSpeicher (BitVec.ofNat 64 8193) 42 } := by
    unfold write64
    rw [if_pos hsch]
  exact ⟨by decide, by decide, _, hwr⟩

/-- OVERLAP refusal stays refusal: the partial-overlap pair is not
    admitted by the conservative policy (reused, not restated). -/
theorem ueberlapp_verweigert_bleibt :
    aliasZulassen (klassifiziere (Fuss (natAdresse 8192))
      (Fuss (natAdresse 8196))) = false :=
  gegenbeispielC_verweigert

/-! ## Joint witness: normal store run plus faulting fetch/store/divide.

  One conjunction ties the reached memory-changing run to three
  fault observations with their correct preserved state and class:
  the divide trap IS #DE with the pre-state as its observation, the
  truncated fetch refuses with no fault, and the dark-memory store
  refuses inside its permitted class. Non-degenerate: the run stores
  42 into two actual cells starting from zero. -/

/-- `INT_MIN / -1` on real execution classifies as #DE. -/
theorem idiv_min_neg1_ist_de :
    klassifiziereMulDiv
      (mulDivSchritt ⟨.idivRax .rcx, 3⟩ dfZustandIdivMin) =
      some .de := by
  have h := fehler_idiv_oben_haelt_zeuge.1
  simp [klassifiziereMulDiv, h]

/-- Dark-memory store: nothing writable, so the write refuses inside
    its permitted class. -/
theorem dunkel_schreiben_in_klasse :
    schreibKlasse witDunkel (BitVec.ofNat 64 8192) 42 = some .pf := by
  have hsch : schreibbar8 witDunkel (BitVec.ofNat 64 8192) = false := by
    decide
  have h := write64_verweigert witDunkel (BitVec.ofNat 64 8192) 42 hsch
  unfold schreibKlasse
  rw [h]

/-- JOINT WITNESS: the reached two-step store run changes two actual
    cells from zero to 42; the zero-divisor divide classifies as #DE
    with its fault RIP still naming the pre-state; the truncated
    fetch refuses with no fault; the dark store refuses in-class. -/
theorem fehler_zeuge_gemeinsam :
    extZelle (extSchritt2 extWitStart extWitBereit)
        (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) ∧
      extZelle (extSchritt2 extWitStart extWitBereit)
        (BitVec.ofNat 64 8200) = some (BitVec.ofNat 8 42) ∧
      extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      klassifiziereMulDiv
        (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = some .de ∧
      (beobachte mdZustandNull).fehlerRip = mdZustandNull.rip ∧
      extByteschritt (einByteStart (natByte 233)) extWitBereit =
        .verweigert ∧
      klassifiziereExt
        (extByteschritt (einByteStart (natByte 233))
          extWitBereit) = none ∧
      schreibKlasse witDunkel (BitVec.ofNat 64 8192) 42 =
        some .pf := by
  have hdiv := fehler_div_null_haelt_zeuge.1
  refine ⟨extWit_zwei_schritte_speichern.1,
    extWit_zwei_schritte_speichern.2, extWit_anfang_null.1, ?_,
    rfl, fetch_abgeschnitten_verweigert, ?_,
    dunkel_schreiben_in_klasse⟩
  · simp [klassifiziereMulDiv, hdiv]
  · rfl

/- CUTS:
    Proved here (all over the REUSED canonical dispatchers, steps and
    checks -- no new machine, no new decoder row, no new instruction,
    no source claim):
    - fault vocabulary `ArchFehler` (#DE/#UD/#GP/#SS/#PF/#AC/#NM/#XM,
      Table 6-1) with the outcome classifiers `klassifiziereMulDiv` /
      `klassifiziereExt` and the 660 adapter `adapter660_klasse`
      (halt IS #DE; success and refusal are never a fault);
    - canonical addressing (§3.3.7.1): `istKanonisch` at 48 bits with
      #SS for stack vs #GP for data references, pinned on 0/4096/8192
      vs `2 ^ 47`;
    - data-memory faults as an explicit permitted SET (`#SS/#PF` for
      stack, `#GP/#PF` else) with the pinned `#PF` member tied to the
      real `read64`/`write64` equations; success is never a fault;
    - divide faults on REAL execution (DIV/IDIV entries): zero divisor
      and both overflow directions classify as #DE through the unified
      dispatcher; destinations stay undefined (no RAX/RDX claim);
    - preserved observations: the fault observation IS the pre-state
      (RIP names the fault, memory unchanged by construction); no
      handler call and no RIP advance are modelled -- delivery stays
      with lane 672;
    - no-speculation: a faulting CMOV-memory source refuses on the
      untaken path too, so no adapter may silently make it fault-free;
    - fetch facts on actual bytes: illegal `0xFF` (no silent #UD --
      refusal may be illegal OR unmodelled), truncated `jump32`,
      execute-denied `ret`; enabled-state refusal (packed integer
      without OS state) with no fault claim; unaligned access without
      #AC; overlap refusal reused;
    - joint witness: reached two-cell store run plus divide/fetch/
      store fault observations with correct class and preserved state.
    NOT proved here, and not claimed:
    - No fault PRIORITY between pending classes (fetch vs data vs
      divide order, #GP vs #PF disambiguation needs paging info the
      model has no field for) and no privilege/stack-switch detail:
      fault DELIVERY (IDT/stack/handler/error code) stays with 672.
    - No #UD membership: `decodeExt = none` is proved refusal only;
      which refused bytes are truly illegal encodings stays OPEN.
    - No unmasked #XM/#AC/#NM claim: scalar FP runs masked by default
      (model computes, never traps); flag-gated #AC and CR0-gated #NM
      need control state the admitted profile does not carry.
    - No TSO/concurrency bridge: all facts are sequential over one
      `Speicher`; tearing and GX refinement stay with the TSO lane.
    - No hardware verification: classes NAME the manual entries; the
      quotient rule and flag relations are stated semantics inherited
      from `MulDiv`/`Ganzzahl`, not verified against silicon.
    - No source stop-class transfer, no cost or time transfer.
-/

#print axioms klassifiziereMulDiv
#print axioms klassifiziereExt
#print axioms adapter660_klasse
#print axioms istKanonisch
#print axioms adrKlasse
#print axioms datenFehlerKlassen
#print axioms leseKlasse
#print axioms schreibKlasse
#print axioms div_null_ist_de
#print axioms div_ueberlauf_ist_de
#print axioms idiv_null_ist_de
#print axioms idiv_min_neg1_ist_de
#print axioms stepExt_halt_ist_de
#print axioms stepExt_verweigert_kein_de
#print axioms beobachte
#print axioms untaken_kein_stiller_erfolg
#print axioms fetch_abgeschnitten_verweigert
#print axioms fetch_fehlbyte_verweigert
#print axioms fetch_ohne_exec_verweigert
#print axioms steuerung_vec_ohne_os_verweigert
#print axioms zugriff_ohne_ac
#print axioms ueberlapp_verweigert_bleibt
#print axioms dunkel_schreiben_in_klasse
#print axioms fehler_zeuge_gemeinsam

end Gabbro.Grammatik.X86
