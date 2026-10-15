/-
  File:      Grammatik/X86/DecodeFault.lean
  Subject:   Fault preservation catalogue over the accepted pilot vocabulary.

  Lane 543 (row N16): trapping-operation / refusal facts tied to the actual
  `Ausfuehrung.schritt` and `MulDiv.mulDivSchritt` effects, the accepted
  `ControlFlow.cmovMemSchritt` no-speculation fact and the accepted
  `NarrowOps` profile admission. Validator refusal (a `Bool`) is never an
  architectural fault (a step outcome). Full extended decoding and source
  stop-class transfer stay OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.MulDiv
import Grammatik.X86.ControlFlow
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- Architectural fault outcome of a new-form step: only `hardwareHalt`. -/
def istArchitekturFehler : MulDivErgebnis → Bool
  | .hardwareHalt => true
  | _ => false

/-- Unsigned division by zero traps: the step is the hardware halt. -/
theorem fehler_div_null_haelt (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hnull : (s.register src).toNat = 0) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitU_verweigert_bei_null (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hnull
  exact md_div_halt d s src hok h hnone

/-- Unsigned quotient overflow traps: the step is the hardware halt. -/
theorem fehler_div_ueberlauf_haelt (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hpos : (s.register src).toNat ≠ 0)
    (hgross : ¬ u128 (s.register Register.rdx) (s.register Register.rax) /
      (s.register src).toNat < 2 ^ 64) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitU_verweigert_bei_ueberlauf (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hpos hgross
  exact md_div_halt d s src hok h hnone

/-- Signed division by zero traps: the step is the hardware halt. -/
theorem fehler_idiv_null_haelt (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .idivRax src)
    (hnull : sVal .b64 (s.register src) = 0) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitS_verweigert_bei_null (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hnull
  exact md_idiv_halt d s src hok h hnone

/-- Signed quotient overflow above the range traps. -/
theorem fehler_idiv_oben_haelt (d : MulDivDecodiert) (s : Zustand)
    (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .idivRax src)
    (hpos : sVal .b64 (s.register src) ≠ 0)
    (hgross : ((2 ^ 63 : Nat) : Int) ≤
      (s128 (s.register Register.rdx) (s.register Register.rax)).tdiv
        (sVal .b64 (s.register src))) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitS_verweigert_bei_oben (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hpos hgross
  exact md_idiv_halt d s src hok h hnone

/-- A faulting CMOV-memory source refuses on the untaken path too:
    the untaken path is not automatically fault-free. -/
theorem fehler_cmov_mem_untaken_haelt (d : Decodiert) (s : Zustand)
    (dst base : Register) (disp : BitVec 32) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hread : read64 s.speicher (effAddr s base disp) = none)
    (hbed : bedingung c s.flags = false) :
    cmovMemSchritt d s dst base disp c = none ∧
      bedingung c s.flags = false :=
  cmovMem_feheler_bleibt d s dst base disp c hok hread hbed

/-- Motion/DCE refusal: a trapping division is never marked pure,
    so no motion may treat it as removable. -/
theorem bewegung_verweigert_fuer_falle (src : Register) :
    rein (.divRax src) = false ∧ rein (.idivRax src) = false :=
  ⟨rfl, rfl⟩

/-- Decode refusal is no architectural fault: a bad length misses,
    it never halts as hardware. -/
theorem dekodierverweigerung_ist_kein_hardwarehalt (d : MulDivDecodiert)
    (s : Zustand) (h : laengeOk d.laenge = false) :
    mulDivSchritt d s = .misslungen ∧
      istArchitekturFehler (mulDivSchritt d s) = false := by
  have hm := md_laenge_misslungen d s h
  exact ⟨hm, by rw [hm]; rfl⟩

/-- Profile refusal is no architectural fault: at the misaligned
    address the narrow admission refuses, yet the scalar read answers. -/
theorem profilverweigerung_ist_kein_fehler :
    narrowAdmitted zeugenSpeicher (BitVec.ofNat 64 8193) .b32 false = false ∧
      readBreite zeugenSpeicher .b32 (BitVec.ofNat 64 8193) = some 0 :=
  probe_fallback_unaligned

/-- Moving a faulting operation can change observations: the SAME
    division halts under a zero divisor and answers under `17 / 5`, so
    hoisting it across a divisor-defining store is observable. -/
theorem bewegen_aendert_beobachtung :
    istHalt (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = true ∧
      okWerte (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandDiv) =
        some (3, 2, false) :=
  ⟨probe_div_halt_schritt, probe_div_schritt⟩

/-- Witness state for the 65-bit quotient `2 ^ 64 / 1`: RDX = 1,
    RAX = 0, divisor RCX = 1. -/
def dfZustandUeberlauf : Zustand :=
  { register := (fun q => if q = Register.rax then BitVec.ofNat 64 0
      else if q = Register.rdx then BitVec.ofNat 64 1
      else if q = Register.rcx then BitVec.ofNat 64 1
      else if q = Register.rsp then BitVec.ofNat 64 8192
      else BitVec.ofNat 64 0),
    flags := zeugeFlags, rip := BitVec.ofNat 64 4096,
    speicher := zeugeSpeicher }

/-- JOINT witness for `fehler_div_ueberlauf_haelt`: concrete overflow
    premises plus the quotient/remainder memory run with an observable
    byte change. -/
theorem fehler_div_ueberlauf_haelt_zeuge :
    mulDivSchritt ⟨.divRax .rcx, 3⟩ dfZustandUeberlauf = .hardwareHalt ∧
    ∃ (m1 m2 : Speicher),
      write64 zeugenSpeicher 0 3 = some m1 ∧
      read64 m1 0 = some 3 ∧
      zeugenSpeicher.bytes 0 ≠ m1.bytes 0 ∧
      write64 m1 8 2 = some m2 ∧
      read64 m2 8 = some 2 := by
  have hpos : (dfZustandUeberlauf.register .rcx).toNat ≠ 0 := by decide
  have hgross : ¬ u128 (dfZustandUeberlauf.register .rdx)
      (dfZustandUeberlauf.register .rax) /
      (dfZustandUeberlauf.register .rcx).toNat < 2 ^ 64 := by
    decide
  exact ⟨fehler_div_ueberlauf_haelt _ _ _ (by decide) rfl hpos hgross,
    muldiv_speicher_sonde.2⟩

/-- Witness state for `INT_MIN / -1`: RDX = -1, RAX = INT_MIN,
    divisor RCX = -1 (signed quotient overflow). -/
def dfZustandIdivMin : Zustand :=
  { register := (fun q => if q = Register.rax then 0x8000000000000000
      else if q = Register.rdx then 0xFFFFFFFFFFFFFFFF
      else if q = Register.rcx then 0xFFFFFFFFFFFFFFFF
      else if q = Register.rsp then BitVec.ofNat 64 8192
      else BitVec.ofNat 64 0),
    flags := zeugeFlags, rip := BitVec.ofNat 64 4096,
    speicher := zeugeSpeicher }

/-- JOINT witness for `fehler_idiv_oben_haelt`: the `INT_MIN / -1`
    premises on concrete values plus the memory run with an observable
    byte change. -/
theorem fehler_idiv_oben_haelt_zeuge :
    mulDivSchritt ⟨.idivRax .rcx, 3⟩ dfZustandIdivMin = .hardwareHalt ∧
    ∃ (m1 m2 : Speicher),
      write64 zeugenSpeicher 0 3 = some m1 ∧
      read64 m1 0 = some 3 ∧
      zeugenSpeicher.bytes 0 ≠ m1.bytes 0 ∧
      write64 m1 8 2 = some m2 ∧
      read64 m2 8 = some 2 := by
  have hpos : sVal .b64 (dfZustandIdivMin.register .rcx) ≠ 0 := by decide
  have hgross : ((2 ^ 63 : Nat) : Int) ≤
      (s128 (dfZustandIdivMin.register .rdx)
        (dfZustandIdivMin.register .rax)).tdiv
        (sVal .b64 (dfZustandIdivMin.register .rcx)) := by
    decide
  exact ⟨fehler_idiv_oben_haelt _ _ _ (by decide) rfl hpos hgross,
    muldiv_speicher_sonde.2⟩

/-- JOINT witness for `fehler_div_null_haelt`: zero-divisor premises
    on concrete values plus the memory run with an observable change. -/
theorem fehler_div_null_haelt_zeuge :
    mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull = .hardwareHalt ∧
    ∃ (m1 m2 : Speicher),
      write64 zeugenSpeicher 0 3 = some m1 ∧
      read64 m1 0 = some 3 ∧
      zeugenSpeicher.bytes 0 ≠ m1.bytes 0 ∧
      write64 m1 8 2 = some m2 ∧
      read64 m2 8 = some 2 :=
  ⟨fehler_div_null_haelt _ _ _ (by decide) rfl (by decide),
    muldiv_speicher_sonde.2⟩

/-- JOINT witness for `fehler_idiv_null_haelt`: signed zero-divisor
    premises on concrete values plus the memory run. -/
theorem fehler_idiv_null_haelt_zeuge :
    mulDivSchritt ⟨.idivRax .rcx, 3⟩ mdZustandNull = .hardwareHalt ∧
    ∃ (m1 m2 : Speicher),
      write64 zeugenSpeicher 0 3 = some m1 ∧
      read64 m1 0 = some 3 ∧
      zeugenSpeicher.bytes 0 ≠ m1.bytes 0 ∧
      write64 m1 8 2 = some m2 ∧
      read64 m2 8 = some 2 := by
  have hnull : sVal .b64 (mdZustandNull.register .rcx) = 0 := by decide
  exact ⟨fehler_idiv_null_haelt _ _ _ (by decide) rfl hnull,
    muldiv_speicher_sonde.2⟩

/-- JOINT witness for `fehler_cmov_mem_untaken_haelt`: unreadable
    source with a false condition still refuses, plus the memory run. -/
theorem fehler_cmov_mem_untaken_haelt_zeuge :
    cmovMemSchritt ⟨.movReg64 .rax .rbx, 3⟩
      { witFalse with speicher := witDunkel } .rax .rsp
      (BitVec.ofNat 32 0) .e = none ∧
    bedingung .e witFalse.flags = false ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hok : laengeOk 3 = true := by decide
  have hread : read64 witDunkel
      (effAddr { witFalse with speicher := witDunkel } .rsp
        (BitVec.ofNat 32 0)) = none := by
    decide
  have hbed : bedingung .e witFalse.flags = false := by decide
  obtain ⟨href, _⟩ := fehler_cmov_mem_untaken_haelt
    ⟨.movReg64 .rax .rbx, 3⟩ { witFalse with speicher := witDunkel } .rax .rsp
    (BitVec.ofNat 32 0) .e hok hread hbed
  exact ⟨href, hbed, cmov_speicher_zeuge⟩

/- CUTS:
    Proved here (all over the REUSED canonical `MulDiv.mulDivSchritt`,
    `ControlFlow.cmovMemSchritt`, `NarrowOps.narrowAdmitted`/`readBreite`
    and the reused witness states -- no new machine, no new instruction,
    no new decoder row, no source claim):
    - fault preservation catalogue: unsigned div-by-zero, unsigned quotient
      overflow, signed div-by-zero and signed quotient overflow each force
      `MulDivErgebnis.hardwareHalt` (the divide-error trap), each with a
      joint concrete witness plus the quotient/remainder memory run with an
      observable byte change;
    - faulting CMOV-memory keeps its fault on the untaken path
      (`cmovMem_feheler_bleibt` reused, not restated), with a joint witness
      on unreadable memory plus the selected-word memory run;
    - motion/DCE refusal: trapping divisions are never pure, with the
      concrete observable pair (same division halts under a zero divisor
      and answers `17 / 5 = 3` remainder `2` under a defined one), so
      hoisting a trapping operation across a divisor-defining store is
      observably different;
    - validator refusal versus architectural fault: a bad decode length
      misses (never a hardware halt), and a refused narrow profile
      admission still answers the scalar read -- refusal channels are
      distinct from faults by construction, never by prose.
    NOT proved here, and not claimed:
    - No extended decoding: `MulDivDecodiert.laenge` is checked input data
      (1..15); which bytes encode MUL/IMUL/DIV/IDIV stays with `Codec`
      and the Typen owner.
    - No source stop-class transfer: `hardwareHalt` NAMES the stop class
      the source `FortschrittG` calls `hardware`; the guard/fault/channel/
      order correspondence stays OPEN with the bridge lane.
    - No TSO/concurrency bridge: all facts are sequential over one
      `Speicher`; tearing and GX refinement stay with the TSO lane.
    - No hardware verification: the quotient-overflow rule, truncation
      direction and flag relations are STATED executable semantics
      inherited from `MulDiv`/`Ganzzahl`, not verified against silicon.
    - No cost or time transfer: no cycle or latency claim is made.
-/

#print axioms istArchitekturFehler
#print axioms fehler_div_null_haelt
#print axioms fehler_div_ueberlauf_haelt
#print axioms fehler_idiv_null_haelt
#print axioms fehler_idiv_oben_haelt
#print axioms fehler_cmov_mem_untaken_haelt
#print axioms bewegung_verweigert_fuer_falle
#print axioms dekodierverweigerung_ist_kein_hardwarehalt
#print axioms profilverweigerung_ist_kein_fehler
#print axioms bewegen_aendert_beobachtung
#print axioms fehler_div_null_haelt_zeuge
#print axioms fehler_div_ueberlauf_haelt_zeuge
#print axioms fehler_idiv_null_haelt_zeuge
#print axioms fehler_idiv_oben_haelt_zeuge
#print axioms fehler_cmov_mem_untaken_haelt_zeuge

end Gabbro.Grammatik.X86
