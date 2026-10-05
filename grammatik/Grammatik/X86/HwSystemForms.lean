/-
  File:      Grammatik/X86/HwSystemForms.lean
  Subject:   Privileged/system instructions for OS and freestanding profiles.

  Lane 1151: the system-forms family producer over the coherent machine
  of `HardwareExecution.lean` §11. Event type (`SysEreignis`), outcome
  (`SysAusgang` over the accepted `ArchFehler` of `HardwareFaults.lean`,
  never edited here), `HwAdapter` plug (`adapterSystem`) and extended
  step relation (`SysSchritt`) embedding `HwSchritt` exactly.

  Silicon assumptions (ANNAHMEN, clone-local Intel SDM extracts):
  - S-PRIV: HLT faults #GP(0) unless CPL = 0 (Vol. 2A 3-439).
  - S-IF: CLI/STI fault #GP(0) when CPL > IOPL (Vol. 2A 3-148/3-149,
    2B 4-674/4-675); PVI/VME/VIF refinement is NOT modelled (CUTS).
  - S-PAUSE: PAUSE changes no architectural state (Vol. 2B 4-226).
  - S-CPUID: any privilege, serialising, EAX/EBX/ECX/EDX out, high
    halves of RAX..RDX cleared (Vol. 2A 3-203/3-204).
  - S-RDTSC: EDX:EAX, high halves cleared, #GP(0) iff TSD set and
    CPL > 0, NOT serialising (Vol. 2B 4-561/4-562).
  - S-SYSCALL: 64-bit + SCE else #UD; RCX := next RIP, RIP := LSTAR,
    R11 := RFLAGS, RFLAGS &= ~FMASK, CPL := 0 (Vol. 2B 4-699/4-700).
  - S-SYSRET: #UD unless 64-bit + SCE, #GP(0) unless CPL = 0, #GP(0)
    on noncanonical RCX (64-bit); RIP := RCX, CPL := 3 (Vol. 2B 4-709).
  - S-INT: software INT checks DPL (INT1 exempt) through the accepted
    `pruefeTor`/`liefere` pipeline, reused unchanged (INT entry).
  - S-SERIAL: CPUID serialises; SYSCALL/SYSRET/RDTSC/INT delivery do
    NOT drain the TSO store buffer (SYSCALL/SYSRET ordering note,
    Vol. 2B 4-699/4-709). Buffer equations are proved; the ordering
    claim itself stays a named assumption, never a theorem.
  No OS is assumed: MSR snapshots and leaf answers arrive as explicit
  caller inputs; an environment service is user logic. Absent profile
  form = architectural #UD.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.InterruptDescriptorHardware
import Grammatik.X86.HardwareFaults
import Grammatik.X86.ArchitecturalFlags

namespace Gabbro.Grammatik.X86

/-- System-form kind: the ten privileged/system instructions. -/
inductive SysFormArt where
  | hlt | cli | sti | pause | cpuid | rdtsc
  | intN | iret | syscall | sysret
  deriving DecidableEq, Repr

/-! ## 1. Encoded lengths: one row per form from the opcode table.
    HLT F4 (1); CLI FA (1); STI FB (1); PAUSE F3 90 (2);
    CPUID 0F A2 (2); RDTSC 0F 31 (2); INT n CD ib (2);
    IRET CF (1); SYSCALL 0F 05 (2); SYSRET 0F 07 (2,
    REX.W form 3 -- the lane models the 64-bit return only, CUTS). -/

/-- Encoded length of each system form. -/
def sysLaenge : SysFormArt → Nat
  | .hlt => 1 | .cli => 1 | .sti => 1 | .pause => 2
  | .cpuid => 2 | .rdtsc => 2 | .intN => 2 | .iret => 1
  | .syscall => 2 | .sysret => 2

/-- Length pins: every form carries its opcode-table length. -/
theorem sysLaenge_pins :
    sysLaenge .hlt = 1 ∧ sysLaenge .cli = 1 ∧
      sysLaenge .sti = 1 ∧ sysLaenge .pause = 2 ∧
      sysLaenge .cpuid = 2 ∧ sysLaenge .rdtsc = 2 ∧
      sysLaenge .intN = 2 ∧ sysLaenge .iret = 1 ∧
      sysLaenge .syscall = 2 ∧ sysLaenge .sysret = 2 := by
  decide

/-! ## 2. Profiles: hosted OS versus freestanding.
    The profile selects which forms are enabled; an absent form is
    the architectural #UD. Privilege (CPL) is orthogonal and checked
    per step against the stored control state. -/

/-- Environment profile: hosted OS service or freestanding. -/
inductive SysProfilArt where
  | gehostet | freistehend
  deriving DecidableEq, Repr

/-- Enabled forms per profile: freestanding has no OS syscall
    handler, so SYSCALL/SYSRET are absent there; every other form
    is present in both (privilege still gates per step). -/
def formFrei : SysProfilArt → SysFormArt → Bool
  | .freistehend, .syscall => false
  | .freistehend, .sysret => false
  | _, _ => true

/-- Hosted enables every form. -/
theorem formFrei_gehostet (f : SysFormArt) :
    formFrei .gehostet f = true := by
  cases f <;> rfl

/-- Freestanding refuses exactly the syscall pair. -/
theorem formFrei_freistehend :
    formFrei .freistehend .syscall = false ∧
      formFrei .freistehend .sysret = false ∧
      formFrei .freistehend .hlt = true ∧
      formFrei .freistehend .intN = true := by
  decide

/-! ## 3. Per-core system control beside the coherent machine.
    `HwKern` carries no CPL/IF (its `Flags` are the six arithmetic
    bits only), so control lives here: the canonical `Steuer`
    (cpl/iopl/ifBit/vm, `ArchitecturalFlags`, reused unchanged), the
    HLT halt bit, and the full RFLAGS word the SYSCALL/SYSRET/INT
    frames save and restore. -/

/-- Per-core system control: canonical privilege state, HLT bit
    and the full RFLAGS word. -/
structure SysSteuer where
  steuer : Steuer
  halted : Bool
  rflagsW : Wort
  deriving DecidableEq, Repr

/-- Extended machine: coherent machine plus per-core control. -/
structure SysMaschine where
  hw : HwMaschine
  sys : Nat → SysSteuer

/-- Well-formedness lifts from the coherent machine. -/
def SysWf (s : SysMaschine) : Prop := HwWf s.hw

/-- CPUID leaf answer: the four output words the environment
    reports for the caller's leaf (user logic, never invented). -/
structure CpuIdAntwort where
  eax : Wort
  ebx : Wort
  ecx : Wort
  edx : Wort
  deriving DecidableEq, Repr

/-- Profile snapshot for one step: environment plus the OS-written
    configuration the architecture reads but never invents. MSR
    values, leaf answers and the time-stamp word arrive as explicit
    caller inputs (environment service is user logic); the step
    computes only the architectural effect. -/
structure SysEingaben where
  profil : SysProfilArt
  sceLang : Bool
  tsd : Bool
  lstar : Wort
  fmask : Wort
  op64 : Bool
  eaxIn : Wort
  ecxIn : Wort
  cpuidOut : CpuIdAntwort
  tsc : Wort
  vektor : Nat
  codeOk : Bool
  wechsel : Bool
  neuDpl : Nat
  idtBasis : Adresse
  idtLimit : Nat
  tssBasis : Adresse
  tssLimit : Nat
  deriving DecidableEq, Repr

/-- One system event: the form plus its explicit inputs. -/
structure SysEreignis where
  form : SysFormArt
  eingaben : SysEingaben
  deriving DecidableEq, Repr

/-- Machine-level system outcome: successor, architectural fault
    class (the accepted `ArchFehler` vocabulary, never redefined),
    or explicit refusal. -/
inductive SysAusgang where
  | ok : SysMaschine → SysAusgang
  | fehler : ArchFehler → SysAusgang
  | verweigert : SysAusgang

/-- Descriptor-path faults classified to the accepted classes:
    gate/stack-pointer faults follow §3.3.7.1 (#SS for stack
    references, #GP else); the not-present gate has no `#NP` member
    in `ArchFehler` and maps to #GP (CUTS); TSS faults likewise. -/
def torFehlerKlasse : TorFehler → ArchFehler
  | .stapelFehler => .ss
  | _ => .gp

/-- Stack faults classify as #SS. -/
theorem torFehlerKlasse_stapel :
    torFehlerKlasse .stapelFehler = .ss := rfl

/-- Every other descriptor fault classifies as #GP. -/
theorem torFehlerKlasse_gp (v : Nat) :
    torFehlerKlasse (.limitFehler v) = .gp ∧
      torFehlerKlasse (.dplFehler v) = .gp ∧
      torFehlerKlasse (.nichtVorhanden v) = .gp ∧
      torFehlerKlasse .zielFehler = .gp :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 4. Single-core outcome and the register-only legs.
    The outcome carries the new core data, new control and new
    memory; buffers and both profiles are untouched by
    construction. -/

/-- Single-core system outcome: new core data, control and memory,
    the fault class, or explicit refusal. -/
inductive SysSnapAusgang where
  | ok : HwKern → SysSteuer → Speicher → SysSnapAusgang
  | fehler : ArchFehler → SysSnapAusgang
  | verweigert : SysSnapAusgang

/-- Core data with new registers and RIP; flags, XMM and FP kept. -/
def kernMitRegRip (k : HwKern) (reg : Register → Wort)
    (rip : Adresse) : HwKern :=
  ⟨reg, k.flags, rip, k.xmm, k.fp⟩

/-- The new core data carries the registers. -/
theorem kernMitRegRip_reg (k : HwKern) (reg : Register → Wort)
    (rip : Adresse) (q : Register) :
    (kernMitRegRip k reg rip).register q = reg q := rfl

/-- The new core data carries the RIP. -/
theorem kernMitRegRip_rip (k : HwKern) (reg : Register → Wort)
    (rip : Adresse) :
    (kernMitRegRip k reg rip).rip = rip := rfl

/-- The new core data keeps the arithmetic flags. -/
theorem kernMitRegRip_flags (k : HwKern) (reg : Register → Wort)
    (rip : Adresse) :
    (kernMitRegRip k reg rip).flags = k.flags := rfl

/-- Zero-extended low 32 bits: CPUID/RDTSC answers on the 64-bit file. -/
def ext32 (w : Wort) : Wort := w &&& (0xFFFFFFFF : Wort)

/-- Low half of a 64-bit time-stamp word (RDTSC EAX side). -/
def tscTief (t : Wort) : Wort := ext32 t

/-- High half of a 64-bit time-stamp word (RDTSC EDX side). -/
def tscHoch (t : Wort) : Wort := ext32 (t >>> 32)

/-- HLT leg: CPL 0 halts past the 1-byte form, else #GP(0).
    Saved IP points past HLT; only this core halts (S-PRIV). -/
def schrittHlt (m : HwMaschine) (c : Nat) (st : SysSteuer) :
    SysSnapAusgang :=
  if st.steuer.cpl = 0 then
    let k := m.kerne c
    .ok (kernMitRegRip k k.register
      (k.rip + BitVec.ofNat 64 (sysLaenge .hlt)))
      ⟨st.steuer, true, st.rflagsW⟩ m.mem
  else .fehler .gp

/-- HLT at CPL 0 halts with RIP past the form. -/
theorem schrittHlt_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (h : st.steuer.cpl = 0) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittHlt m c st = .ok k' st' m.mem ∧ st'.halted = true ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 1 := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .hlt)),
    ⟨st.steuer, true, st.rflagsW⟩, ?_, rfl, rfl⟩
  simp [schrittHlt, h, sysLaenge]

/-- HLT above CPL 0 is #GP(0) and changes nothing. -/
theorem schrittHlt_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (h : ¬ st.steuer.cpl = 0) :
    schrittHlt m c st = .fehler .gp := by
  simp [schrittHlt, h]

/-- CLI/STI leg: CPL ≤ IOPL flips IF past the 1-byte form,
    else #GP(0) (S-IF; VIF/PVI refinement open, CUTS). -/
def schrittIf (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (neu : Bool) (laenge : Nat) : SysSnapAusgang :=
  if st.steuer.cpl ≤ st.steuer.iopl then
    let k := m.kerne c
    .ok (kernMitRegRip k k.register
      (k.rip + BitVec.ofNat 64 laenge))
      ⟨⟨st.steuer.cpl, st.steuer.iopl, neu, st.steuer.vm⟩,
        st.halted, st.rflagsW⟩ m.mem
  else .fehler .gp

/-- CLI clears IF where admitted. -/
theorem schrittIf_cli_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (h : st.steuer.cpl ≤ st.steuer.iopl) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittIf m c st false (sysLaenge .cli) = .ok k' st' m.mem ∧
        st'.steuer.ifBit = false := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .cli)),
    ⟨⟨st.steuer.cpl, st.steuer.iopl, false, st.steuer.vm⟩,
      st.halted, st.rflagsW⟩, ?_, rfl⟩
  simp [schrittIf, h]

/-- STI sets IF where admitted. -/
theorem schrittIf_sti_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (h : st.steuer.cpl ≤ st.steuer.iopl) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittIf m c st true (sysLaenge .sti) = .ok k' st' m.mem ∧
        st'.steuer.ifBit = true := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .sti)),
    ⟨⟨st.steuer.cpl, st.steuer.iopl, true, st.steuer.vm⟩,
      st.halted, st.rflagsW⟩, ?_, rfl⟩
  simp [schrittIf, h]

/-- CLI/STI above IOPL is #GP(0). -/
theorem schrittIf_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (neu : Bool) (laenge : Nat)
    (h : ¬ st.steuer.cpl ≤ st.steuer.iopl) :
    schrittIf m c st neu laenge = .fehler .gp := by
  simp [schrittIf, h]

/-- PAUSE leg: the 2-byte hint advances RIP and changes nothing
    else (S-PAUSE: no architectural state change, no fault). -/
def schrittPause (m : HwMaschine) (c : Nat) (st : SysSteuer) :
    SysSnapAusgang :=
  let k := m.kerne c
  .ok (kernMitRegRip k k.register
    (k.rip + BitVec.ofNat 64 (sysLaenge .pause))) st m.mem

/-- PAUSE keeps registers, control and memory. -/
theorem schrittPause_still (m : HwMaschine) (c : Nat) (st : SysSteuer) :
    ∃ k' : HwKern, ∃ st' : SysSteuer, ∃ mem' : Speicher,
      schrittPause m c st = .ok k' st' mem' ∧
        k'.register = (m.kerne c).register ∧ st' = st ∧
        mem' = m.mem ∧
        k'.rip = (m.kerne c).rip + BitVec.ofNat 64 2 := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .pause)),
    st, m.mem, ?_, rfl, rfl, rfl, rfl⟩
  simp [schrittPause]

/-- CPUID leg: the caller-supplied leaf answer lands zero-extended
    in EAX/EBX/ECX/EDX at any privilege (S-CPUID); the high halves
    of RAX..RDX are cleared. The leaf select (EAX/ECX in) is
    environment addressing, carried for the record. -/
def schrittCpuid (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ans : CpuIdAntwort) : SysSnapAusgang :=
  let k := m.kerne c
  let reg : Register → Wort := fun q =>
    match q with
    | .rax => ext32 ans.eax
    | .rbx => ext32 ans.ebx
    | .rcx => ext32 ans.ecx
    | .rdx => ext32 ans.edx
    | _ => k.register q
  .ok (kernMitRegRip k reg
    (k.rip + BitVec.ofNat 64 (sysLaenge .cpuid))) st m.mem

/-- CPUID writes the zero-extended EAX answer. -/
theorem schrittCpuid_rax (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ans : CpuIdAntwort) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittCpuid m c st ans = .ok k' st' m.mem ∧
        k'.register .rax = ext32 ans.eax ∧ st' = st := by
  refine ⟨kernMitRegRip (m.kerne c)
    (fun q => match q with
      | .rax => ext32 ans.eax
      | .rbx => ext32 ans.ebx
      | .rcx => ext32 ans.ecx
      | .rdx => ext32 ans.edx
      | _ => (m.kerne c).register q)
    ((m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .cpuid)),
    st, ?_, ?_, rfl⟩
  · simp [schrittCpuid]
  · rfl

/-- RDTSC leg: the caller-supplied stamp lands split in EDX:EAX
    with cleared high halves; TSD-gated #GP(0) above CPL 0
    (S-RDTSC, explicitly NOT serialising: S-RDTSC-UNGEORDNET). -/
def schrittRdtsc (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (tsd : Bool) (tsc : Wort) : SysSnapAusgang :=
  if tsd && decide (0 < st.steuer.cpl) then .fehler .gp
  else
    let k := m.kerne c
    let reg : Register → Wort := fun q =>
      match q with
      | .rax => tscTief tsc
      | .rdx => tscHoch tsc
      | _ => k.register q
    .ok (kernMitRegRip k reg
      (k.rip + BitVec.ofNat 64 (sysLaenge .rdtsc))) st m.mem

/-- RDTSC with TSD set above CPL 0 is #GP(0). -/
theorem schrittRdtsc_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (tsc : Wort) (h : 0 < st.steuer.cpl) :
    schrittRdtsc m c st true tsc = .fehler .gp := by
  simp [schrittRdtsc, h]

/-- RDTSC without TSD writes the split stamp. -/
theorem schrittRdtsc_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (tsc : Wort) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittRdtsc m c st false tsc = .ok k' st' m.mem ∧
        k'.register .rax = tscTief tsc ∧
        k'.register .rdx = tscHoch tsc := by
  refine ⟨kernMitRegRip (m.kerne c)
    (fun q => match q with
      | .rax => tscTief tsc
      | .rdx => tscHoch tsc
      | _ => (m.kerne c).register q)
    ((m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .rdtsc)),
    st, ?_, ?_, ?_⟩
  · simp [schrittRdtsc]
  · rfl
  · rfl

/-! ## 5. SYSCALL/SYSRET: the fast pair over caller MSR snapshots.
    LSTAR/FMASK arrive as explicit inputs (OS-written, user logic);
    the step computes only the architectural effect (S-SYSCALL,
    S-SYSRET). Neither drains the TSO buffer (S-SYSCALL-KEIN-DRAIN,
    proved as buffer equations at the machine lift). -/

/-- SYSCALL leg: SCE + 64-bit mode else #UD; otherwise RCX takes
    the next RIP, RIP takes LSTAR, R11 takes RFLAGS, RFLAGS is
    masked and CPL falls to 0. -/
def schrittSyscall (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) : SysSnapAusgang :=
  if !ev.sceLang then .fehler .ud
  else
    let k := m.kerne c
    let reg : Register → Wort := fun q =>
      match q with
      | .rcx => k.rip + BitVec.ofNat 64 (sysLaenge .syscall)
      | .r11 => st.rflagsW
      | _ => k.register q
    let rflagsNeu := st.rflagsW &&& ~~~ev.fmask
    .ok (kernMitRegRip k reg ev.lstar)
      ⟨⟨0, st.steuer.iopl, rflagsNeu.getLsbD 9, st.steuer.vm⟩,
        st.halted, rflagsNeu⟩ m.mem

/-- SYSCALL without SCE/64-bit mode is #UD. -/
theorem schrittSyscall_ud (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (h : ev.sceLang = false) :
    schrittSyscall m c st ev = .fehler .ud := by
  simp [schrittSyscall, h]

/-- SYSCALL saves the next RIP in RCX and targets LSTAR at CPL 0. -/
theorem schrittSyscall_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (h : ev.sceLang = true) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittSyscall m c st ev = .ok k' st' m.mem ∧
        k'.register .rcx =
          (m.kerne c).rip + BitVec.ofNat 64 2 ∧
        k'.rip = ev.lstar ∧ st'.steuer.cpl = 0 ∧
        k'.register .r11 = st.rflagsW := by
  refine ⟨kernMitRegRip (m.kerne c)
    (fun q => match q with
      | .rcx => (m.kerne c).rip + BitVec.ofNat 64 (sysLaenge .syscall)
      | .r11 => st.rflagsW
      | _ => (m.kerne c).register q)
    ev.lstar,
    ⟨⟨0, st.steuer.iopl, (st.rflagsW &&& ~~~ev.fmask).getLsbD 9,
      st.steuer.vm⟩, st.halted, st.rflagsW &&& ~~~ev.fmask⟩,
    ?_, ?_, ?_, rfl, ?_⟩
  · simp [schrittSyscall, h]
  · rfl
  · rfl
  · rfl

/-- SYSRET mask: R11 keeps only the restorable RFLAGS bits, bit 1
    reads set (Vol. 2B 4-709: RF/VM cleared, reserved fixed). -/
def sysretMaske : Wort := (0x3C7FD7 : Wort)

/-- SYSRET leg: #UD unless SCE/64-bit, #GP(0) above CPL 0 or on a
    noncanonical RCX (64-bit form); otherwise RIP takes RCX, RFLAGS
    takes the masked R11 and CPL rises to 3. -/
def schrittSysret (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) : SysSnapAusgang :=
  if !ev.sceLang then .fehler .ud
  else if !(st.steuer.cpl = 0) then .fehler .gp
  else
    let k := m.kerne c
    let rcx := k.register .rcx
    if ev.op64 && !istKanonisch rcx then .fehler .gp
    else
      let rflagsNeu := (k.register .r11 &&& sysretMaske) ||| (2 : Wort)
      .ok (kernMitRegRip k k.register rcx)
        ⟨⟨3, st.steuer.iopl, rflagsNeu.getLsbD 9, st.steuer.vm⟩,
          st.halted, rflagsNeu⟩ m.mem

/-- SYSRET without SCE/64-bit mode is #UD. -/
theorem schrittSysret_ud (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (h : ev.sceLang = false) :
    schrittSysret m c st ev = .fehler .ud := by
  simp [schrittSysret, h]

/-- SYSRET above CPL 0 is #GP(0). -/
theorem schrittSysret_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (hs : ev.sceLang = true)
    (h : ¬ st.steuer.cpl = 0) :
    schrittSysret m c st ev = .fehler .gp := by
  simp [schrittSysret, hs, h]

/-- SYSRET to a noncanonical RCX is #GP(0). -/
theorem schrittSysret_rcx_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (hs : ev.sceLang = true)
    (h0 : st.steuer.cpl = 0) (h64 : ev.op64 = true)
    (hk : istKanonisch ((m.kerne c).register .rcx) = false) :
    schrittSysret m c st ev = .fehler .gp := by
  simp [schrittSysret, hs, h0, h64, hk]

/-- SYSRET returns to RCX at CPL 3. -/
theorem schrittSysret_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (hs : ev.sceLang = true)
    (h0 : st.steuer.cpl = 0)
    (hk : ev.op64 = true →
      istKanonisch ((m.kerne c).register .rcx) = true) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittSysret m c st ev = .ok k' st' m.mem ∧
        k'.rip = (m.kerne c).register .rcx ∧
        st'.steuer.cpl = 3 := by
  refine ⟨kernMitRegRip (m.kerne c) (m.kerne c).register
    ((m.kerne c).register .rcx),
    ⟨⟨3, st.steuer.iopl,
      (((m.kerne c).register .r11 &&& sysretMaske) ||| (2 : Wort)).getLsbD 9,
      st.steuer.vm⟩, st.halted,
      ((m.kerne c).register .r11 &&& sysretMaske) ||| (2 : Wort)⟩,
    ?_, rfl, rfl⟩
  simp only [schrittSysret, hs, h0]
  by_cases h64 : ev.op64 = true
  · have hkk := hk h64
    simp [h64, hkk]
  · simp [h64]

/-! ## 6. INT n: software delivery through the accepted pipeline.
    The gate bytes are read from machine memory and the accepted
    `liefere` (with `.softwareInt`, INT1 exempt) is lifted, never
    redefined (S-INT). Delivery alone never drains the TSO buffer
    (S-INT-KEIN-DRAIN, the async S3 analogue). -/

/-- Control snapshot for the accepted pipeline from stored
    control plus the event's IDT/TSS window. -/
def sysSteuerstand (st : SysSteuer) (ev : SysEingaben) : Steuerstand :=
  ⟨ev.idtBasis, ev.idtLimit, ev.tssBasis, ev.tssLimit,
    st.steuer.cpl, st.steuer.ifBit⟩

/-- Software-INT request over the acting core's registers: return
    address past the 2-byte form, no error code. -/
def sysIntAnfrage (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (t : Wort × Wort) : LieferAnfrage :=
  let k := m.kerne c
  ⟨ev.vektor, t, .softwareInt (decide (ev.vektor = 1)),
    ev.codeOk, ev.wechsel, ev.neuDpl, k.register .rsp,
    0, st.rflagsW, 0,
    k.rip + BitVec.ofNat 64 (sysLaenge .intN), none⟩

/-- INT n leg: gate bytes from machine memory, then the accepted
    delivery; faults classify through `torFehlerKlasse`. -/
def schrittInt (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) : SysSnapAusgang :=
  match liesTorBytes m.mem (torAdresse ev.idtBasis ev.vektor) with
  | none => .fehler .gp
  | some t =>
    match liefere m.mem (sysSteuerstand st ev)
        (sysIntAnfrage m c st ev t) with
    | .zugestellt m' ripNeu ifNeu gew =>
      let k := m.kerne c
      let rspNeu := k.register .rsp -
        BitVec.ofNat 64
          (8 * (rahmenWorte (sysIntAnfrage m c st ev t)).length)
      let reg : Register → Wort := fun q =>
        if q = Register.rsp then rspNeu else k.register q
      .ok (kernMitRegRip k reg ripNeu)
        ⟨⟨(if gew then ev.neuDpl else st.steuer.cpl),
          st.steuer.iopl, ifNeu, st.steuer.vm⟩,
          st.halted, st.rflagsW⟩ m'
    | .lieferFehler f _ => .fehler (torFehlerKlasse f)

/-- INT delivery agrees with the accepted pipeline: the same
    request delivers the same memory, handler RIP and IF. -/
theorem schrittInt_liefert (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (t : Wort × Wort) (m' : Speicher)
    (ripNeu : Adresse) (ifNeu gew : Bool)
    (hbytes : liesTorBytes m.mem (torAdresse ev.idtBasis ev.vektor) =
      some t)
    (h : liefere m.mem (sysSteuerstand st ev)
        (sysIntAnfrage m c st ev t) =
        .zugestellt m' ripNeu ifNeu gew) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittInt m c st ev = .ok k' st' m' ∧ k'.rip = ripNeu ∧
        st'.steuer.ifBit = ifNeu := by
  refine ⟨kernMitRegRip (m.kerne c)
    (fun q => if q = Register.rsp then
      (m.kerne c).register .rsp - BitVec.ofNat 64
        (8 * (rahmenWorte (sysIntAnfrage m c st ev t)).length)
      else (m.kerne c).register q)
    ripNeu,
    ⟨⟨(if gew then ev.neuDpl else st.steuer.cpl),
      st.steuer.iopl, ifNeu, st.steuer.vm⟩,
      st.halted, st.rflagsW⟩, ?_, rfl, rfl⟩
  simp [schrittInt, hbytes, h]

/-- INT faults agree with the accepted pipeline's fault. -/
theorem schrittInt_fehler (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (t : Wort × Wort) (f : TorFehler)
    (code : Wort)
    (hbytes : liesTorBytes m.mem (torAdresse ev.idtBasis ev.vektor) =
      some t)
    (h : liefere m.mem (sysSteuerstand st ev)
        (sysIntAnfrage m c st ev t) = .lieferFehler f code) :
    schrittInt m c st ev = .fehler (torFehlerKlasse f) := by
  simp [schrittInt, hbytes, h]

/-- INT at CPL 3 against a DPL-0 gate is #GP (accepted DPL rule). -/
theorem schrittInt_dpl_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ev : SysEingaben) (t : Wort × Wort) (g : IdtTor)
    (hbytes : liesTorBytes m.mem (torAdresse ev.idtBasis ev.vektor) =
      some t)
    (hlim : torImLimit ev.idtLimit ev.vektor = true)
    (hz : zerlegeTor t = .ok g)
    (hd : dplZugelassen (.softwareInt false) g.dpl st.steuer.cpl =
      false)
    (h1 : ¬ ev.vektor = 1) :
    schrittInt m c st ev = .fehler .gp := by
  have hp : pruefeTor ev.vektor ev.idtLimit t
      (Herkunft.softwareInt (decide (ev.vektor = 1))) st.steuer.cpl
      ev.codeOk = .fehler (.dplFehler ev.vektor) := by
    have hd1 : decide (ev.vektor = 1) = false := by
      simp [h1]
    have hd2 : (Herkunft.softwareInt (decide (ev.vektor = 1))) =
        (Herkunft.softwareInt false) := by
      rw [hd1]
    rw [hd2]
    exact pruefeTor_dpl ev.vektor ev.idtLimit t st.steuer.cpl
      ev.codeOk g hlim hz hd
  have hl : liefere m.mem (sysSteuerstand st ev)
      (sysIntAnfrage m c st ev t) =
      .lieferFehler (.dplFehler ev.vektor)
        (torFehlerCode (.dplFehler ev.vektor)
          (Herkunft.softwareInt (decide (ev.vektor = 1)))) := by
    apply liefere_prueft_zuerst
    simp only [sysIntAnfrage, sysSteuerstand]
    exact hp
  have hs := schrittInt_fehler m c st ev t (.dplFehler ev.vektor)
    (torFehlerCode (.dplFehler ev.vektor)
      (Herkunft.softwareInt (decide (ev.vektor = 1)))) hbytes hl
  simp [torFehlerKlasse] at hs
  exact hs

/-! ## 7. IRET: return through the pushed frame.
    The five words the delivery pushed (SS:RSP:RFLAGS:CS:RIP, no
    error code on the software path) are read back with the accepted
    `read64` chain: unreadable stack is #SS, a noncanonical popped
    RIP is #GP. CPL follows the popped CS RPL; IF follows the popped
    RFLAGS bit 9 where CPL ≤ IOPL and is kept otherwise (the
    POPF-gating shape of `ArchitecturalFlags`, lifted minimally).
    Selector validation, task switches and error-code frames are NOT
    modelled (CUTS). -/

/-- IRET leg: pop the five-word frame and resume it. -/
def schrittIret (m : HwMaschine) (c : Nat) (st : SysSteuer) :
    SysSnapAusgang :=
  let k := m.kerne c
  let rsp := k.register .rsp
  match read64 m.mem rsp with
  | none => .fehler .ss
  | some _ss =>
    match read64 m.mem (addrOff rsp 8) with
    | none => .fehler .ss
    | some rspNeu =>
      match read64 m.mem (addrOff rsp 16) with
      | none => .fehler .ss
      | some rflagsGesp =>
        match read64 m.mem (addrOff rsp 24) with
        | none => .fehler .ss
        | some cs =>
          match read64 m.mem (addrOff rsp 32) with
          | none => .fehler .ss
          | some ripNeu =>
            if !istKanonisch ripNeu then .fehler .gp
            else
              let cplNeu := cs.toNat % 4
              let ifNeu := if cplNeu ≤ st.steuer.iopl then
                rflagsGesp.getLsbD 9 else st.steuer.ifBit
              let reg : Register → Wort := fun q =>
                if q = Register.rsp then rspNeu
                else k.register q
              .ok (kernMitRegRip k reg ripNeu)
                ⟨⟨cplNeu, st.steuer.iopl, ifNeu, st.steuer.vm⟩,
                  st.halted, rflagsGesp⟩ m.mem

/-- IRET past an unreadable stack word is #SS. -/
theorem schrittIret_ss (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (h : read64 m.mem ((m.kerne c).register .rsp) = none) :
    schrittIret m c st = .fehler .ss := by
  simp [schrittIret, h]

/-- IRET to a noncanonical popped RIP is #GP. -/
theorem schrittIret_rip_gp (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ss rspNeu rflagsGesp cs ripNeu : Wort)
    (h0 : read64 m.mem ((m.kerne c).register .rsp) = some ss)
    (h1 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 8) = some rspNeu)
    (h2 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 16) = some rflagsGesp)
    (h3 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 24) = some cs)
    (h4 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 32) = some ripNeu)
    (hk : istKanonisch ripNeu = false) :
    schrittIret m c st = .fehler .gp := by
  simp [schrittIret, h0, h1, h2, h3, h4, hk]

/-- IRET resumes the popped frame: RIP, RSP, CPL from CS.RPL. -/
theorem schrittIret_ok (m : HwMaschine) (c : Nat) (st : SysSteuer)
    (ss rspNeu rflagsGesp cs ripNeu : Wort)
    (h0 : read64 m.mem ((m.kerne c).register .rsp) = some ss)
    (h1 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 8) = some rspNeu)
    (h2 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 16) = some rflagsGesp)
    (h3 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 24) = some cs)
    (h4 : read64 m.mem
      (addrOff ((m.kerne c).register .rsp) 32) = some ripNeu)
    (hk : istKanonisch ripNeu = true) :
    ∃ k' : HwKern, ∃ st' : SysSteuer,
      schrittIret m c st = .ok k' st' m.mem ∧
        k'.rip = ripNeu ∧
        k'.register .rsp = rspNeu ∧
        st'.steuer.cpl = cs.toNat % 4 := by
  refine ⟨kernMitRegRip (m.kerne c)
    (fun q => if q = Register.rsp then rspNeu
      else (m.kerne c).register q)
    ripNeu,
    ⟨⟨cs.toNat % 4, st.steuer.iopl,
      (if cs.toNat % 4 ≤ st.steuer.iopl then rflagsGesp.getLsbD 9
        else st.steuer.ifBit),
      st.steuer.vm⟩, st.halted, rflagsGesp⟩, ?_, rfl, ?_, rfl⟩
  · simp [schrittIret, h0, h1, h2, h3, h4, hk]
  · simp [kernMitRegRip]

end Gabbro.Grammatik.X86
