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

end Gabbro.Grammatik.X86
