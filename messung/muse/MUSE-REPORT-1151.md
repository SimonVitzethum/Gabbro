# MUSE-REPORT-1151: Privileged/system instructions for OS and freestanding profiles

## What was done

New file `grammatik/Grammatik/X86/HwSystemForms.lean` (~1400 lines) plus one
`import Grammatik.X86.HwSystemForms` line in `grammatik/Grammatik.lean`.
No other file touched. The ten-form family (HLT, CLI/STI, PAUSE, CPUID,
RDTSC, INT n, IRET, SYSCALL/SYSRET) is connected to the coherent machine
(`HardwareExecution.lean` §11) reusing accepted definitions unchanged:
`HwMaschine`/`HwSchritt`/`HwWf`/`HwAdapter`/`verweigertAdapter`,
`ArchFehler` (`HardwareFaults.lean`), `pruefeTor`/`waehleStapel`/
`schiebeRahmen`/`rahmenWorte`/`liesTorBytes`/`torAdresse`
(`InterruptDescriptorHardware.lean`), `Steuer` (`ArchitecturalFlags.lean`),
`witMem`/`loWit`/`idtWitSteuer` (accepted IDT/TSS witness), TSO
`issueByte`/`loadByte`/`flushKern`, `basisHw`/`basisBereit`.

Key definitions/theorems (all in `Gabbro.Grammatik.X86`):
- `SysFormArt`, `sysLaenge` + `sysLaenge_pins` (opcode-table lengths).
- `SysProfilArt` (`gehostet`/`freistehend`), `formFrei` (freestanding
  refuses exactly SYSCALL/SYSRET) + equations.
- `SysSteuer` (canonical `Steuer` + HLT bit + RFLAGS word), `SysMaschine`
  (coherent machine + per-core control), `SysWf` (lifts `HwWf`).
- `SysEingaben` (explicit caller inputs: MSR snapshots, leaf answers,
  TSC, TSD, IDT/TSS window), `SysEreignis`, `SysAusgang`
  (ok / `ArchFehler` / refused), `torFehlerKlasse` (stack faults to
  #SS, all other descriptor faults to #GP) + equations.
- Ten legs with effect and fault theorems: `schrittHlt`
  (`schrittHlt_ok`, `schrittHlt_gp`), `schrittIf`
  (`schrittIf_cli_ok`, `schrittIf_sti_ok`, `schrittIf_gp`),
  `schrittPause` (`schrittPause_still`), `schrittCpuid`
  (`schrittCpuid_rax`), `schrittRdtsc`
  (`schrittRdtsc_gp`, `schrittRdtsc_ok`), `schrittSyscall`
  (`schrittSyscall_ud`, `schrittSyscall_ok`), `schrittSysret`
  (`schrittSysret_ud`, `schrittSysret_gp`, `schrittSysret_rcx_gp`,
  `schrittSysret_ok`), staged `schrittInt`/`schrittIntFertig`
  (`schrittInt_liefert`, `schrittInt_torfehler`,
  `schrittInt_stapelfehler`, `schrittInt_dpl_gp`,
  `schrittInt_gate_unlesbar`), `schrittIret`
  (`schrittIret_ss`, `schrittIret_rip_gp`, `schrittIret_ok`).
- `sysSnapSchritt` (dispatcher), `sysInstalliert` (+ buffer/profile/wf
  lemmas), `sysAusfuehren` (absent profile form = #UD) with
  `sysAusfuehren_ud`, `sysAusfuehren_syscall_freistehend`,
  `sysAusfuehren_wf`, `sysAusfuehren_puffer` (no leg drains any TSO
  buffer: machine side of S-SERIAL).
- `adapterSystem : HwAdapter (SysSteuer × SysEreignis)` with
  `adapterSystem_ok`, `adapterSystem_fehler`.
- `SysSchritt` (sync embeds `HwSchritt` exactly) with
  `sysSchritt_sync_einbetten`, `sysSchritt_sync_nur`,
  `sysSchritt_wf`, `sysSchritt_sys_puffer`.
- Witness: `sysWitStart` (accepted IDT/TSS memory, CPL 0), core-0
  chain CLI/STI/CPUID/RDTSC/SYSCALL/INT, core-1 INT then HLT, 21
  closed `decide` observations (handler 0x2000 on both cores,
  IF cleared, RSP 16344, little-endian frame bytes in memory,
  six refusals), TSO issue/forward/drain 0 -> 42, all joined in
  `sysWit_zeuge`.

Findings during the work (both repaired, not downgraded):
1. First INT draft restored RSP from the *old* stack instead of the
   *selected* stack on privilege switch. Rewrote the leg in accepted
   stages (`pruefeTor`/`waehleStapel`/`schiebeRahmen`) mirroring
   `asyncSchritt`; agreement theorems bridge to the same outcomes.
2. `TorFehler.nichtVorhanden` (#NP) and `tssFehler` (#TS) have no
   member in `ArchFehler`; they map to #GP, recorded in CUTS.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwSystemForms.lean`:
  `== 0 error(s)`, no warnings.
- `./lean-bau`: `Build completed successfully (608 jobs)`.
  First attempt failed with `failed to create thread` (resource
  starvation, no proof content involved); retry passed unchanged.
- `#print axioms` for all 18 main theorems: within
  `propext, Classical.choice, Quot.sound` only (most use a subset).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file.
- Every theorem uses all its premises (no `intro _`/`have _ :=`;
  tuple-projection fragility avoided via the `CpuIdAntwort` struct
  and explicit witnesses throughout).

## What remains open (see CUTS in the file)

No hardware correspondence beyond self-consistency + SDM provenance;
PVI/VME/VIF refinement; serialisation-to-W/GX bridge (assumptions
S-SERIAL-* named, buffers proved untouched); #NP/#TS folded to #GP;
IRET always-five-word frame without selector/task-switch checks;
SYSCALL/SYSRET 64-bit non-FRED only, no CET; INT non-FRED with INT1
exemption; HLT wakeup with the interrupt lane; no RFLAGS-word to
six-flag coherence link; environment inputs (TSC, leaves, MSRs) are
caller data, never silicon claims.

## What I believe is wrong in the task (minor)

Nothing blocking. Two notes: (a) the task's "buffered store visible
via forwarding to the owner only" is demonstrated with an explicit
TSO issue/load/flush stage after delivery, since no system form
itself issues TSO stores -- that stage is witness scaffolding, not a
family effect; (b) `HwRegAusgang` mentioned in the task was
superseded in-tree by `HwFehlerAusgang`/`PrioritaetsFehler`; the file
reuses the newer accepted fault outcome vocabulary plus `ArchFehler`
classes, which is the same requirement with the current names.
