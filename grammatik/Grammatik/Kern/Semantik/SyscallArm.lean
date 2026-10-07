/-
  File:      Grammatik/Kern/Semantik/SyscallArm.lean
  Subject:   THE AArch64 LINUX SYSTEM-CALL ABI AS DATA, and the AArch64 counterparts of the
             stack-alignment premises of `tor.trampolin` / `tor.kind` / `start.nolibc`.

  Agent D of the AArch64 direction (Simon's decision: x86 work stops, the next target is
  AArch64). This file MIRRORS `Syscall.lean` (`SysReg`, `SysAbi`, `schreibAbi`) and the
  `FadenLaufzeit` / `start.nolibc` alignment premises of `Bausteine/Schablonen/`; it edits none of
  them, and no existing x86 statement moves. Everything lives in the namespace `Arm`.

  The agreed ABI: `arch aarch64`; call number in `x8`; arguments in `x0 .. x5`; result in `x0`
  (a negative errno as a signed value); the instruction `svc #0`; the kernel preserves every
  register except `x0`. Stack 16-byte aligned at every public interface (AAPCS64); callee-saved
  `x19 .. x28`, `x29`, `x30`.

  * §1 the register set (`x0 .. x30`, `sp`) and the flag state `NZCV`;
  * §2 `SysAbiArm` (number register, argument map, result register, clobbers) with
    well-formedness; the Linux numbers as constants;
  * §3 the `write` ABI, and a concrete register assignment for a `write` call (the witness);
  * §4 the AArch64 stack-alignment premises: `sp` 16-aligned at the callee's first instruction
    (`bl` pushes nothing, it writes `x30`), against x86's `rsp + 8`.
-/

namespace Gabbro.Grammatik

namespace Arm

/-! ## 1. Registers and flags -/

/-- The AArch64 general registers a syscall stub can name: `x0 .. x30` and the stack pointer.
    (`xzr` is not a register one can bind: it reads as zero and discards writes.) -/
inductive ArmReg where
  | x (n : Fin 31)
  | sp
  deriving DecidableEq, Repr

/-- The condition flags `NZCV`. They are part of the machine state; the agreed Linux ABI says
    nothing about them across `svc`, and this file does NOT claim they are preserved. -/
structure Flags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr

/-- A register state: 64-bit values as naturals (reduced mod 2^64 where a result is written),
    plus the flags. -/
structure ArmZustand where
  reg : ArmReg → Nat
  flags : Flags

/-- The register `x_n` for a literal. -/
abbrev xr (n : Nat) (h : n < 31 := by decide) : ArmReg := .x ⟨n, h⟩

/-- The callee-saved registers of AAPCS64: `x19 .. x28`, `x29`, `x30`. -/
def calleeSaved : List ArmReg :=
  (List.range 12).filterMap fun i =>
    if h : 19 + i < 31 then some (.x ⟨19 + i, h⟩) else none

/-! ## 2. The ABI record -/

/-- `SysAbiArm`: the machine side of one AArch64 `syscall` declaration. Differs from the x86
    `SysAbi` by one field: the call number travels in a register (`x8`) the declaration names,
    where x86 fixes it in `rax`, which is also the answer register. -/
structure SysAbiArm where
  /-- The call number dispatched on. -/
  nummer : Nat
  /-- The register the number is loaded into. -/
  nummerReg : ArmReg
  /-- Input map: `(register, parameter index)` pairs. -/
  ein : List (ArmReg × Nat)
  /-- Output register carrying the raw signed return value. -/
  aus : ArmReg
  /-- Clobbered registers. -/
  clobber : List ArmReg
  deriving DecidableEq, Repr

/-- Well-formedness: input registers pairwise distinct, no parameter bound twice, the number
    register is no input register, and the output register is not clobbered. -/
def SysAbiArm.gut (a : SysAbiArm) : Prop :=
  (a.ein.map Prod.fst).Nodup ∧ (a.ein.map Prod.snd).Nodup ∧
    a.nummerReg ∉ a.ein.map Prod.fst ∧ a.aus ∉ a.clobber

instance (a : SysAbiArm) : Decidable a.gut :=
  inferInstanceAs (Decidable
    ((a.ein.map Prod.fst).Nodup ∧ (a.ein.map Prod.snd).Nodup ∧
      a.nummerReg ∉ a.ein.map Prod.fst ∧ a.aus ∉ a.clobber))

/-- The Linux AArch64 argument registers `x0 .. x5`, in order. -/
def argRegs : List ArmReg := [xr 0, xr 1, xr 2, xr 3, xr 4, xr 5]

/-- The call-number register, `x8`. -/
def nummerRegLinux : ArmReg := xr 8

/-- The result register, `x0`. -/
def ergebnisReg : ArmReg := xr 0

/-- The Linux AArch64 call numbers of the agreed list (asm-generic table). -/
def nrRead : Nat := 63
def nrWrite : Nat := 64
def nrOpenat : Nat := 56
def nrClose : Nat := 57
def nrMmap : Nat := 222
def nrMunmap : Nat := 215
def nrMprotect : Nat := 226
def nrMadvise : Nat := 233
def nrExit : Nat := 93
def nrExitGroup : Nat := 94
def nrClone : Nat := 220
def nrFutex : Nat := 98
def nrSchedYield : Nat := 124
def nrClockGettime : Nat := 113

/-- The numbers are pairwise distinct (a table with a repeated number would make two gates
    the same call). -/
theorem nummern_verschieden :
    [nrRead, nrWrite, nrOpenat, nrClose, nrMmap, nrMunmap, nrMprotect, nrMadvise, nrExit,
      nrExitGroup, nrClone, nrFutex, nrSchedYield, nrClockGettime].Nodup := by decide

/-- A Linux AArch64 gate over the first `k` argument registers: number in `x8`, arguments
    `x0 .. x_{k-1}` as parameters `0 .. k-1`, answer in `x0`, nothing clobbered (the kernel
    preserves every register except `x0`). -/
def linuxAbi (nr k : Nat) : SysAbiArm :=
  { nummer := nr
    nummerReg := nummerRegLinux
    ein := (argRegs.take k).zip (List.range k)
    aus := ergebnisReg
    clobber := [] }

/-- The six argument registers are pairwise distinct. -/
theorem argRegs_verschieden : argRegs.Nodup := by decide

/-- None of the six argument registers is `x8`. -/
theorem argRegs_nicht_x8 : nummerRegLinux ∉ argRegs := by decide

/-- The number register is not the result register. -/
theorem nummerReg_nicht_ergebnis : nummerRegLinux ≠ ergebnisReg := by decide

/-- The argument registers and the number register are outside the callee-saved set
    `x19 ..`, so a stub that loads them destroys nothing the caller keeps in AAPCS64
    registers. -/
theorem argRegs_nicht_calleeSaved : ∀ r ∈ argRegs ++ [nummerRegLinux], r ∉ calleeSaved := by
  decide

/-- Every `linuxAbi nr k` with `k ≤ 6` is well-formed, for every number: the argument registers
    are distinct, `x8` is none of them, and nothing is clobbered. -/
theorem linuxAbi_gut (nr : Nat) : ∀ k, k ≤ 6 → (linuxAbi nr k).gut := by
  intro k hk
  -- `gut` does not read the number, so the instance at `nr = 0` is the same proposition.
  suffices h : (linuxAbi 0 k).gut from h
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 3. `write`, and a witness -/

/-- `write(fd, buf, len)`: number 64, three arguments in `x0, x1, x2`, answer in `x0`. -/
def schreibAbiArm : SysAbiArm := linuxAbi nrWrite 3

/-- `schreibAbiArm` is exactly what one writes out by hand. -/
theorem schreibAbiArm_wert :
    schreibAbiArm =
      { nummer := 64, nummerReg := xr 8
        ein := [(xr 0, 0), (xr 1, 1), (xr 2, 2)]
        aus := xr 0, clobber := [] } := by decide

theorem schreibAbiArm_gut : schreibAbiArm.gut := by decide

/-- The register assignment a stub establishes before `svc #0`: the number in its register,
    each bound input register holding its argument; every other register as the caller had it
    (`vorher`). -/
def ladeAufruf (a : SysAbiArm) (vorher : ArmZustand) (args : Nat → Nat) : ArmZustand :=
  { reg := fun r =>
      if r = a.nummerReg then a.nummer
      else match a.ein.find? (fun p => decide (p.1 = r)) with
        | some p => args p.2
        | none => vorher.reg r
    flags := vorher.flags }

/-- The kernel side of `svc #0`: the (signed) answer, reduced mod 2^64, in `x0`; every other
    register and the flags exactly as they were. This is the AGREED ABI stated as a function,
    not a statement about any kernel. -/
def nachSvc (vorher : ArmZustand) (antwort : Int) : ArmZustand :=
  { reg := fun r => if r = ergebnisReg then (antwort % 18446744073709551616).toNat
                    else vorher.reg r
    flags := vorher.flags }

/-- A concrete caller state: `x_n` holds `1000 + n`, `sp` holds `0x7ffc1000`, flags clear. -/
def beispielVorher : ArmZustand :=
  { reg := fun r => match r with
      | .x n => 1000 + n.val
      | .sp => 0x7ffc1000
    flags := ⟨false, false, false, false⟩ }

/-- The arguments of the witness call `write(1, 0x4000, 5)`. -/
def beispielArgs : Nat → Nat := fun i => [1, 0x4000, 5].getD i 0

/-- **Witness (non-degenerate):** `write(1, 0x4000, 5)` as a concrete register assignment: the
    number 64 in `x8`, `fd = 1` in `x0`, `buf = 0x4000` in `x1`, `len = 5` in `x2`, and an
    unrelated callee-saved register (`x19`) and the stack pointer untouched. -/
theorem schreibAufruf_zeuge :
    let s := ladeAufruf schreibAbiArm beispielVorher beispielArgs
    s.reg nummerRegLinux = 64 ∧ s.reg (xr 0) = 1 ∧ s.reg (xr 1) = 0x4000 ∧
    s.reg (xr 2) = 5 ∧ s.reg (xr 19) = 1019 ∧ s.reg .sp = 0x7ffc1000 := by
  decide

/-- The kernel keeps every register but `x0`: after `svc #0` answering `5`, `x0 = 5`, `x8` is
    still 64 and `x19` is untouched. -/
theorem svc_zeuge :
    let s := ladeAufruf schreibAbiArm beispielVorher beispielArgs
    let t := nachSvc s 5
    t.reg ergebnisReg = 5 ∧ t.reg nummerRegLinux = 64 ∧ t.reg (xr 19) = 1019 := by
  decide

/-- A negative errno (`-9`, EBADF) lands in `x0` as its two's complement, 2^64 - 9. -/
theorem svc_errno_zeuge :
    (nachSvc beispielVorher (-9)).reg ergebnisReg = 18446744073709551607 := by decide

/-- The frame law, for every state and answer: `svc` changes `x0` and nothing else. -/
theorem nachSvc_rahmen (vorher : ArmZustand) (antwort : Int) (r : ArmReg)
    (h : r ≠ ergebnisReg) : (nachSvc vorher antwort).reg r = vorher.reg r := by
  simp [nachSvc, h]

/-- ... and `x0` carries the answer mod 2^64. -/
theorem nachSvc_ergebnis (vorher : ArmZustand) (antwort : Int) :
    (nachSvc vorher antwort).reg ergebnisReg = (antwort % 18446744073709551616).toNat := by
  simp [nachSvc]

/-! ## 4. The stack-alignment premises, AArch64 -/

/-- Round the stack pointer down to 16 (`and sp, x, #-16`). -/
def ausrichtenArm (sp : Nat) : Nat := sp - sp % 16

/-- The AArch64 counterpart of `start.nolibc`. At process entry the Linux kernel hands a 16-byte
    aligned `sp`; the stub still rounds it down and `bl main` pushes nothing (it writes the
    return address into `x30`). The AAPCS64 entry condition is `sp % 16 = 0` AT the callee's
    first instruction, against x86's `(rsp + 8) % 16 = 0`. -/
structure StartLaufArm where
  spEintritt : Nat
  ud2 : Bool

def startLaufArm (sp : Nat) (mainKehrtZurueck : Bool) : StartLaufArm where
  spEintritt := ausrichtenArm sp
  ud2 := mainKehrtZurueck

/-- **Counterpart of `start_nolibc`.** With a stack pointer of at least 16 (the loader, premise
    (d) as for x86) and `main` not returning: `sp` at `main`'s first instruction is 16-aligned,
    not above the kernel's `sp` (so `argc/argv/envp` above it stay intact), and the trap
    (`brk` for `ud2`) never runs. The x86 theorem's strict `< rsp` for the return address has
    no counterpart: the return address lives in `x30`, not on the stack. -/
theorem start_nolibc_arm (sp : Nat) (hsp : 16 ≤ sp) (mainKehrtZurueck : Bool)
    (hnie : mainKehrtZurueck = false) :
    (startLaufArm sp mainKehrtZurueck).spEintritt % 16 = 0 ∧
    (startLaufArm sp mainKehrtZurueck).spEintritt ≤ sp ∧
    sp < (startLaufArm sp mainKehrtZurueck).spEintritt + 16 ∧
    (startLaufArm sp mainKehrtZurueck).ud2 = false := by
  simp only [startLaufArm, ausrichtenArm]
  refine ⟨?_, ?_, ?_, hnie⟩ <;> omega

theorem start_nolibc_arm_ud2 (sp : Nat) : (startLaufArm sp true).ud2 = true := rfl

/-- Witness: the same 8-aligned-only pointer as `start_nolibc_zeuge` (`0x7ffc12345678`). -/
theorem start_nolibc_arm_zeuge :
    (startLaufArm 0x7ffc12345678 false).spEintritt % 16 = 0 ∧
    (startLaufArm 0x7ffc12345678 false).spEintritt ≤ 0x7ffc12345678 ∧
    0x7ffc12345678 < (startLaufArm 0x7ffc12345678 false).spEintritt + 16 ∧
    (startLaufArm 0x7ffc12345678 false).ud2 = false :=
  start_nolibc_arm 0x7ffc12345678 (by decide) false rfl

/-- The child of a clone with a handed stack: `sp` is the handed top and the stack register
    still holds it (as in `FadenLaufzeit.KindRegs`; on AArch64 the stack register is an
    ordinary `x_n`, bound in `regs in`, neither the answer nor `x8`). -/
structure KindRegsArm where
  sp : Nat
  stapelReg : Nat

def kindNachSvc (v : Nat) : KindRegsArm := { sp := v, stapelReg := v }

structure KindRufArm where
  argument : Nat
  spEintritt : Nat
  ud2 : Bool

/-- `mov x0, stack; and sp, sp, #-16; bl gabbro_kind_<nr>; brk`. -/
def kindRufArm (r : KindRegsArm) (regionKehrtZurueck : Bool) : KindRufArm :=
  { argument := r.stapelReg, spEintritt := ausrichtenArm r.sp, ud2 := regionKehrtZurueck }

/-- **Counterpart of `kind_region`.** For a handed top of at least 16 and a region that does not
    return: the argument is the handed value, `sp` at entry is 16-aligned (x86: `rsp + 8`
    16-aligned), inside the carved stack (within 16 bytes under the handed top, not above it --
    x86's entry is strictly below because `call` pushes 8; `bl` pushes nothing), and the trap
    never runs. -/
theorem kind_region_arm (v : Nat) (hv : 16 ≤ v) (regionKehrtZurueck : Bool)
    (hnie : regionKehrtZurueck = false) :
    (kindRufArm (kindNachSvc v) regionKehrtZurueck).argument = v ∧
    (kindRufArm (kindNachSvc v) regionKehrtZurueck).spEintritt % 16 = 0 ∧
    (kindRufArm (kindNachSvc v) regionKehrtZurueck).spEintritt ≤ v ∧
    v < (kindRufArm (kindNachSvc v) regionKehrtZurueck).spEintritt + 16 ∧
    (kindRufArm (kindNachSvc v) regionKehrtZurueck).ud2 = false := by
  refine ⟨rfl, ?_, ?_, ?_, hnie⟩ <;> simp only [kindRufArm, kindNachSvc, ausrichtenArm] <;> omega

theorem kind_region_arm_rueckkehr (v : Nat) : (kindRufArm (kindNachSvc v) true).ud2 = true := rfl

/-- Witness: the 64 KiB stack of `kind_region_zeuge`, plus an 8-aligned-only top. -/
theorem kind_region_arm_zeuge :
    (kindRufArm (kindNachSvc 0x7f0000010000) false).argument = 0x7f0000010000 ∧
    (kindRufArm (kindNachSvc 0x7f0000010000) false).spEintritt % 16 = 0 ∧
    (kindRufArm (kindNachSvc 0x7f0000010008) false).spEintritt % 16 = 0 ∧
    (kindRufArm (kindNachSvc 0x7f0000010008) false).spEintritt ≤ 0x7f0000010008 ∧
    (kindRufArm (kindNachSvc 0x7f0000010000) false).ud2 = false := by
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> decide

/-- The two-call child path of `tor.trampolin` (root, then the end), AArch64: each callee is
    entered with the same aligned `sp` (`bl` pushes nothing, so the second call sees the same
    `sp` once the first returned). The registers holding the two targets survive the gate only
    if the gate preserves them -- the same `C187` premise as x86, stated there. -/
def kindPfadArm (spitze kind ende : Nat) (endeKehrtZurueck : Bool) :
    List (Nat × Nat) × Bool :=
  let a := ausrichtenArm spitze
  ([(kind, a), (ende, a)], endeKehrtZurueck)

/-- **Counterpart of `trampolin_kind`** (the entry-alignment half; the register-preservation
    half is about the gate's contract and is unchanged). -/
theorem trampolin_kind_arm (spitze kind ende : Nat) (hsp : 16 ≤ spitze)
    (endeKehrtZurueck : Bool) (hnie : endeKehrtZurueck = false) :
    (kindPfadArm spitze kind ende endeKehrtZurueck).1.map Prod.fst = [kind, ende] ∧
    (∀ z ∈ (kindPfadArm spitze kind ende endeKehrtZurueck).1,
      z.2 % 16 = 0 ∧ z.2 ≤ spitze ∧ spitze < z.2 + 16) ∧
    (kindPfadArm spitze kind ende endeKehrtZurueck).2 = false := by
  refine ⟨rfl, ?_, hnie⟩
  intro z hz
  simp only [kindPfadArm, ausrichtenArm, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with h | h <;> subst h <;> simp only <;> omega

theorem trampolin_kind_arm_zeuge :
    (kindPfadArm 0x7f0000010008 0x401000 0x402000 false).1.map Prod.fst = [0x401000, 0x402000] ∧
    (∀ z ∈ (kindPfadArm 0x7f0000010008 0x401000 0x402000 false).1,
      z.2 % 16 = 0 ∧ z.2 ≤ 0x7f0000010008 ∧ 0x7f0000010008 < z.2 + 16) ∧
    (kindPfadArm 0x7f0000010008 0x401000 0x402000 false).2 = false :=
  trampolin_kind_arm _ _ _ (by decide) false rfl

end Arm

/- CUTS: what is NOT claimed.
   - This MODELS the agreed AArch64 Linux ABI as data and states AArch64 alignment premises; it
     proves nothing about hardware or about the kernel. `nachSvc` IS the agreed ABI ("only `x0`
     changes"), not a theorem about Linux. The flags are carried but their preservation across
     `svc` is not claimed.
   - The Linux numbers are the asm-generic table as agreed with Agent C; nothing here checks
     them against a kernel.
   - No machine-G / `Programm` / `Ax` wiring: `SysAbiArm` is not yet accepted by `Ax`, which
     holds the x86 `SysAbi`. The generalisation (`SysAbi` over a register type) is in
     `messung/ARM-KOMPATIBILITAET-D.md`; it would edit `Syscall.lean`, `SyscallPaarung.lean`,
     `CloneHandoff.lean` and is not done here.
   - `CloneAbi` (the handed-stack shape) has no AArch64 counterpart yet; only the alignment
     premises of the templates are mirrored. `faden_warte_korrekt` and the futex template are
     architecture-neutral (see the report) and untouched.
   - Not a model of AArch64 instruction execution: no `svc` decoding, no exception levels.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.Arm.nummern_verschieden
#print axioms Gabbro.Grammatik.Arm.argRegs_verschieden
#print axioms Gabbro.Grammatik.Arm.argRegs_nicht_x8
#print axioms Gabbro.Grammatik.Arm.nummerReg_nicht_ergebnis
#print axioms Gabbro.Grammatik.Arm.argRegs_nicht_calleeSaved
#print axioms Gabbro.Grammatik.Arm.linuxAbi_gut
#print axioms Gabbro.Grammatik.Arm.schreibAbiArm_wert
#print axioms Gabbro.Grammatik.Arm.schreibAbiArm_gut
#print axioms Gabbro.Grammatik.Arm.schreibAufruf_zeuge
#print axioms Gabbro.Grammatik.Arm.svc_zeuge
#print axioms Gabbro.Grammatik.Arm.svc_errno_zeuge
#print axioms Gabbro.Grammatik.Arm.nachSvc_rahmen
#print axioms Gabbro.Grammatik.Arm.nachSvc_ergebnis
#print axioms Gabbro.Grammatik.Arm.start_nolibc_arm
#print axioms Gabbro.Grammatik.Arm.start_nolibc_arm_zeuge
#print axioms Gabbro.Grammatik.Arm.kind_region_arm
#print axioms Gabbro.Grammatik.Arm.kind_region_arm_zeuge
#print axioms Gabbro.Grammatik.Arm.trampolin_kind_arm
#print axioms Gabbro.Grammatik.Arm.trampolin_kind_arm_zeuge
