/-
  File:      Grammatik/Kern/Semantik/SyscallArmLinux.lean
  Subject:   THE GATES OF `bibliothek/linux/linux-aarch64.gab` AS `SysAbiArm` VALUES, with the
             register-map facts the Rust checker's `arch aarch64` rows rely on.

  Agent C of the AArch64 direction. `SyscallArm.lean` (agent D) states the agreed ABI as data
  (`linuxAbi nr k`); this file states, for EACH gate the AArch64 binding declares, the exact
  `SysAbiArm` that its `abi linux arch aarch64 number N / regs in {...} / regs out {x0} /
  clobbers {}` clause denotes, and proves it well-formed. `crates/gabbro-check/tests/arm_abi.rs`
  holds the SAME numbers against `linux-aarch64.gab` and against `SyscallArm.lean` by text, so
  the Rust table, the binding and this model cannot drift apart unnoticed.

  The one gate that is not `linuxAbi nr k` is `clone`: AArch64's raw
  `clone(flags, stack, parent_tid, tls, child_tid)` takes the child's tid word in `x4`, not in
  the fourth argument register (x86_64: `r10`, with `tls` in `r8`). Its gate binds
  `x0, x1, x2, x4`; `x3` (the `tls` register) is unbound because no `CLONE_SETTLS` flag is set.

  NOT here (see `messung/ARM-KOMPATIBILITAET-C.md`): wiring `SysAbiArm` into `Ax`/machine G,
  which holds the x86 `SysAbi`.
-/
import Grammatik.Kern.Semantik.SyscallArm

namespace Gabbro.Grammatik

namespace Arm

/-- `linux_os_mmap(addr, len, prot, flags, fd, off)`. -/
def gateMmap : SysAbiArm := linuxAbi nrMmap 6
/-- `linux_os_mprotect(addr, len, prot)`. -/
def gateMprotect : SysAbiArm := linuxAbi nrMprotect 3
/-- `linux_os_write(fd, buf, len)`. -/
def gateWrite : SysAbiArm := linuxAbi nrWrite 3
/-- `linux_os_exit_group(code)`. -/
def gateExitGroup : SysAbiArm := linuxAbi nrExitGroup 1
/-- `linux_os_madvise(addr, len, advice)`. -/
def gateMadvise : SysAbiArm := linuxAbi nrMadvise 3
/-- `linux_os_sched_yield()`. -/
def gateSchedYield : SysAbiArm := linuxAbi nrSchedYield 0
/-- `linux_os_exit(code)`. -/
def gateExit : SysAbiArm := linuxAbi nrExit 1
/-- `linux_os_futex(wort, op, erwartet, frist)`. -/
def gateFutex : SysAbiArm := linuxAbi nrFutex 4

/-- `gabbro_os_klon_tor(flaggen, spitze, eltern, kind)`:
    `regs in { x0 = flaggen, x1 = spitze, x2 = eltern, x4 = kind }`. -/
def gateKlon : SysAbiArm :=
  { nummer := nrClone
    nummerReg := nummerRegLinux
    ein := [(xr 0, 0), (xr 1, 1), (xr 2, 2), (xr 4, 3)]
    aus := ergebnisReg
    clobber := [] }

/-- The handed-stack register of the clone gate (`stack x1`). -/
def klonStapelReg : ArmReg := xr 1

/-- All nine gates of the binding, with the number each must carry. -/
def alleTore : List (SysAbiArm × Nat) :=
  [(gateMmap, 222), (gateMprotect, 226), (gateWrite, 64), (gateExitGroup, 94),
   (gateMadvise, 233), (gateSchedYield, 124), (gateExit, 93), (gateFutex, 98),
   (gateKlon, 220)]

/-- Every gate of the binding is well-formed, and carries the number the binding declares. -/
theorem alleTore_gut_und_nummer :
    ∀ p ∈ alleTore, p.1.gut ∧ p.1.nummer = p.2 := by decide

/-- The nine call numbers are pairwise distinct. -/
theorem alleTore_nummern_verschieden : (alleTore.map (·.2)).Nodup := by decide

/-- Every gate reads its answer from `x0` and destroys nothing (the kernel keeps every
    register but `x0`; the agreed ABI). -/
theorem alleTore_ergebnis_x0 :
    ∀ p ∈ alleTore, p.1.aus = ergebnisReg ∧ p.1.clobber = [] := by decide

/-- The clone gate's stack register is bound as an input, is neither the answer register nor
    the number register -- the `N446` demands the checker makes for AArch64 (`x1`). -/
theorem klon_stapelreg_gut :
    klonStapelReg ∈ gateKlon.ein.map Prod.fst ∧ klonStapelReg ≠ gateKlon.aus ∧
    klonStapelReg ≠ gateKlon.nummerReg ∧ klonStapelReg ∉ gateKlon.clobber := by decide

/-- **The AArch64 `clone` differs from `linuxAbi nrClone 4`**: the child's tid word travels in
    `x4`, so `x3` is unbound. A table that mapped the fourth argument to `x3` (the x86_64 habit:
    `r10` is the fourth register) would start a thread whose `CLONE_CHILD_CLEARTID` word is the
    kernel's `tls` argument -- the join would hang. -/
theorem klon_ist_nicht_linuxAbi : gateKlon ≠ linuxAbi nrClone 4 := by decide

theorem klon_kind_in_x4 : (xr 4, 3) ∈ gateKlon.ein ∧ xr 3 ∉ gateKlon.ein.map Prod.fst := by
  decide

/-- Witness: the clone gate's registers loaded for a concrete call
    (`flaggen = 0x350f00`, `spitze = 0x7f0000010000`, `eltern = 0x1000`, `kind = 0x2000`). -/
theorem klon_aufruf_zeuge :
    let s := ladeAufruf gateKlon beispielVorher (fun i => [0x350f00, 0x7f0000010000, 0x1000, 0x2000].getD i 0)
    s.reg (xr 8) = 220 ∧ s.reg (xr 0) = 0x350f00 ∧ s.reg (xr 1) = 0x7f0000010000 ∧
    s.reg (xr 2) = 0x1000 ∧ s.reg (xr 4) = 0x2000 ∧ s.reg (xr 3) = 1003 := by
  decide

end Arm

/- CUTS: what is NOT claimed.
   - The register maps are the BINDING's declarations restated; nothing here says the Linux
     kernel behaves so. The numbers are the asm-generic table (see `SyscallArm.lean`).
   - `SysAbiArm` is still not accepted by `Ax`/machine G; this file does not touch that.
   - The 64 KiB page granule of `linux-aarch64.gab` (`gabbro_os_seitengroesse`) is a Gabbro
     function over no register and has no statement here.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.Arm.alleTore_gut_und_nummer
#print axioms Gabbro.Grammatik.Arm.alleTore_nummern_verschieden
#print axioms Gabbro.Grammatik.Arm.alleTore_ergebnis_x0
#print axioms Gabbro.Grammatik.Arm.klon_stapelreg_gut
#print axioms Gabbro.Grammatik.Arm.klon_ist_nicht_linuxAbi
#print axioms Gabbro.Grammatik.Arm.klon_kind_in_x4
#print axioms Gabbro.Grammatik.Arm.klon_aufruf_zeuge
