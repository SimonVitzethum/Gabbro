/-
  File:      Grammatik/Kern/Semantik/SyscallArmPflicht.lean
  Subject:   THE NATIVE AArch64 COMPILER'S SYSTEM-CALL, ENTRY AND THREAD-START DUTIES AS
             VALIDATION OBLIGATIONS ON DECODED FINAL BYTES (not C templates).

  The C backend is deprecated; the planned path is source -> model -> AArch64 bytes, checked in
  Lean. For that path a duty is a PROPOSITION about a block of decoded instructions, which the
  validator discharges for the bytes the compiler produced. This file states four such duties
  over a deliberately small instruction type (`Bef`, only the forms these blocks use), gives each
  a canonical block, and proves the canonical block meets it for EVERY ABI record / stack value.
  The real obligation is the same proposition over the decoded bytes of the real block.

  * `PflichtSvc abi bs`        -- the system-call stub: `svc` sees exactly the registers
                                  `ladeAufruf abi` describes, the answer is in the answer
                                  register, every other register and `sp` come back unchanged.
  * `PflichtEintritt bs`       -- the process entry: one call, `sp` 16-aligned at its first
                                  instruction and inside `[sp0 - 15, sp0]`, then a trap.
  * `PflichtKind stapelReg bs` -- the cloned child's start on the handed stack.
  * `PflichtTrampolin bs`      -- the two-call child path through callee-saved registers.

  Sources: `SyscallArm.lean` (`SysAbiArm`, `ladeAufruf`, `nachSvc`, `ausrichtenArm`).
  See `messung/ARM-NATIV-ABI.md` for what is still missing (memory: `argc/argv` loads, the
  kernel's clone semantics, the decoder).
-/
import Grammatik.Kern.Semantik.SyscallArmLinux

namespace Gabbro.Grammatik

namespace Arm

/-! ## 1. The instruction forms and their meaning -/

/-- The AArch64 instruction forms the duty blocks use (after decoding the final bytes). -/
inductive Bef where
  /-- `mov d, #v` (`movz`/`movk` sequences decode to this). -/
  | movImm (d : ArmReg) (v : Nat)
  /-- `mov d, s` (also `mov x9, sp`; `xzr` as source is `movImm d 0`). -/
  | movReg (d s : ArmReg)
  /-- `and sp, via, #-16`. -/
  | andSp16 (via : ArmReg)
  /-- `svc #0`. -/
  | svc
  /-- `bl target` (writes `x30`; pushes nothing). -/
  | bl (ziel : Nat)
  /-- `blr r`. -/
  | blr (r : ArmReg)
  /-- `brk #0`. -/
  | brk
  deriving DecidableEq

/-- What a straight-line run records: the register state, every call as
    `(target, sp at the callee's first instruction, x0 at the call)`, the register state at every
    `svc`, and whether the trap was reached. -/
structure Lauf where
  z : ArmZustand
  aufrufe : List (Nat × Nat × Nat)
  svcs : List (ArmReg → Nat)
  halt : Bool

def setzeReg (z : ArmZustand) (d : ArmReg) (v : Nat) : ArmZustand :=
  { z with reg := fun r => if r = d then v % 18446744073709551616 else z.reg r }

/-- One instruction. `antwort` is what the kernel answers an `svc` with (the agreed ABI,
    `nachSvc`). -/
def schritt (antwort : Int) (l : Lauf) : Bef → Lauf
  | .movImm d v => { l with z := setzeReg l.z d v }
  | .movReg d s => { l with z := setzeReg l.z d (l.z.reg s) }
  | .andSp16 via => { l with z := setzeReg l.z .sp (ausrichtenArm (l.z.reg via)) }
  | .svc => { l with svcs := l.svcs ++ [l.z.reg], z := nachSvc l.z antwort }
  | .bl t => { l with aufrufe := l.aufrufe ++ [(t, l.z.reg .sp, l.z.reg ergebnisReg)] }
  | .blr r => { l with aufrufe := l.aufrufe ++ [(l.z.reg r, l.z.reg .sp, l.z.reg ergebnisReg)] }
  | .brk => { l with halt := true }

def lauf (antwort : Int) (z : ArmZustand) (bs : List Bef) : Lauf :=
  bs.foldl (schritt antwort) ⟨z, [], [], false⟩

/-! ## 2. Duty 1: the system-call stub -/

/-- **`PflichtSvc abi bs`.** For every caller state in which each bound input register holds its
    argument, every kernel answer: the one `svc` executes with exactly the registers
    `ladeAufruf abi vorher args` (the number in its register, each argument in its register,
    everything else as the caller had it), the answer reduced mod 2^64 is in the answer register,
    every register other than the answer and the number register and `sp` are as before, and no
    call and no trap happen. -/
def PflichtSvc (abi : SysAbiArm) (bs : List Bef) : Prop :=
  ∀ (vorher : ArmZustand) (args : Nat → Nat) (antwort : Int),
    (∀ p ∈ abi.ein, vorher.reg p.1 = args p.2) →
    let l := lauf antwort vorher bs
    l.svcs.length = 1 ∧ (∀ s ∈ l.svcs, ∀ r, s r = (ladeAufruf abi vorher args).reg r) ∧
    l.z.reg abi.aus = (antwort % 18446744073709551616).toNat ∧
    (∀ r, r ≠ abi.aus → r ≠ abi.nummerReg → l.z.reg r = vorher.reg r) ∧
    l.aufrufe = [] ∧ l.halt = false

/-- The canonical stub: load the number, `svc #0`. (Arguments are already in place: the gate's
    parameters are pinned to their registers by the call sequence.) -/
def stubBlock (abi : SysAbiArm) : List Bef := [.movImm abi.nummerReg abi.nummer, .svc]

/-- **The canonical stub meets the duty for every well-formed ABI record** whose number fits
    64 bits, that answers in `x0` (the agreed `svc` ABI: `nachSvc` changes `x0` only) and whose
    number register is not `x0`. -/
theorem stub_erfuellt (abi : SysAbiArm) (hn : abi.nummer < 18446744073709551616)
    (haus : abi.aus = ergebnisReg) :
    PflichtSvc abi (stubBlock abi) := by
  intro vorher args antwort harg
  have hl : ∀ r, (setzeReg vorher abi.nummerReg abi.nummer).reg r =
      (ladeAufruf abi vorher args).reg r := by
    intro r
    simp only [setzeReg, ladeAufruf]
    by_cases hr : r = abi.nummerReg
    · simp [hr, Nat.mod_eq_of_lt hn]
    · simp only [hr, if_false]
      cases hf : abi.ein.find? (fun p => decide (p.1 = r)) with
      | none => rfl
      | some p =>
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        have hp' : p.1 = r := of_decide_eq_true hp
        simp only []
        rw [← hp']
        exact (harg p hm)
  simp only [lauf, stubBlock, List.foldl, schritt]
  refine ⟨rfl, ?_, ?_, ?_, trivial, trivial⟩
  · intro s hs r
    simp only [List.nil_append, List.mem_singleton] at hs
    subst hs
    exact hl r
  · rw [haus]
    simp [nachSvc]
  · intro r h1 h2
    rw [haus] at h1
    simp only [nachSvc, h1, if_false, setzeReg, h2]

/-- Witness: the duty is not vacuous -- it holds for the `write` gate and `clone` gate of the
    AArch64 binding, and a block that forgets the number is REFUSED. -/
theorem stub_zeuge :
    PflichtSvc schreibAbiArm (stubBlock schreibAbiArm) ∧ PflichtSvc gateKlon (stubBlock gateKlon) ∧
    ¬ PflichtSvc schreibAbiArm [.svc] := by
  refine ⟨stub_erfuellt _ (by decide) rfl, stub_erfuellt _ (by decide) rfl, ?_⟩
  intro h
  have h1 := (h beispielVorher (fun i => 1000 + i) 0 (by decide)).2.1 beispielVorher.reg
    (by simp [lauf, schritt, List.foldl])
  have h2 := h1 (xr 8)
  revert h2
  decide

/-! ## 3. Duty 2: the process entry (`_start`) -/

/-- **`PflichtEintritt bs`.** From any entry state with `sp0 >= 16`: exactly one call, taken with
    `sp` 16-aligned, not above `sp0` (so `argc/argv/envp` above it stay intact) and less than 16
    below it; the frame-chain register `x29` is zero at the call; then the trap is reached (the
    called `main` never returns, `brk` is the guard); no `svc` runs. -/
def PflichtEintritt (bs : List Bef) : Prop :=
  ∀ (z0 : ArmZustand), 16 ≤ z0.reg .sp → z0.reg .sp < 18446744073709551616 →
    let l := lauf 0 z0 bs
    l.aufrufe.length = 1 ∧
    (∀ c ∈ l.aufrufe, c.2.1 % 16 = 0 ∧ c.2.1 ≤ z0.reg .sp ∧ z0.reg .sp < c.2.1 + 16) ∧
    l.z.reg (xr 29) = 0 ∧ l.halt = true ∧ l.svcs = []

/-- `mov x29, #0; mov x9, sp; and sp, x9, #-16; bl main; brk #0`. -/
def eintrittBlock (haupt : Nat) : List Bef :=
  [.movImm (xr 29) 0, .movReg (xr 9) .sp, .andSp16 (xr 9), .bl haupt, .brk]

theorem eintritt_erfuellt (haupt : Nat) : PflichtEintritt (eintrittBlock haupt) := by
  intro z0 hsp hlt
  simp only [lauf, eintrittBlock, List.foldl, schritt, setzeReg, ausrichtenArm]
  simp
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- An entry state with an 8-mod-16 stack pointer (the kernel hands 16-aligned; the duty must hold
    for the weaker case the `nolibc` entry is written for). -/
def eintrittVorher : ArmZustand :=
  { beispielVorher with reg := fun r => if r = .sp then 0x7ffc12345678 else beispielVorher.reg r }

/-- Witness: the canonical entry aligns an 8-mod-16 stack pointer, and a block that forgets the
    alignment is REFUSED. -/
theorem eintritt_zeuge :
    PflichtEintritt (eintrittBlock 0x401000) ∧
    ¬ PflichtEintritt [.movImm (xr 29) 0, .bl 0x401000, .brk] := by
  refine ⟨eintritt_erfuellt _, ?_⟩
  intro h
  have := (h eintrittVorher (by decide) (by decide)).2.1
  have h2 := this (0x401000, eintrittVorher.reg .sp, eintrittVorher.reg ergebnisReg)
    (by simp [lauf, schritt, List.foldl, setzeReg]; intro h; exact absurd h (by decide))
  revert h2
  decide

/-! ## 4. Duty 3: the cloned child on the handed stack -/

/-- **`PflichtKind stapelReg bs`.** The child starts with `sp` and the `stack` clause's register
    both holding the handed top `v >= 16` (`kindNachSvc`; Linux hands the child exactly that
    stack). The block calls its region once with `x0 = v` (the handed value), at a 16-aligned
    `sp` not above `v` and less than 16 below it, `x29` is zero, and the trap follows. The
    parent's frame is never touched: nothing here reads any register but `stapelReg` and `sp`. -/
def PflichtKind (stapelReg : ArmReg) (bs : List Bef) : Prop :=
  ∀ (z0 : ArmZustand) (v : Nat), 16 ≤ v → v < 18446744073709551616 →
    z0.reg .sp = v → z0.reg stapelReg = v → stapelReg ≠ xr 9 → stapelReg ≠ xr 29 →
    let l := lauf 0 z0 bs
    l.aufrufe.length = 1 ∧
    (∀ c ∈ l.aufrufe, c.2.2 = v ∧ c.2.1 % 16 = 0 ∧ c.2.1 ≤ v ∧ v < c.2.1 + 16) ∧
    l.z.reg (xr 29) = 0 ∧ l.halt = true ∧ l.svcs = []

/-- `mov x0, stack; mov x9, sp; and sp, x9, #-16; mov x29, #0; bl region; brk #0`. -/
def kindBlock (stapelReg : ArmReg) (region : Nat) : List Bef :=
  [.movReg ergebnisReg stapelReg, .movReg (xr 9) .sp, .andSp16 (xr 9), .movImm (xr 29) 0,
   .bl region, .brk]

theorem kind_erfuellt (stapelReg : ArmReg) (region : Nat) :
    PflichtKind stapelReg (kindBlock stapelReg region) := by
  intro z0 v hv hlt hsp hst h9 h29
  simp only [lauf, kindBlock, List.foldl, schritt, setzeReg, ausrichtenArm, ergebnisReg]
  simp [hsp, hst]
  refine ⟨hlt, ?_, ?_, ?_⟩ <;> omega

/-! ## 5. Duty 4: the two-call child path through callee-saved registers -/

/-- **`PflichtTrampolin ra rb bs`.** With the two targets held in the callee-saved registers
    `ra`, `rb` (distinct from `x9`/`x29`, and from each other): both are called, in that order,
    each at the same 16-aligned `sp` within 16 below the entry `sp`, and the trap follows. (That
    the gate PRESERVES `ra`/`rb` across the `svc` is `alleTore_ergebnis_x0`: only `x0` changes.) -/
def PflichtTrampolin (ra rb : ArmReg) (bs : List Bef) : Prop :=
  ∀ (z0 : ArmZustand), 16 ≤ z0.reg .sp → z0.reg .sp < 18446744073709551616 →
    ra ≠ xr 9 → rb ≠ xr 9 → ra ≠ .sp → rb ≠ .sp →
    let l := lauf 0 z0 bs
    l.aufrufe.map (·.1) = [z0.reg ra, z0.reg rb] ∧
    (∀ c ∈ l.aufrufe, c.2.1 % 16 = 0 ∧ c.2.1 ≤ z0.reg .sp ∧ z0.reg .sp < c.2.1 + 16) ∧
    l.halt = true ∧ l.svcs = []

def trampolinBlock (ra rb : ArmReg) : List Bef :=
  [.movReg (xr 9) .sp, .andSp16 (xr 9), .blr ra, .blr rb, .brk]

theorem trampolin_erfuellt (ra rb : ArmReg) : PflichtTrampolin ra rb (trampolinBlock ra rb) := by
  intro z0 hsp hlt h9a h9b hsa hsb
  simp only [lauf, trampolinBlock, List.foldl, schritt, setzeReg, ausrichtenArm]
  simp [h9a, h9b, hsa, hsb]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Witness for the kind and trampoline duties: concrete handed stack tops, plus a REFUSED block
    (the child path that skips the alignment). -/
theorem kind_zeuge :
    PflichtKind (xr 1) (kindBlock (xr 1) 0x401000) ∧
    ¬ PflichtKind (xr 1) [.movReg ergebnisReg (xr 1), .movImm (xr 29) 0, .bl 0x401000, .brk] := by
  refine ⟨kind_erfuellt _ _, ?_⟩
  intro h
  let z0 : ArmZustand :=
    { beispielVorher with reg := fun r =>
        if r = .sp then 0x7f0000010008 else if r = xr 1 then 0x7f0000010008 else beispielVorher.reg r }
  have := (h z0 0x7f0000010008 (by decide) (by decide) (by simp [z0]) (by simp [z0])
    (by decide) (by decide)).2.1
  have h2 := this (0x401000, 0x7f0000010008, 0x7f0000010008)
    (by simp [z0, lauf, schritt, List.foldl, setzeReg, ergebnisReg])
  revert h2
  decide

end Arm

/- CUTS: what is NOT claimed.
   - `Bef` is a MINI instruction type, not the decoder's output type. No AArch64 decoder exists in
     the tree yet; the duties transfer to it by one lemma per instruction form (mov, and-sp, svc,
     bl, blr, brk) relating decoded bytes to `Bef`.
   - Memory is not modelled: `argc/argv/envp` loads from `[sp]`, the stack bytes the child must
     not touch, the write of `x30` by `bl`, and the kernel's clone semantics (the child gets
     `x0 = 0` and the handed `sp`; here that is the HYPOTHESIS of `PflichtKind`). Flags are not
     modelled (`svc` clobber of NZCV is not claimed, as in `SyscallArm.lean`).
   - The canonical blocks are the shape the validator ACCEPTS, not the compiler's output; the
     compiler's output is accepted when its decoded bytes satisfy the same `Pflicht*`
     proposition (or are a block proved equivalent to a canonical one).
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.Arm.stub_erfuellt
#print axioms Gabbro.Grammatik.Arm.stub_zeuge
#print axioms Gabbro.Grammatik.Arm.eintritt_erfuellt
#print axioms Gabbro.Grammatik.Arm.eintritt_zeuge
#print axioms Gabbro.Grammatik.Arm.kind_erfuellt
#print axioms Gabbro.Grammatik.Arm.kind_zeuge
#print axioms Gabbro.Grammatik.Arm.trampolin_erfuellt
