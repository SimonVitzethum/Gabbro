import Runner.Beweis.Bild
import Runner.Beweis.Spur
import Runner.Prog.Proben

/-! # Witness: the premises of `runner_ok` hold on the real runner with a real image

The fixture is the memory a run of `runner hello.img` has after the loader: the runner's file at `BASE`
(readable, not writable) and the probe image `hello` at `IMG` (readable and writable), with `x` at a copy of the
dispatch, `r12` at the first IR instruction and `r13` at the image's first frame. `runner_zeuge`: `R L0` holds, and
the IR state takes a real step (the fixture is not degenerate: the image's first byte is the opcode `const`). -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

def inImg (a : W) : Bool := IMG ≤ a.toNat && a.toNat < IMG + hello.length
def inRun (a : W) : Bool := BASE ≤ a.toNat && a.toNat < BASE + image.length

def m0 : Mem where
  b a := if inRun a then image.getD (a.toNat - BASE) 0 else if inImg a then hello.getD (a.toNat - IMG) 0 else 0
  rd a := inRun a || inImg a
  wr a := inImg a

set_option maxRecDepth 100000 in
theorem image_len : image.length = 4136 := by decide +kernel

theorem m0_file : FileInv m0 := by
  intro j hj
  have hl := image_len
  have ht : (BitVec.ofNat 64 (BASE + j)).toNat = BASE + j := by
    simp only [BitVec.toNat_ofNat, BASE]; omega
  have hr : inRun (BitVec.ofNat 64 (BASE + j)) = true := by
    simp only [inRun, ht, Bool.and_eq_true, decide_eq_true_eq]; omega
  have hn : ¬(IMG ≤ BASE + j) := by simp only [IMG, BASE]; omega
  have hi : inImg (BitVec.ofNat 64 (BASE + j)) = false := by simp [inImg, ht, hn]
  refine ⟨?_, by simp [m0, hr], by simp [m0, hi]⟩
  simp only [m0, hr, ↓reduceIte, ht, Nat.add_sub_cancel_left]
  simp only [List.getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- A copy of the dispatch: the end of `jmp`'s handler. -/
def dsite : Nat := find tab 18 + lenOf [fld .rax 1, .alu .add .r12 .rax]

set_option maxRecDepth 100000 in
theorem dsite_ok : (dispatch.all Ins.ok && (dispatch.flatMap enc).isPrefixOf (image.drop dsite)) = true := by
  decide +kernel

def fp0 : W := (m0.rd64 (BitVec.ofNat 64 IMG)).getD 0

def s0 : IR.S := { pc := BitVec.ofNat 64 (IMG + 16), fp := fp0, mem := m0 }

def x0 : X :=
  { rax := 0, rcx := 0, rdx := 0, rbx := 0, rsp := 0, rbp := 0, rsi := 0, rdi := 0, r8 := 0, r9 := 0, r10 := 0,
    r11 := 0, r12 := BitVec.ofNat 64 (IMG + 16), r13 := fp0, r14 := L0.T, r15 := 0,
    rip := BitVec.ofNat 64 (BASE + dsite), cf := none, zf := none, sf := none, of := none, mem := m0 }

/-- The first request to the kernel within `n` steps, as its number and arguments. -/
def firstSys {σ : Type} (st : σ → Res σ) : Nat → σ → Option (List Nat)
  | 0, _ => none
  | n + 1, s => match st s with
    | .next t => firstSys st n t
    | .sys q _ => some [q.nr.toNat, q.a1.toNat, q.a2.toNat, q.a3.toNat, q.a4.toNat, q.a5.toNat, q.a6.toNat]
    | _ => none

set_option maxRecDepth 100000 in
/-- The IR of `hello` asks `write(1, msg, 16)` first. -/
theorem zeuge_ir : firstSys IR.step 20 s0 = some [1, 1, IMG + 192, 16, 0, 0, 0] := by decide +kernel

theorem runner_zeuge : R L0 s0 x0 := by
  have hd := dsite_ok
  simp only [Bool.and_eq_true] at hd
  exact ⟨code_of_file m0_file hd.1 hd.2, rfl, rfl, rfl, rfl, image_ok m0_file⟩

end Runner.Beweis

namespace Runner.Beweis
open Runner.X86 Runner.Prog

set_option maxRecDepth 100000 in
/-- The x86-64 model running the runner's bytes on `hello` asks the kernel the same first request. -/
theorem zeuge_x86 : firstSys X86.step 200 x0 = some [1, 1, IMG + 192, 16, 0, 0, 0] := by decide +kernel

end Runner.Beweis
