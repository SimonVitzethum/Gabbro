import Runner.Beweis.Bild
import Runner.Prog.Proben

/-! # The runner's theorems, and their witness on the real file

`runner_tso`: start the runner's thread at a copy of the dispatch, related to the IR's first state, in any state
of x86-TSO: every observation of the x86 process -- with all the threads it starts by `clone` -- is an observation
of the IR process from the same state, and it never reaches an undescribed step. `runner_sc`: the same on one
sequentially consistent memory.

`runner_zeuge`: the premises hold together on the real runner file loaded at `BASE`, the probe image `hello` at
`IMG`, empty store buffers. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog Runner.Mach

theorem start_rel {M : MemSys} {s : M.St} {t : IR.T} {x : X} (hD : Disp L0 t x) :
    Rel L0 (M := M) ⟨s, [some (.next t)]⟩ ⟨s, [some x]⟩ := by
  refine ⟨rfl, fun j => ?_⟩
  match j with
  | 0 => exact (MatchP.disp hD : Match L0 (.next t) x)
  | j + 1 => trivial

theorem runner_tso {s : (TSO L0).St} {t : IR.T} {x : X} (hD : Disp L0 t x) {l : List Ev} {e : Ende} {n : Nat}
    (h : Tr (TSO L0) (actX L0) ⟨s, [some x]⟩ l e n) :
    e ≠ .unk ∧ ∃ m, Tr (TSO L0) actI ⟨s, [some (.next t)]⟩ l e m :=
  runner_mt (tso_fixed L0) cinv_L0 n (start_rel hD) h

theorem runner_sc {s : (SC L0).St} {t : IR.T} {x : X} (hD : Disp L0 t x) {l : List Ev} {e : Ende} {n : Nat}
    (h : Tr (SC L0) (actX L0) ⟨s, [some x]⟩ l e n) :
    e ≠ .unk ∧ ∃ m, Tr (SC L0) actI ⟨s, [some (.next t)]⟩ l e m :=
  runner_mt (sc_fixed L0) cinv_L0 n (start_rel hD) h

/-! ## Witness -/

def inImg (a : W) : Bool := IMG ≤ a.toNat && a.toNat < IMG + hello.length

def m0 : Mem where
  b a := if inRun a then image.getD (a.toNat - BASE) 0 else if inImg a then hello.getD (a.toNat - IMG) 0 else 0
  rd a := inRun a || inImg a
  wr a := inImg a

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

/-- The x86-TSO state after the loader: the memory `m0`, every buffer empty. -/
def s0 : (TSO L0).St := ⟨⟨m0, fun _ => []⟩, tab_of_file m0_file, fun _ _ he => by cases he⟩

/-- A copy of the dispatch: the end of `jmp`'s handler. -/
def dsite : Nat := find tab 18 + lenOf [fld .rax 1, .alu .add .r12 .rax]

set_option maxRecDepth 100000 in
theorem dsite_ok : (dispatch.all Ins.ok && (dispatch.flatMap enc).isPrefixOf (image.drop dsite)) = true := by
  decide +kernel

def fp0 : W := (m0.rd64 (BitVec.ofNat 64 IMG)).getD 0

def t0 : IR.T := { pc := BitVec.ofNat 64 (IMG + 16), fp := fp0 }

def x0 : X :=
  { rax := 0, rcx := 0, rdx := 0, rbx := 0, rsp := 0, rbp := 0, rsi := 0, rdi := 0, r8 := 0, r9 := 0, r10 := 0,
    r11 := 0, r12 := BitVec.ofNat 64 (IMG + 16), r13 := fp0, r14 := L0.T, r15 := 0,
    rip := BitVec.ofNat 64 (BASE + dsite), cf := none, zf := none, sf := none, of := none }

theorem x0_disp : Disp L0 t0 x0 := by
  have hd := dsite_ok
  simp only [Bool.and_eq_true] at hd
  exact ⟨code_of_image hd.1 hd.2, rfl, rfl, rfl⟩

/-- The premises of `runner_tso` hold together on the real file and a real image; the fixture is not degenerate:
    the first request of both threads is the read of the first opcode byte at `IMG + 16`. -/
theorem runner_zeuge : Disp L0 t0 x0 ∧ TInv L0 s0.1 ∧
    (∃ k, step L0.C x0 = .ask (.rd 1 (BitVec.ofNat 64 (IMG + 16))) k) ∧
    (∃ k, IR.step t0 = .ask (.rd 1 (BitVec.ofNat 64 (IMG + 16))) k) := by
  refine ⟨x0_disp, s0.2, ?_, ⟨_, rfl⟩⟩
  rw [step_code x0_disp.code]
  have hea : ea x0 (mb .r12) = BitVec.ofNat 64 (IMG + 16) := by
    simp only [ea, mb, X.get, x0]
    rw [show sx32 0 = 0 from by decide]
    exact BitVec.add_zero _
  simp only [exec, rd8, hea]
  exact ⟨_, rfl⟩

end Runner.Beweis
