module
public import Runner.Beweis.Bild
@[expose] public section


/-! # The runner's theorems and dispatch initialization

`runner_tso`: start the runner's thread at a copy of the dispatch, related to the IR's first state, in any state
of x86-TSO: every observation of the x86 process -- with all the threads it starts by `clone` -- is an observation
of the IR process from the same state, and it never reaches an undescribed step. `runner_sc`: the same on one
sequentially consistent memory.

`runner_start_erfuellbar`: the loaded runner file and empty store buffers admit a dispatch state for any IR entry. -/

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

/-! ## Dispatch initialization -/

/-- A copy of the dispatch: the end of `jmp`'s handler. -/
def dsite : Nat := find tab 18 + lenOf [fld .rax 1, .alu .add .r12 .rax]

set_option maxRecDepth 100000 in
theorem dsite_ok : (dispatch.all Ins.ok && (dispatch.flatMap enc).isPrefixOf (image.drop dsite)) = true := by
  decide +kernel

private def dispatchState (t : IR.T) : X :=
  { rax := 0, rcx := 0, rdx := 0, rbx := 0, rsp := 0, rbp := 0, rsi := 0, rdi := 0, r8 := 0, r9 := 0,
    r11 := 0, r12 := t.pc, r13 := t.fp, r14 := L0.T, r15 := 0,
    rip := BitVec.ofNat 64 (BASE + dsite), cf := none, zf := none, of := none, sf := none, mxcsr := 0x1F80 }

/-- A loaded runner admits the dispatch relation at any IR entry, with empty TSO buffers. -/
theorem runner_start_erfuellbar {m : Mem} (loaded : FileInv m) (t : IR.T) :
    ∃ (x : X) (s : (TSO L0).St), s.1 = ⟨m, fun _ => []⟩ ∧ Disp L0 t x := by
  have table : TInv L0 ⟨m, fun _ => []⟩ :=
    ⟨tab_of_file loaded, fun _ _ inEmpty => nomatch inEmpty⟩
  have code := Bool.and_eq_true.mp dsite_ok
  exact ⟨dispatchState t, ⟨_, table⟩, rfl, code_of_image code.1 code.2, rfl, rfl, rfl, by decide⟩

end Runner.Beweis
