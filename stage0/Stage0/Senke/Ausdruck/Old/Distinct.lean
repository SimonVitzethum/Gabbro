/- Joint full-span capture witness: distinct cells, nonzero data and preserved frame storage. -/
module
public import Stage0.Senke.Ausdruck.Old.Spans
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Runner.Prog.IRAsm
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Stage0.Senke.DistinctSnapshotProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev shape : Ty := .arr (.int 0 255) 3

def unit : UProg := {
  tabs := [], locks := [], fns := []
  globs := [{name := "payload", ty := .wert shape, init := 0},
    {name := "counter", ty := .int 0 100, init := 0}] }
abbrev D := declOf unit
abbrev payload : D.Glob := ⟨0, by decide⟩
abbrev counter : D.Glob := ⟨1, by decide⟩

def value : Wert D shape := fun i =>
  ⟨i.val + 1, by omega, by have := i.isLt; omega⟩

def world : World D where
  slots t := nomatch t
  globs g := by
    obtain ⟨g, hg⟩ := g
    cases g with
    | zero => exact value
    | succ g =>
      have : g = 0 := by change g + 1 < 2 at hg; omega
      subst g
      exact ⟨19, by decide, by decide⟩
  spur := []

def layout : Lay D where
  col t := nomatch t
  ga g := 8192 + 32 * g.val
  lo := 8192
  hi := 8232
  tor _ := none
  byte _ := none

def cells : List (Zelle D) := [.glob payload, .glob counter]
def code : List II := loadSpan 3 4 8192 ++ loadSpan 1 7 8224

def memory : Runner.Mem where
  b a := if a.toNat < 128 then
      ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 4096 then 64 else if a.toNat = 4160 then 33
    else if a.toNat = 4168 then 34
    else if a.toNat = 8192 then 1 else if a.toNat = 8200 then 2
    else if a.toNat = 8208 then 3 else if a.toNat = 8224 then 19 else 0
  rd _ := true
  wr a := decide (a.toNat < 8192)

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem frame : FrameOK memory 4096 32 := by
  refine ⟨by decide, fun _ _ => rfl, ?_⟩
  intro i hi
  apply all_of
  intro j hj
  have slotValue := slot_toNat (fp := (4096 : Runner.W)) (K := 32) (by decide) hi
  change decide (((slot 4096 (BitVec.ofNat 64 i)) + BitVec.ofNat 64 j).toNat < 8192) = true
  apply decide_eq_true
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, slotValue, show (4096 : Runner.W).toNat = 4096 from rfl]
  omega

theorem code_at : CodeAt memory 0 code := by
  intro k hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
    change k < 8 at hk
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [code, loadSpan, List.cons_append, List.nil_append,
      List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel +revert

theorem inputs : EntrySnapshots.Inputs layout world memory cells := by
  intro cell hc
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · constructor
    · intro i; trivial
    · change WordsAt memory 8192 0 [1, 2, 3]
      intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
      rcases cases with rfl | rfl | rfl <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel +revert
  · exact ⟨trivial, fun i hi => by
      have : i = 0 := by change i < 1 at hi; omega
      subst i
      decide +kernel +revert⟩

/-- Every capture premise holds jointly. Source storage is read-only; all three
    payload limbs, the distinct counter and preserved original parameter survive. -/
theorem capture_ok_zeuge [Kern] :
    EntrySnapshots.capture layout cells 4 = some code ∧
    EntrySnapshots.words cells = 4 ∧ memory.wr 8192 = false ∧ memory.wr 8224 = false ∧
    ∃ m', Star ⟨0, 4096⟩ memory ⟨128, 4096⟩ m' ∧
      EntrySnapshots.At layout world m' 4096 cells 4 ∧
      m'.rd64 4160 = some 33 ∧ m'.rd64 4096 = some 64 ∧
      EntrySnapshots.Inputs layout world m' cells := by
  have emitted : EntrySnapshots.capture layout cells 4 = some code := by decide +kernel
  obtain ⟨m', run, changed, saved⟩ := EntrySnapshots.capture_ok cells 4 emitted memory 0
    frame (by decide) (by decide) (by intro cell hc; simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl <;> decide +kernel)
    code_at (by unfold CodeFar; decide +kernel) inputs
  refine ⟨emitted, rfl, rfl, rfl, m', ?_, saved, ?_, ?_, ?_⟩
  · rw [show (0 : Runner.W) + BitVec.ofNat 64 (16 * code.length) = (128 : Runner.W) by decide +kernel] at run
    exact run
  · have unchanged := rd64_agree_out (a := 4160) changed (by decide) (Or.inr (by decide))
    rw [show BitVec.ofNat 64 4160 = (4160 : Runner.W) by decide +kernel] at unchanged
    rw [unchanged]
    decide +kernel
  · have first := agree_rd_low (i := 0) changed (by decide) (by decide) (by decide)
    simpa only [slot, BitVec.zero_mul, BitVec.add_zero] using
      first.trans (show memory.rd64 4096 = some 64 by decide +kernel)
  · exact EntrySnapshots.Inputs.agree inputs changed
      (by intro cell hc; simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hc; rcases hc with rfl | rfl <;> decide +kernel)
      (fun cell hc => (EntrySnapshots.capture_bounds cells 4 emitted cell hc).2)

end Gabbro.Stage0.Senke.DistinctSnapshotProbe
