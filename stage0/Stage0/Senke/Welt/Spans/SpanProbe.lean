/- Joint nondegenerate witness: all load premises and recursive validity together. -/
import Stage0.Senke.Welt.Spans.SpanStore
import Grammatik.Bausteine.Arena.Unbounded.GRegion
import Runner.Prog.IRAsm

namespace Gabbro.Stage0.Senke.SpanProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
abbrev shape : Ty := .arr (.int 0 255) 3

def value {D : Deklaration} : Wert D shape := fun i =>
  ⟨i.val + 1, by omega, by have := i.isLt; omega⟩
def code : List II := loadSpan 3 8 8192

def memory : Runner.Mem where
  b a := if a.toNat < 96 then
      ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 8192 then 1 else if a.toNat = 8200 then 2
    else if a.toNat = 8208 then 3 else 0
  rd _ := true
  wr _ := true

local instance (m : Runner.Mem) (pc : Runner.W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

theorem code_at : CodeAt memory 0 code := by
  intro k hk
  have bound : k < 6 := by simpa [code] using hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [code, loadSpan, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem storage_at {D : Deklaration} (L : Lay D) :
    StorageAt L memory 8192 shape (value (D := D)) := by
  constructor
  · intro i; trivial
  · change WordsAt memory 8192 0 [1, 2, 3]
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases cases with rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem loadValue_run_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ValueOk L memory 0 4096 16 8 code shape (value (D := D)) := by
  obtain ⟨m', run, changed, output⟩ := loadValue_run
    (fp := 4096) (K := 16) (dst := 8) (address := 8192)
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩ (by decide)
    (by decide) (by decide) (by decide) code_at (by unfold CodeFar; decide) (storage_at L)
  exact ⟨m', run, Agree.widen changed (by decide), output⟩

theorem writeValue_same_zeuge {D : Deklaration} (L : Lay D) :
    StorageAt L (writeSpan memory 8192 (encodeWords L shape value)) 8192 shape
      (value (D := D)) :=
  writeValue_same (by decide) (fun _ _ => rfl) (by intro i; trivial)

abbrev D := GRegion.rD

def layout : Lay D where
  col _ _ := 8192
  ga g := nomatch g
  lo := 8192
  hi := 8216
  tor _ := none
  byte _ := none

def storeCode : List II := storeSpan 3 8 4 8192

def storeMemory : Runner.Mem where
  b a := if a.toNat < 96 then
      ((storeCode.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 4128 then 1 else if a.toNat = 4136 then 2
    else if a.toNat = 4144 then 3 else 0
  rd _ := true
  wr _ := true

theorem store_code_at : CodeAt storeMemory 0 storeCode := by
  intro k hk
  have bound : k < 6 := by simpa [storeCode] using hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [storeCode, storeSpan, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem store_input : ValueAt layout storeMemory 4096 4 shape value := by
  constructor
  · intro i; trivial
  · change WordsAt storeMemory 4096 4 [1, 2, 3]
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases cases with rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem storeValue_run_zeuge [Kern] :
    ∃ m', Star ⟨0, 4096⟩ storeMemory ⟨96, 4096⟩ m' ∧
      SpanEffect 4096 8 8192 3 storeMemory m' ∧ StorageAt layout m' 8192 shape value := by
  have lay : LayIn layout := by
    refine ⟨fun t f k hk => ?_, (fun g => nomatch g), by decide⟩
    change (k : Int) < 0 at hk
    omega
  exact storeValue_run (fp := 4096) (K := 16) (tmp := 8) (src := 4) lay
    (by decide) (by decide) (by decide)
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    (by decide) (by decide) (by decide) store_code_at (by unfold CodeFar; decide)
    store_input (fun _ _ => rfl) (fun _ _ => rfl)

end Gabbro.Stage0.Senke.SpanProbe
