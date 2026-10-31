/- Joint actual-IR witness for downward overlapping transport of three canonical words. -/
import Stage0.Senke.Ausdruck.Quant.Memory
import Runner.Prog.IRAsm
namespace Gabbro.Stage0.Senke.PointerProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
abbrev shape : Ty := .arr (.int 0 255) 3

def value {D : Deklaration} : Wert D shape := fun i =>
  ⟨i.val + 1, by omega, by have := i.isLt; omega⟩
def code : List II := loadPointerSpan 3 3 8 9 0

def memory : Runner.Mem where
  b a := if a.toNat < 144 then
      ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 4128 then 1 else if a.toNat = 4136 then 2 else if a.toNat = 4144 then 3
    else if a.toNat = 4160 then 32 else if a.toNat = 4161 then 16 else 0
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
  have bound : k < 9 := by simpa [code] using hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [code, loadPointerSpan, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem source_at {D : Deklaration} (L : Lay D) : ValueAt L memory 4128 0 shape (value (D := D)) := by
  constructor
  · intro i; trivial
  · change WordsAt memory 4128 0 [1, 2, 3]
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases cases with rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem loadPointerValue_run_zeuge [Kern] {D : Deklaration} (L : Lay D) :
    ∃ m', Star ⟨0, 4096⟩ memory ⟨144, 4096⟩ m' ∧ Agree 4096 3 16 memory m' ∧
      SpanEffect 4096 9 4120 3 memory m' ∧ ValueAt L m' 4096 3 shape (value (D := D)) ∧
      m'.rd64 (slot 4096 8) = some 4128 := by
  exact loadPointerValue_run (fp := 4096) (K := 16) (dst := 3) (ptr := 8) (tmp := 9) (offset := 0)
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide)) code_at
    (by unfold CodeFar; decide) (by decide +kernel) (source_at L)

theorem overlapping_ranges_zeuge {D : Deklaration} :
    (4120 : Nat) < 4128 ∧ 4128 < 4120 + 8 * 3 ∧ (value (D := D) ⟨0, by decide⟩).n = 1 := by
  exact ⟨by decide, by decide, rfl⟩
end Gabbro.Stage0.Senke.PointerProbe
