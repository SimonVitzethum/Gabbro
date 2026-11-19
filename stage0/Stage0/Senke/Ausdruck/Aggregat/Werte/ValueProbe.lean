/- A nondegenerate three-word variable fixture with every execution premise supplied. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.KopieSatz
public import Stage0.Senke.Ausdruck.Aggregat.Materialize
public import Runner.Prog.IRAsm
@[expose] public section


namespace Gabbro.Stage0.Senke.ValueProbe
open Gabbro.Grammatik Runner.IR Runner.Mem

abbrev element : Ty := .int 0 255
abbrev shape : Ty := .arr element 3

def value {D : Deklaration} : Wert D shape := fun i =>
  ⟨i.val + 1, by omega, by have := i.isLt; omega⟩

def env {D : Deklaration} : Env D [shape] := .cons value .nil
def code : List II := copyWords 3 8 4

theorem value_encoding {D : Deklaration} (L : Lay D) :
    encodeWords L shape (value (D := D)) = [1, 2, 3] := by
  simp only [encodeWords.eq_def, shape, elementEncoding]
  rfl

def memory : Runner.Mem where
  b a := if a.toNat < 48 then
      ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 4128 then 1 else if a.toNat = 4136 then 2
    else if a.toNat = 4144 then 3 else 0
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
  have bound : k < 3 := by simpa [code] using hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases cases with rfl | rfl | rfl <;>
    simp only [code, copyWords, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem input_at {D : Deklaration} (L : Lay D) : ValueAt L memory 4096 4 shape (value (D := D)) := by
  have encoded := value_encoding L
  constructor
  · intro i; trivial
  · change WordsAt memory 4096 4 (encodeWords L shape value)
    rw [encoded]
    intro i hi
    have bound : i < 3 := hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel

theorem env_at {D : Deklaration} (L : Lay D) : EnvAt L memory 4096 env := by
  intro τ x
  cases x with
  | here =>
    change ValueAt L memory 4096 4 shape value
    exact input_at L
  | there x => nomatch x

def parameterCode : List II := (constWords [1, 2, 3] FB).1

def parameterMemory : Runner.Mem where
  b a := ((parameterCode.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

end Gabbro.Stage0.Senke.ValueProbe
