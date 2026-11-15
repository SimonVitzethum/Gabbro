/- Small joint witness for stored-array lowering, without evaluating a program image. -/
module
public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Welt.AnordnungLayout
public import Stage0.Senke.Images.BildLese
@[expose] public section

namespace Gabbro.Stage0.Senke.StoredProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

def unit : UProg := { tabs := [], locks := [], fns := [] }
abbrev D := declOf unit
def layout : Lay D := layU unit (fun _ => none) 65536
def world : World D where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

abbrev element : Ty := .int 0 255
abbrev shape : Ty := .arr element 3
def value : Wert D shape := fun i => ⟨i.val + 1, by omega, by have := i.isLt; omega⟩
def env : Env D [shape] := .cons value .nil
def expression : Expr D [shape] [] element :=
  .arrGet (.var .here) (.widen (by decide) (by decide) (.lit 1))

def code : List II :=
  [ci 17 8 4 0, ci 1 9 1 0, ci 1 10 8 0, ci 5 9 9 10, ci 3 8 8 9] ++
    loadPointerSpan 1 7 8 10 0

def memory : Runner.Mem where
  b a := if a.toNat < 128 then ((code.flatMap encII)[a.toNat]?).getD 0
    else if a.toNat = 4128 then 1 else if a.toNat = 4136 then 2
    else if a.toNat = 4144 then 3 else 0
  rd _ := true
  wr _ := true

theorem bytes : BytesAt memory 0 (code.flatMap encII) := by
  intro i hi
  have length : (code.flatMap encII).length = 128 := by decide +kernel
  have small : i < 2 ^ 64 := by omega
  refine ⟨rfl, rfl, ?_⟩
  simp only [memory, Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    if_pos (by omega : i < 128), List.getElem?_eq_getElem hi, Option.getD_some]

theorem source : ValueAt layout memory 4096 4 shape value := by
  refine ⟨fun _ => trivial, ?_⟩
  have encoding : encodeWords layout shape value = [1, 2, 3] := by
    simp only [encodeWords.eq_def, shape, element, elementEncoding]
    rfl
  rw [encoding]
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
  rcases cases with rfl | rfl | rfl <;> rfl

theorem pre [Kern] : PreS layout memory 0 4096 16 7 code env := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    codeAt_bytes code 0 (by decide) bytes, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar
    decide
  · intro τ x
    cases x with
    | here => exact source
    | there x => nomatch x

theorem layout_in : LayIn layout :=
  ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), by decide⟩

theorem world_at (m : Runner.Mem) : WeltAt m layout world := by
  refine ⟨(fun t => Fin.elim0 t), (fun g => Fin.elim0 g), ?_⟩
  intro x low high
  change 65536 ≤ x at low
  change x < 65536 at high
  omega

/-- Every premise is inhabited together: three distinct stored elements, a real
    frame, emitted instructions and the unchanged complete expression simulation. -/
theorem lowE_ok_zeuge [Kern] :
    lowE layout expression 7 = some (code, 11) ∧
    PreS layout memory 0 4096 16 7 code env ∧
    (eval world expression world env).n = 2 ∧
    ValueOk layout memory 0 4096 16 7 code element (eval world expression world env) := by
  have lowered : lowE layout expression 7 = some (code, 11) := by rfl
  exact ⟨lowered, pre, rfl, lowE_ok (same := by intro _; rfl) world world
    (fun m _ => world_at m) layout_in expression 7 code 11 lowered (by decide) memory 0 env pre⟩

/-- The child-induction premise of address correctness is inhabited by the same
    nonempty storage fixture; it is not made true by refusing the expression. -/
theorem lowStorage_sound_zeuge [Kern] :
    StorageChildrenOk (L := layout) (currentOld := true) world world env 4096 16 0
      (fun _ => True) (Expr.var (D := D) (Λ := []) (Var.here : Var [shape] shape)) ∧
    lowStorage layout (Expr.var (D := D) (Λ := []) (Var.here : Var [shape] shape)) 8 =
      some ([ci 17 8 4 0], 9) :=
  ⟨trivial, rfl⟩

end Gabbro.Stage0.Senke.StoredProbe
