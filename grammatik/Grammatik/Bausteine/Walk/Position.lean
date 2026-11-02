module

public import Grammatik.Bausteine.Walk.Abbildung
public import Grammatik.Kern.Syntax.Syntax.Teil2

@[expose] public section

namespace Gabbro.Grammatik

/-- Root-to-entry position `j` belongs to level `L - 1 - j`, not the reversed level. -/
theorem walkIndexAt_path {N : Nat} (levels : Nat) (path : List (Fin N)) (j : Nat)
    (depth : path.length ≤ levels) (active : j < path.length) :
    walkIndexAt levels path (levels - 1 - j) = ((path[j]?).map (·.val)).getD 0 := by
  have above : ¬ levels - 1 - j < levels - path.length := by omega
  have below : levels - 1 - j < levels := by omega
  have position : levels - 1 - (levels - 1 - j) = j := by omega
  simp only [walkIndexAt, above, if_false, below, if_true, position]

theorem walkIndexAt_lt {N : Nat} (levels : Nat) (path : List (Fin N)) (ell : Nat) (positive : 0 < N) :
    walkIndexAt levels path ell < N := by
  unfold walkIndexAt
  split
  · exact positive
  · split
    · cases found : path[levels - 1 - ell]? with
      | none => simpa only [found, Option.map_none, Option.getD_none] using positive
      | some index => simpa only [found, Option.map_some, Option.getD_some] using index.isLt
    · exact positive

/-- A byte coordinate requires an explicit positive layout scale; logical `va` stays in leaf units. -/
structure WalkScale where
  bytesPerLeaf : Nat
  positive : 0 < bytesPerLeaf

def WalkScale.byteVa (scale : WalkScale) (levels N : Nat) (path : List (Fin N)) : Nat :=
  scale.bytesPerLeaf * walkVa levels N path

theorem WalkScale.byteVa_lt (scale : WalkScale) (levels N : Nat) (path : List (Fin N))
    (positive : 0 < N) (depth : path.length ≤ levels) :
    scale.byteVa levels N path < scale.bytesPerLeaf * N ^ levels :=
  Nat.mul_lt_mul_of_pos_left (walkVa_lt levels N path positive depth) scale.positive

/-- Append field values in declaration order. This is unrelated to reverse local-context placement. -/
def ProdVal.appendFields {F : Type} {fits : F → Nat → Bool} :
    (fields tail : List Ty) → ProdVal F fits fields → ProdVal F fits tail →
      ProdVal F fits (fields ++ tail)
  | [], _, _, rest => rest
  | _ :: fields, tail, values, rest =>
    (values.1, ProdVal.appendFields fields tail values.2 rest)

/-- Each entry contributes every field, plus the exact logical coordinates, at the declared mapping type. -/
def WalkShape.mappingValue {D : Deklaration} (shape : WalkShape) (name : Nat)
    (path : List (Fin shape.arity)) (nonempty : 0 < path.length) (depth : path.length ≤ shape.levels)
    (positive : 0 < shape.arity) (entry : ProdVal D.Fn D.passt shape.entry) :
    Wert D (shape.mappingTy name) := by
  have vaBound : (walkVa shape.levels shape.arity path : Int) < (shape.arity : Int) ^ shape.levels := by
    exact_mod_cast walkVa_lt shape.levels shape.arity path positive depth
  have levelBound : shape.levels - path.length < shape.levels := by omega
  have levelCast : ((shape.levels - path.length : Nat) : Int) < (shape.levels : Int) := by exact_mod_cast levelBound
  let va : Zahl 0 ((shape.arity : Int) ^ shape.levels - 1) := ⟨walkVa shape.levels shape.arity path, by omega, by omega⟩
  let level : Zahl 0 ((shape.levels : Int) - 1) := ⟨((shape.levels - path.length : Nat) : Int), by omega, by omega⟩
  let indices : Wert D shape.indexTy := fun index =>
    let bound := walkIndexAt_lt shape.levels path index.val positive
    let castBound : (walkIndexAt shape.levels path index.val : Int) < (shape.arity : Int) := by exact_mod_cast bound
    ⟨walkIndexAt shape.levels path index.val, by omega, by omega⟩
  exact ProdVal.appendFields shape.entry [shape.vaTy, shape.levelTy, shape.indexTy] entry (va, level, indices, ())

theorem walkIndexAt_path_zeuge :
    walkIndexAt 3 [(1 : Fin 4), 2] (3 - 1 - 0) = 1 ∧
    walkIndexAt 3 [(1 : Fin 4), 2] (3 - 1 - 1) = 2 := by decide

theorem WalkScale.byteVa_lt_zeuge :
    ({ bytesPerLeaf := 4096, positive := by decide } : WalkScale).byteVa 3 4 [1, 2] = 98304 ∧
    ({ bytesPerLeaf := 4096, positive := by decide } : WalkScale).byteVa 3 4 [1, 2] < 4096 * 4 ^ 3 := by
  constructor
  · decide
  · exact WalkScale.byteVa_lt _ 3 4 [1, 2] (by decide) (by decide)

end Gabbro.Grammatik
