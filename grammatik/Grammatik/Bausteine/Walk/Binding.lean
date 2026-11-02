module

public import Grammatik.Bausteine.Walk.Position
public import Grammatik.Kern.Syntax.Zucker

@[expose] public section

namespace Gabbro.Grammatik

/-- Safe finite node storage: a node is an existing cell holding an entry array. Children are bounded
    indices into that same declared storage. A raw numeric address cannot inhabit this interface. -/
structure WalkBinding (D : Deklaration) (shape : WalkShape) where
  nodes : D.Tab
  field : D.Feld nodes
  entryName : Nat
  schema : D.typ nodes field = .arr (.prod entryName shape.entry) shape.arity
  child : FieldAt shape.entry (.opt (D.count nodes))
  iterator : D.Tab
  count : D.count iterator = (shape.arity : Int)
  scale : WalkScale

abbrev WalkBinding.entryTy {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape) : Ty :=
  .prod binding.entryName shape.entry

/-- This view uses the actual declared memory, not an unrelated flattened table. -/
def WalkBinding.entries {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    (state : World D) (node : Wert D (.index (D.count binding.nodes))) :
    Fin shape.arity → Wert D binding.entryTy :=
  cast (congrArg (Wert D) binding.schema) (state.slots binding.nodes node.n binding.field)

/-- The only child selection is a checked optional index stored in the entry. -/
def WalkBinding.tree {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    (state : World D) (leaf descend : Wert D binding.entryTy → Bool) : WalkTree (Wert D binding.entryTy) shape.arity :=
  { leaf, dwhen := descend, down := fun entry => (prodGetW binding.child entry).map (binding.entries state) }

theorem WalkBinding.child_bounded {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    (entry : Wert D binding.entryTy) (node : Wert D (.index (D.count binding.nodes)))
    (_selected : prodGetW binding.child entry = some node) :
    0 ≤ node.n ∧ node.n < D.count binding.nodes := by
  have lower := node.lo_le
  have upper := node.le_hi
  exact ⟨lower, by omega⟩

/-- The stored child view and the pure enumeration use exactly the same resolved child cell. -/
theorem WalkBinding.tree_down {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    (state : World D) (leaf descend : Wert D binding.entryTy → Bool)
    (entry : Wert D binding.entryTy) :
    (binding.tree state leaf descend).down entry =
      (prodGetW binding.child entry).map (binding.entries state) := rfl

/-- Casts of typed expressions commute with evaluation and do not alter carrier footprints. -/
theorem eval_typeCast {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {sourceTy targetTy : Ty}
    (same : sourceTy = targetTy) (expression : Expr D Γ Λ sourceTy) (entry state : World D) (env : Env D Γ) :
    eval entry (same ▸ expression) state env = (same ▸ eval entry expression state env) := by
  cases same
  rfl

theorem Expr.orte_typeCast {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {sourceTy targetTy : Ty}
    (same : sourceTy = targetTy) (expression : Expr D Γ Λ sourceTy) :
    (same ▸ expression).orte = expression.orte := by cases same; rfl

/-- A guarded G read of one entry from a resolved node. Both coordinates remain bounded. -/
def WalkBinding.readEntry {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    {Γ : Ctx} {Λ : List (Res D)} (guard : darf D binding.nodes Λ)
    (node : Expr D Γ Λ (.index (D.count binding.nodes)))
    (index : Expr D Γ Λ (.index shape.arity)) : Expr D Γ Λ binding.entryTy :=
  .arrGet (binding.schema ▸ Expr.slot binding.nodes binding.field node guard) index

theorem WalkBinding.readEntry_eval {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    {Γ : Ctx} {Λ : List (Res D)} (guard : darf D binding.nodes Λ)
    (node : Expr D Γ Λ (.index (D.count binding.nodes))) (index : Expr D Γ Λ (.index shape.arity))
    (entry state : World D) (env : Env D Γ) :
    eval entry (binding.readEntry guard node index) state env =
      binding.entries state (eval entry node state env) (eval entry index state env).fin := by
  have hc := eval_typeCast binding.schema (Expr.slot binding.nodes binding.field node guard) entry state env
  unfold WalkBinding.readEntry
  simp only [eval]
  simp only [hc]
  unfold WalkBinding.entries
  generalize eval entry index state env = i
  apply congrFun
  apply eq_of_heq
  refine (eqRec_heq _ _).trans ?_
  refine HEq.trans ?_ (cast_heq _ _).symm
  exact HEq.rfl

/-- Subfields do not split a node carrier into independent locks or race locations. -/
theorem WalkBinding.readEntry_orte {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    {Γ : Ctx} {Λ : List (Res D)} (guard : darf D binding.nodes Λ)
    (node : Expr D Γ Λ (.index (D.count binding.nodes))) (index : Expr D Γ Λ (.index shape.arity)) :
    (binding.readEntry guard node index).orte = (.inl binding.nodes :: node.orte) ++ index.orte := by
  change (binding.schema ▸ Expr.slot binding.nodes binding.field node guard).orte ++ index.orte = _
  rw [Expr.orte_typeCast]
  rfl

/-- Reading the node cells never rewrites them: `World.lese` only records events. -/
@[simp] theorem WalkBinding.entries_lese {D : Deklaration} {shape : WalkShape}
    (binding : WalkBinding D shape) (σ : World D) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) (node : Wert D (.index (D.count binding.nodes))) :
    binding.entries (σ.lese Λ os) node = binding.entries σ node := rfl

/-- Mapping membership is tied to safe node storage, including shared children at distinct paths. -/
theorem WalkBinding.mappings_mem_iff {D : Deklaration} {shape : WalkShape} (binding : WalkBinding D shape)
    (state : World D) (leaf descend : Wert D binding.entryTy → Bool)
    (node : Wert D (.index (D.count binding.nodes))) (level : Nat)
    (path : List (Fin shape.arity)) (entry : Wert D binding.entryTy) :
    (path, entry) ∈ visitT (binding.tree state leaf descend) level (binding.entries state node) ↔
      WalkHit (binding.tree state leaf descend) level (binding.entries state node) path entry :=
  visitT_mem_iff _ _ _ _ _

end Gabbro.Grammatik
