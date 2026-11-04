module

public import Grammatik.Bausteine.Walk.Expansion
public import Grammatik.Parser.Elab.UebersetzeAllg
import all Grammatik.Parser.Elab.Generic.SignatureData

@[expose] public section

namespace Gabbro.Grammatik.WalkBindingWitness
open Parser.Uebersetze Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def shape : WalkShape := { levels := 2, arity := 2, entry := [.opt 2, .bool, .bool], levels_pos := by decide }
def nodeTable : UTab := { name := "Nodes", count := 2, cols := [("entries", (0, 0))], werte := [("entries", .arr (.prodOf 11 shape.entry) 2)] }
def unit : UProg := { tabs := [nodeTable], locks := [], fns := [] }
def declaration : Deklaration := declOf unit

def nodeIndex : declaration.Tab := (⟨0, by decide⟩ : Fin unit.tabs.length)
def entryField : declaration.Feld nodeIndex :=
  (⟨0, by decide +kernel⟩ : Fin (fieldCount unit nodeIndex))

def binding : WalkBinding declaration shape := {
  nodes := nodeIndex
  field := entryField
  entryName := 11
  schema := by rfl
  child := .head
  iterator := nodeIndex
  count := by rfl
  scale := { bytesPerLeaf := 4096, positive := by decide } }

private theorem node_count : declaration.count binding.nodes = 2 := rfl

def leafField : FieldAt shape.entry .bool := .tail .head
def descendField : FieldAt shape.entry .bool := .tail (.tail .head)
def contract : Vertrag declaration := { schreibt := fun _ => false, gschreibt := fun _ => false, erg := none, gruende := 0, haelt := [], produziert := [] }
def oracle : Orakel declaration := { wirkt := fun a _ _ => Fin.elim0 a, regLies := fun r _ => Fin.elim0 r, regSchreib := fun r _ => Fin.elim0 r, sichtbar := fun g _ => Fin.elim0 g }

def rootEntries : Fin 2 → Wert declaration binding.entryTy :=
  fun index =>
    ProdVal.pcons (some (⟨1, by decide, by decide⟩ : Zahl 0 1))
      (ProdVal.pcons (index.val != 0) (ProdVal.pcons true ()))

def childEntries : Fin 2 → Wert declaration binding.entryTy :=
  fun index => ProdVal.pcons none (ProdVal.pcons (index.val == 0) (ProdVal.pcons false ()))

def slots (table : declaration.Tab) (node : Int) (field : declaration.Feld table) :
    Wert declaration (declaration.typ table field) := by
  have tableZero : table = nodeIndex := Fin.ext (by
    have bound := table.isLt
    change table.val < 1 at bound
    change table.val = 0
    omega)
  subst table
  have fieldZero : field = entryField := Fin.ext (by
    have bound := field.isLt
    change field.val < 1 at bound
    change field.val = 0
    omega)
  subst field
  exact if node = 0 then rootEntries else childEntries

def state : World declaration := { slots, globs := fun index => Fin.elim0 index, spur := [] }

def code : WalkCode binding contract [] [] := {
  invariant := fun {Γ} _ _ _ => (Expr.tru : Expr declaration Γ [] .bool)
  leaf := fun {Γ} _ (entry : Expr declaration Γ [] binding.entryTy) => .prodGet entry leafField
  descend := fun {Γ} _ (entry : Expr declaration Γ [] binding.entryTy) => .prodGet entry descendField
  visit := fun {Γ} _ _ _ _ => (Block.nil : Block declaration contract true Γ [] []) }
def root : Wert declaration (.index (declaration.count binding.nodes)) :=
  ⟨0, by decide, by rw [node_count]; decide⟩

/-- The root has one real child, and a leaf which also has that child: leaf selection wins. -/
theorem safe_children_zeuge :
    (visitT (binding.tree state (prodGetW leafField) (prodGetW descendField)) 1
      (binding.entries state root)).map (·.1) =
        [[⟨0, by decide⟩, ⟨0, by decide⟩], [⟨1, by decide⟩]] := by decide +kernel

/-- The generated G expansion reads two root entries and two child entries, never the leaf's child. -/
theorem expansion_reads_zeuge :
    match execBlock oracle 0 (fun index => Fin.elim0 index)
      (binding.walk (loop := false) (by
          intro resource member
          change resource ∈ [] at member
          cases member) code
        (Expr.widen (by decide) (by rw [node_count]; decide) (.lit 0))) state Env.nil with
    | .ok final _ => final.spur.length = 4
    | _ => False := by decide +kernel

/-- All entry fields survive the generated product, with the root index at the highest level. -/
theorem mapping_value_zeuge :
    let value := shape.mappingValue (D := declaration) 19 [⟨1, by decide⟩] (by decide) (by decide)
      (by decide) (rootEntries ⟨1, by decide⟩)
    prodGetW (fs := shape.mappingFields) .head value =
        (some ⟨1, by decide, by decide⟩ : Option (Zahl 0 1)) ∧
      (prodGetW (fs := shape.mappingFields) (.tail (.tail (.tail .head))) value).n = 2 ∧
      (prodGetW (fs := shape.mappingFields) (.tail (.tail (.tail (.tail .head)))) value).n = 1 ∧
      (prodGetW (fs := shape.mappingFields) (.tail (.tail (.tail (.tail (.tail .head))))) value
        ⟨0, by decide⟩).n = 0 ∧
      (prodGetW (fs := shape.mappingFields) (.tail (.tail (.tail (.tail (.tail .head))))) value
        ⟨1, by decide⟩).n = 1 := by decide +kernel

/-- The mapping retains all three original entry fields, including the leaf's live child. -/
theorem mapping_entry_fields_zeuge :
    let value := shape.mappingValue (D := declaration) 19 [⟨1, by decide⟩] (by decide) (by decide)
      (by decide) (rootEntries ⟨1, by decide⟩)
    prodGetW (fs := shape.mappingFields) .head value =
        (some ⟨1, by decide, by decide⟩ : Option (Zahl 0 1)) ∧
      prodGetW (fs := shape.mappingFields) (.tail .head) value = true ∧
      prodGetW (fs := shape.mappingFields) (.tail (.tail .head)) value = true := by decide +kernel

end Gabbro.Grammatik.WalkBindingWitness

namespace Gabbro.Grammatik

/-- A selected child in the existing two-node fixture satisfies both bounds. -/
theorem WalkBinding.child_bounded_zeuge :
    0 ≤ (1 : Int) ∧ (1 : Int) < WalkBindingWitness.declaration.count WalkBindingWitness.binding.nodes :=
  WalkBinding.child_bounded WalkBindingWitness.binding
    (WalkBindingWitness.rootEntries ⟨0, by decide⟩)
    ⟨1, by decide, by rw [WalkBindingWitness.node_count]; decide⟩ (by rfl)

end Gabbro.Grammatik
