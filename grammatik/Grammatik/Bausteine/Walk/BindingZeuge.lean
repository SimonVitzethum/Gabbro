module

public import Grammatik.Bausteine.Walk.Expansion
public import Grammatik.Parser.Elab.UebersetzeAllg

@[expose] public section

namespace Gabbro.Grammatik.WalkBindingWitness
open Parser.Uebersetze Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def shape : WalkShape := { levels := 2, arity := 2, entry := [.opt 2, .bool, .bool], levels_pos := by decide }
def nodeTable : UTab := { name := "Nodes", count := 2, cols := [("entries", (0, 0))], werte := [("entries", .arr (.prodOf 11 shape.entry) 2)] }
def unit : UProg := { tabs := [nodeTable], locks := [], fns := [] }
def declaration : Deklaration := declOf unit

def binding : WalkBinding declaration shape := { nodes := 0, field := 0, entryName := 11, schema := by rfl, child := .head, iterator := 0, count := by rfl, scale := { bytesPerLeaf := 4096, positive := by decide } }
def contract : Vertrag declaration := { schreibt := fun _ => false, gschreibt := fun _ => false, erg := none, gruende := 0, haelt := [], produziert := [] }
def oracle : Orakel declaration := { wirkt := fun a _ _ => Fin.elim0 a, regLies := fun r _ => Fin.elim0 r, regSchreib := fun r _ => Fin.elim0 r, sichtbar := fun g _ => Fin.elim0 g }

def rootEntries : Fin 2 → Wert declaration binding.entryTy :=
  fun index => if index.val = 0 then (some ⟨1, by decide, by decide⟩, false, true, ())
    else (some ⟨1, by decide, by decide⟩, true, true, ())

def childEntries : Fin 2 → Wert declaration binding.entryTy :=
  fun index => (none, index.val == 0, false, ())

def slots (table : declaration.Tab) (node : Int) (field : declaration.Feld table) :
    Wert declaration (declaration.typ table field) := by
  have tableZero : table = 0 := Fin.ext (by have := table.isLt; change table.val < 1 at this; omega)
  subst table
  have fieldZero : field = 0 := Fin.ext (by have := field.isLt; change field.val < 1 at this; omega)
  subst field
  exact if node = 0 then rootEntries else childEntries

def state : World declaration := { slots, globs := fun index => Fin.elim0 index, spur := [] }

def code : WalkCode binding contract [] [] := { invariant := fun _ _ _ => .tru, leaf := fun _ entry => .prodGet entry (.tail .head), descend := fun _ entry => .prodGet entry (.tail (.tail .head)), visit := fun _ _ _ _ => .nil }
def root : Zahl 0 1 := ⟨0, by decide, by decide⟩

/-- The root has one real child, and a leaf which also has that child: leaf selection wins. -/
theorem safe_children_zeuge :
    (visitT (binding.tree state (fun entry => entry.2.1) (fun entry => entry.2.2.1)) 1
      (binding.entries state root)).map (·.1) = [[0, 0], [1]] := by decide +kernel

/-- The generated G expansion reads two root entries and two child entries, never the leaf's child. -/
theorem expansion_reads_zeuge :
    match execBlock oracle 0 (fun index => Fin.elim0 index)
      (binding.walk (loop := false) (by intro resource member; cases member) code
        (Expr.widen (by decide) (by decide) (.lit 0))) state Env.nil with
    | .ok final _ => final.spur.length = 4
    | _ => False := by decide +kernel

/-- All entry fields survive the generated product, with the root index at the highest level. -/
theorem mapping_value_zeuge :
    let value := shape.mappingValue (D := declaration) 19 [(1 : Fin 2)] (by decide) (by decide)
      (by decide) (rootEntries 1)
    value.1 = (some ⟨1, by decide, by decide⟩ : Option (Zahl 0 1)) ∧
      value.2.2.2.1.n = 2 ∧ value.2.2.2.2.1.n = 1 ∧
      (value.2.2.2.2.2.1 0).n = 0 ∧ (value.2.2.2.2.2.1 1).n = 1 := by decide +kernel

end Gabbro.Grammatik.WalkBindingWitness
