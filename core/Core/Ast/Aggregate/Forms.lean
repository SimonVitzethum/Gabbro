module

public import Core.Ast.Aggregate.Syntax
public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog

def arrayValueForm (scope : Scope) : Quellform (.expression scope) (Surface.ArrayValueArgs scope) where
  produktion := Surface.arrayValue scope
  befehl := fun args => .baueArray 0 args.element args.types.length
  position := fun args => (itemCode 0 args.items).code.length

def arrayIndexForm (scope : Scope) : Quellform (.expression scope) (Surface.ArrayIndexArgs scope) where
  produktion := Surface.arrayIndex scope
  befehl := fun args => .liesArray 0 args.element args.count
  position := fun args => ((expr 0 args.base).anhaengen (expr 1 args.offset)).code.length

def tupleValueForm (scope : Scope) : Quellform (.expression scope) (Surface.TupleValueArgs scope) where
  produktion := Surface.tupleValue scope
  befehl := fun args => .baueTupel 0 args.types
  position := fun args => (((expr 0 args.first).anhaengen (expr 1 args.second)).anhaengen
    (itemCode 2 args.tail)).code.length

def tupleFieldForm (scope : Scope) : Quellform (.expression scope) (Surface.TupleFieldArgs scope) where
  produktion := Surface.tupleField scope
  befehl := fun args => .liesTupelfeld 0 args.types args.index
  position := fun args => (expr 0 args.base).code.length

/-- A typed pre-state reports the actual checked offset and size in the partial-operation table. -/
def ArrayIndexGuardAussage : Prop :=
  ∀ (frame : Rahmen) (slot : Nat) (element : Ty .value) (count : Nat)
    (values : Vector (Wert element) count) {lo hi : Int} (offset : Zahl lo hi)
    (lower : 0 ≤ lo) (upper : hi < (count : Int)),
    frame.temp slot = some ⟨.array element count, values⟩ →
    frame.temp (slot + 1) = some ⟨.int lo hi, offset⟩ →
    let position := indexPosition offset lower upper
    (Befehl.liesArray slot element count).guard frame = some ⟨.index, (position.val, count)⟩ ∧
      waechterBedarf .index (position.val, count) ∧
      ((Befehl.liesArray slot element count).auswerten frame).temp slot =
        some ⟨element, values[position.val]'position.isLt⟩

end Gabbro.Core.Ast.Semantik
