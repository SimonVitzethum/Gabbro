module

public import Core.Ast.Aggregate.RecordSurface
public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Gabbro.Core.Text

def recordDeclForm (scope : Scope) : Quellform (.declaration scope) Surface.RecordDeclArgs where
  produktion := Surface.recordDecl scope
  befehl := fun a => .definiereRecord a.name.val (recordLabels a.members) (recordTypes a.members)
  position := fun _ => 0

def recordValueForm (scope : Scope) : Quellform (.expression scope) (Surface.RecordValueArgs scope) where
  produktion := Surface.recordValue scope
  befehl := fun a => .baueRecord 0 a.ref.name.val a.labels a.types
    (List.ofFn fun i : Fin a.types.length => (a.fields.slot i).val)
  position := fun a => (labeledCode 0 a.args).code.length

def recordFieldForm (scope : Scope) : Quellform (.expression scope) (Surface.RecordFieldArgs scope) where
  produktion := Surface.recordField scope
  befehl := fun a => .liesRecordFeld 0 a.name a.labels a.types a.index
  position := fun a => (expr 0 a.base).code.length

def assignFieldForm (ctx : Scope × Option (Ty .value)) :
    Quellform (.statement ctx.1 ctx.2) (Surface.AssignFieldArgs ctx.1) where
  produktion := Surface.assignField ctx
  befehl := fun a => .setzeRecordFeld 0 a.ref.index a.name a.labels a.types a.index
  position := fun a => (expr 0 a.value).code.length

def mutableValueForm (ctx : Scope × Option (Ty .value)) :
    Quellform (.statement ctx.1 ctx.2) (Surface.MutableValueArgs ctx.1) where
  produktion := Surface.mutableValue ctx
  befehl := fun a => .bindeWert 0 a.type false
  position := fun a => (expr 0 a.value).code.length

def tupleBindForm (ctx : Scope × Option (Ty .value)) :
    Quellform (.statement ctx.1 ctx.2) (Surface.TupleBindArgs ctx.1) where
  produktion := Surface.tupleBind ctx
  befehl := fun a => .bindeTupel 0 a.types (a.pattern.names.map Option.isSome)
  position := fun a => (expr 0 a.value).code.length

/-- The schema marker is the statement's only change to the local stack. -/
def RecordDeclBindingAussage : Prop :=
  ∀ scope (args : Surface.RecordDeclArgs) (frame : Rahmen),
    let next := ((recordDeclForm scope).befehl args).auswerten frame
    next.lokale = some ⟨(recordBinding args.name args.members).type, PUnit.unit⟩ :: frame.lokale ∧
      next.pc = frame.pc + 1 ∧ next.temp = frame.temp

/-- Construction permutes values only after all actuals have been evaluated. -/
def RecordValueSlotsAussage : Prop :=
  ∀ scope (args : Surface.RecordValueArgs scope) (frame : Rahmen)
    (actual : Wert (tupleType args.actualTypes)),
    (∀ i : Fin args.actualTypes.length,
      frame.temp i.val = some ⟨args.actualTypes.get i, tupleGet args.actualTypes i actual⟩) →
    let packed : Wert (recordValueType args.ref.name.val args.labels args.types) :=
      tupleOfFn args.types fun i => Wert.widen (args.actualTypes.get (args.fields.slot i)) (args.types.get i)
        (args.fits i) (tupleGet args.actualTypes (args.fields.slot i) actual)
    (((recordValueForm scope).befehl args).auswerten frame).temp 0 =
      some ⟨recordValueType args.ref.name.val args.labels args.types, packed⟩

def RecordFieldValueAussage : Prop :=
  ∀ scope (args : Surface.RecordFieldArgs scope) (frame : Rahmen)
    (record : Wert (recordValueType args.name args.labels args.types)),
    frame.temp 0 = some ⟨recordValueType args.name args.labels args.types, record⟩ →
    (((recordFieldForm scope).befehl args).auswerten frame).temp 0 =
      some ⟨args.types.get args.index, tupleGet args.types args.index record⟩

def AssignFieldFrameAussage : Prop :=
  ∀ ctx (args : Surface.AssignFieldArgs ctx.1) (frame : Rahmen)
    (record : Wert (recordValueType args.name args.labels args.types)) (value : Wert args.source),
    frame.lokale[args.ref.index]? = some (some ⟨recordValueType args.name args.labels args.types, record⟩) →
    frame.temp 0 = some ⟨args.source, value⟩ →
    let next := ((assignFieldForm ctx).befehl args).auswerten frame
    let widened := Wert.widen args.source (args.types.get args.index) args.fits value
    next.lokale[args.ref.index]? =
      some (some ⟨recordValueType args.name args.labels args.types, tupleSet args.types args.index widened record⟩) ∧
      (∀ i, i ≠ args.ref.index → next.lokale[i]? = frame.lokale[i]?) ∧
      next.pc = frame.pc + 1 ∧ next.temp = frame.temp

def TupleBindLocalsAussage : Prop :=
  ∀ ctx (args : Surface.TupleBindArgs ctx.1) (frame : Rahmen) (value : Wert (tupleType args.types)),
    frame.temp 0 = some ⟨tupleType args.types, value⟩ →
    let next := ((tupleBindForm ctx).befehl args).auswerten frame
    next.lokale = (tupleLocals args.types value (args.pattern.names.map Option.isSome)).reverse ++ frame.lokale ∧
      next.lokale.length = (args.pattern.bindings args.types).length + frame.lokale.length ∧
      next.pc = frame.pc + 1 ∧ next.temp = frame.temp

end Gabbro.Core.Ast.Semantik
