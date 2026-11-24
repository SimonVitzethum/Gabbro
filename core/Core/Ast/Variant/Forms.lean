module

public import Core.Ast.Variant.Surface
public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def taggedDeclForm (scope : Scope) : Quellform (.declaration scope) Surface.TaggedDeclArgs where
  produktion := Surface.taggedDecl scope
  befehl := fun a => .definiereVariante a.name.val (variantLabels a.cases) (variantPayloads a.cases)
  position := fun _ => 0

def variantValueForm (scope : Scope) : Quellform (.expression scope) (Surface.VariantValueArgs scope) where
  produktion := Surface.variantValue scope
  befehl := fun a => .baueVariante 0 a.ref.name.val a.labels a.payloads a.index
  position := fun a => (caseCode 0 a.payload).code.length

def variantMatchForm (ctx : Scope × Option (Ty .value)) :
    Quellform (.statement ctx.1 ctx.2) (Surface.VariantMatchArgs ctx) where
  produktion := Surface.variantMatch ctx
  befehl := fun a => .waehleVariante 0 a.name a.labels a.payloads (variantArms a.arms).branches
  position := fun a => (expr 0 a.value).code.length

def TaggedDeclBindingAussage : Prop :=
  ∀ scope (a : Surface.TaggedDeclArgs) (frame : Rahmen),
    let next := ((taggedDeclForm scope).befehl a).auswerten frame
    let marker : Dynamisch := ⟨variantSchemaType a.name.val (variantLabels a.cases) (variantPayloads a.cases), PUnit.unit⟩
    next.pc = frame.pc + 1 ∧ next.lokale = some marker :: frame.lokale ∧
      next.globale = some marker :: frame.globale ∧ next.temp = frame.temp

def VariantValuePayloadAussage : Prop :=
  ∀ scope (a : Surface.VariantValueArgs scope) (frame : Rahmen)
    (payload : Wert ((a.payloads.get a.index).getD .productEnd)),
    variantActual (a.payloads.get a.index) (frame.temp 0) = some payload →
    let packed := variantInject a.payloads a.index payload
    let out : Dynamisch := ⟨variantValueType a.ref.name.val a.labels a.payloads, packed⟩
    (((variantValueForm scope).befehl a).auswerten frame).temp 0 = some out ∧
      (variantCase a.payloads packed).1 = a.index.val

def VariantMatchExhaustiveAussage : Prop :=
  ∀ ctx (a : Surface.VariantMatchArgs ctx),
    let branches := (variantArms a.arms).branches
    branches.length = a.payloads.length ∧
      ∀ value : Wert (variantValueType a.name a.labels a.payloads),
        (variantCase a.payloads value).1 < branches.length

def VariantMatchDispatchAussage : Prop :=
  ∀ ctx (a : Surface.VariantMatchArgs ctx) (frame : Rahmen)
    (value : Wert (variantValueType a.name a.labels a.payloads)),
    frame.temp 0 = some ⟨variantValueType a.name a.labels a.payloads, value⟩ →
      let (index, payload) := variantCase a.payloads value
      ∃ offset bind,
        (variantArms a.arms).branches[index]? = some (offset, bind) ∧
        let next := ((variantMatchForm ctx).befehl a).auswerten frame
        next.pc = frame.pc + offset ∧
          next.lokale = (if bind then payload :: frame.lokale else frame.lokale) ∧
          (bind = true → payload.isSome = true) ∧ next.stopp = frame.stopp

end Gabbro.Core.Ast.Semantik
