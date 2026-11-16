module

public import Grammatik.Logik.Invarianten.Pruefer.Writer

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration}

mutual

/-- Check the part of the expression language whose value is independent of
    the entry-world parameter. Unsupported forms, including `old`, are refused.
    This is a syntax calculation, not a supplied contract proof. -/
def currentOnly (expression : Expr D Γ Λ τ) :
    Except Invarianten.Frag.Refusal (PLift (∀ old world locals,
      eval old expression world locals = eval world expression world locals)) :=
  match expression with
  | .lit _ | .tru | .fls | .var _ | .glob .. | .ptrOf .. | .fnref ..
    | .none _ | .why .. | .arrNil | .strLit .. => .ok ⟨fun _ _ _ => rfl⟩
  | .widen _ _ body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .add left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .sub left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .mul left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .neg body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .lt left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .le left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .eq left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .and left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .or left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .not body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .slot table field index _ | .thru _ table _ field index _ => do
      let checked ← currentOnly index
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .thruOwn _ _ _ _ index _ _ _ _ _ _ => do
      let checked ← currentOnly index
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .div _ _ left right | .rem _ _ left right | .sdiv _ left right | .srem _ left right
    | .band _ _ left right | .bor _ _ _ _ _ left right | .bxor _ _ _ _ _ left right
    | .shl _ _ _ _ _ left right | .shr _ _ _ _ _ left right
    | .fllt left right | .flle left right | .refEq left right
    | .arrCons left right | .arrGet left right
    | .strCat left right | .strGet left right | .strEq left right | .strLt left right
    | .intBuiltin2 _ left right | .prodSet left _ right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals] <;> rfl⟩
  | .some body | .istSome body | .slotRef body _ _ _ _ _
    | .strLen body | .strWeit _ body | .intBuiltin1 _ body | .prodGet body _ => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .getBytes _ _ _ _ index _ _ _ => do
      let checked ← currentOnly index
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals] <;> rfl⟩
  | .forallSlots _ body _ | .existsSlots _ body _ | .count _ body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world]⟩
  | .reaches _ _ _ left right _ => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .wenn test left right | .arrSet test left right => do
      let guard ← currentOnly test
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, guard.down old world locals, a.down old world locals, b.down old world locals]⟩
  | .eng body _ _ fallback => do
      let a ← currentOnly body
      let b ← currentOnly fallback
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .case _ _ payload => do
      let checked ← currentPayload payload
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals]⟩
  | .prod _ fields => do
      let checked ← currentProduct fields
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals]⟩
  | .oldG .. | .oldS .. =>
      .error (.unsupported "old memory needs a distinct entry-world snapshot observation")

def currentPayload (expression : NutzlastExpr D Γ Λ kind) :
    Except Invarianten.Frag.Refusal (PLift (∀ old world locals,
      evalNutz old expression world locals = evalNutz world expression world locals)) :=
  match expression with
  | .empty => .ok ⟨fun _ _ _ => rfl⟩
  | .val body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => checked.down old world locals⟩

def currentProduct (fields : Args D Γ Λ types) :
    Except Invarianten.Frag.Refusal (PLift (∀ old world locals,
      evalProd old fields world locals = evalProd world fields world locals)) :=
  match fields with
  | .nil => .ok ⟨fun _ _ _ => rfl⟩
  | .cons head tail => do
      let first ← currentOnly head
      let rest ← currentProduct tail
      return ⟨fun old world locals => by
        simp only [evalProd, first.down old world locals, rest.down old world locals]⟩

end

/-- Translate a return contract once for each typed result. The certificate
    relates the formula to the actual entry world, not a substituted one. -/
def postFormula (program : Programm D) (f : D.Fn) (locals : Env D (D.params f))
    (value : ErgVal D (D.erg f)) :
    Except Invarianten.Frag.Refusal { formula : QF (Observation D) // ∀ old world,
      formula.denote (assignment world) ↔ EnsAmRueck program f old world locals value } := do
  let independent ← currentOnly (program.ensures f)
  let encoded ← translate (program.ensures f) (ergEnv (D.erg f) value locals)
  let formula : LProp (Observation D) := encoded.payload
  return ⟨lower formula, fun old world => by
    apply (lower_denote formula (assignment world)).trans
    apply (encoded.bool_iff world).symm.trans
    unfold EnsAmRueck
    rw [independent.down old world]⟩

end Gabbro.Grammatik.Vertraege.Pruefer
