module

public import Grammatik.Logik.Invarianten.Pruefer.Writer

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration}

/-- Check the part of the expression language whose value is independent of
    the entry-world parameter. Unsupported forms, including `old`, are refused.
    This is a syntax calculation, not a supplied contract proof. -/
def currentOnly (expression : Expr D Γ Λ τ) :
    Except Invarianten.Frag.Refusal (PLift (∀ old world locals,
      eval old expression world locals = eval world expression world locals)) :=
  match expression with
  | .lit _ | .tru | .fls | .var _ | .glob .. => .ok ⟨fun _ _ _ => rfl⟩
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
  | _ => .error (.unsupported "contract needs an expression independent of old memory")

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
