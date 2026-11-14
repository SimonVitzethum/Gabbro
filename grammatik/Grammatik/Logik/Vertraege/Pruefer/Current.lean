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
    Except Refusal (PLift (∀ old world locals,
      eval old expression world locals = eval world expression world locals)) :=
  match expression with
  | .lit _ | .tru | .fls | .var _ | .glob .. => .ok ⟨fun _ _ _ => rfl⟩
  | .widen _ _ body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals]⟩
  | .add left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .sub left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .mul left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .neg body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals]⟩
  | .lt left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .le left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .eq left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .and left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .or left right => do
      let a ← currentOnly left
      let b ← currentOnly right
      return ⟨fun old world locals => by
        simp only [eval, a.down old world locals, b.down old world locals]⟩
  | .not body => do
      let checked ← currentOnly body
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals]⟩
  | .slot table field index _ => do
      let checked ← currentOnly index
      return ⟨fun old world locals => by simp only [eval, checked.down old world locals]⟩
  | _ => .error (.unsupported "contract needs an expression independent of old memory")

/-- Translate a return contract once for each typed result. The certificate
    relates the formula to the actual entry world, not a substituted one. -/
def postFormula (program : Programm D) (f : D.Fn) (locals : Env D (D.params f))
    (value : ErgVal D (D.erg f)) :
    Except Refusal { formula : QF (Observation D) // ∀ old world,
      formula.denote (assignment world) ↔ EnsAmRueck program f old world locals value } := do
  let independent ← currentOnly (program.ensures f)
  let encoded ← translate (program.ensures f) (ergEnv (D.erg f) value locals)
  return ⟨lower encoded.payload, fun old world => by
    rw [lower_denote, ← encoded.bool_iff world]
    unfold EnsAmRueck
    rw [independent.down old world]⟩

end Gabbro.Grammatik.Vertraege.Pruefer
