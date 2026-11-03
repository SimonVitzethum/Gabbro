module
public import Grammatik.Parser.Elab.Konst.Values.Export

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst
open Uebersetze

/-- Both result families expose one replacement interface, retaining their exact
    source certificates. Integer results additionally retain bounded/KExpr checks. -/
inductive ReplacementEvidence (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) : SExpr → Type where
  | integer (call : Scalar.CheckedCall k fns env sources) :
      ReplacementEvidence k fns env sources (literalVonInt call.value)
  | portable (call : Values.CheckedCall k fns env sources) :
      ReplacementEvidence k fns env sources call.quoted.syntax

structure Replacement (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) where
  syntax : SExpr
  evidence : ReplacementEvidence k fns env sources syntax

/-- The one production entry point for certified value replacement. -/
def checkReplacement (k : UKonstFn) (fns : List UKonstFn)
    (env : List (String × Int)) (sources : List SExpr) :
    Except String (Replacement k fns env sources) := do
  match k.erg with
  | .int _ _ =>
    let checked ← Scalar.checkCall k fns env sources
    return ⟨literalVonInt checked.value, .integer checked⟩
  | _ =>
    if Values.resultType k.erg then
      let checked ← Values.checkCall k fns env sources
      return ⟨checked.quoted.syntax, .portable checked⟩
    else throw ("const result type without a certified replacement at `" ++ k.name ++ "`")

/-- A shared semantic interface: each replacement retains the generic ordinary
    G-call theorem, and either the normalized scalar candidate or the complete
    typed literal denotation. No semantic obligation is a caller premise. -/
def ReplacementEvidence.Sound : {syntax : SExpr} → ReplacementEvidence k fns env sources syntax → Prop
  | _, .integer call =>
    (Scalar.expression (Scalar.locals k.params)
      (Scalar.normalizeNames (Scalar.locals k.params) k.constants call.function.source) =
        .ok ⟨_, call.function.model.body.2.2⟩) ∧
    (∀ before after,
      uKonstWert call.lo call.hi fns call.bindings 64
        (Scalar.normalizeNames (Scalar.locals k.params) k.constants call.function.source) =
        some (eval before call.function.model.body.2.2.expr after call.args).n) ∧
    (∀ σ O passes depth,
      rufAt call.function.model.program O passes (depth + 1) () σ call.args =
        .ok σ (⟨call.value, call.certificate.range.1, call.certificate.range.2⟩ : Zahl call.lo call.hi))
  | _, .portable call =>
    ∀ σ O passes depth,
      rufAt call.function.model.program O passes (depth + 1) () σ call.args = .ok σ call.value ∧
      eval σ call.quoted.expr σ call.args = call.value ∧
      Values.LiteralMeaning (Scalar.declaration (k.params.map Prod.snd) k.erg)
        (Values.resultSchemas k) k.erg call.quoted.syntax call.value

theorem Replacement.sound (replacement : Replacement k fns env sources) : replacement.evidence.Sound := by
  rcases replacement with ⟨syntax, evidence⟩
  cases evidence with
  | integer call => exact ⟨call.function.normalized, call.normalized_denotation, call.sound⟩
  | portable call => exact call.sound

end Gabbro.Grammatik.Parser.Konst
