module
public import Stage0.Frontend.ConstantScopes
public import Stage0.Frontend.AliasMeaning
public import Stage0.Frontend.Guard
public import Stage0.Profil
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Source provenance and the complete declaration normalization derivation consumed by Stage0.
    Lexing/parsing are the canonical functions; pre108 retains its visibility and name checks. -/
structure Source (text : String) (options : Profil.Options := {}) where
  tokens : List Token
  items : List SItemTief
  members : List SItemTief
  lexed : lex text = .ok tokens
  parsed : parseTopTief tokens = .ok items
  prepared : Profil.Prepared options items
  visibility : Oeffentlich.huelleZu items = true
  compileTime : compileTimeSafe (uMembers (pre108 items)) = true
  normalized : Normalization (uMembers (pre108 items)) members
  aliasDependencies : AliasAcyclic (uMembers (pre108 items)) ∧
    (aliasNames (uMembers (pre108 items))).Nodup
  constantDependencies : ConstantAcyclic (uMembers (pre108 items)) ∧
    (constantNames (uMembers (pre108 items))).Nodup
  derived : DerivedScopes (uMembers (pre108 items))
  aliasMeanings : ∀ item ∈ uMembers (pre108 items), AliasMeaning derived.scope.types item
  constantMeanings : ∀ item ∈ uMembers (pre108 items),
    ConstantMeaning derived.scope.types derived.scope.functions derived.scope.values item

/-- The actual whole-source frontend, producing a proof of provenance and normalization. -/
def source (text : String) (options : Profil.Options := {}) : Except String (Source text options) :=
  match hl : lex text with
  | .error _ => .error "lex"
  | .ok tokens =>
    match hp : parseTopTief tokens with
    | .error e => .error e
    | .ok items =>
      match Profil.prepareItems options items with
      | .error e => .error e
      | .ok prepared =>
        if hv : Oeffentlich.huelleZu items then
          if hc : compileTimeSafe (uMembers (pre108 items)) then do
            let order ← orderAliases (uMembers (pre108 items))
            let result := normalize (uMembers (pre108 items))
            match hd : elaborateConstantScopes (uMembers (pre108 items)) with
            | .error e => .error e
            | .ok derived =>
              if ha : (uMembers (pre108 items)).all (checkAliasMeaning derived.scope.types) then
                if hs : (uMembers (pre108 items)).all
                    (checkConstantMeaning derived.scope.types derived.scope.functions derived.scope.values) then
                  .ok ⟨tokens, items, result.val, hl, hp, prepared, hv, hc, result.property,
                    ⟨order.acyclic, order.unique⟩, elaborateConstantScopes_dependencies _ derived hd,
                    derived, fun item hm =>
                      checkAliasMeaning_sound _ _ (List.all_eq_true.mp ha item hm), fun item hm =>
                      checkConstantMeaning_sound _ _ _ _ (List.all_eq_true.mp hs item hm)⟩
                else .error "compile-time constant does not match its canonical source value"
              else .error "compile-time alias does not match its canonical source type"
          else .error "compile-time call requires unsupported function contracts, effects or body"
        else .error "public interface is not closed"

/-- Successful frontend extraction carries canonical lexer/parser provenance, the original
    compile-time call guard and local declaration rewrite facts. Whole-program denotational
    preservation is a separate obligation, not implied by projecting this certificate. -/
theorem source_sound (text : String) {options : Profil.Options} (result : Source text options) :
    lex text = .ok result.tokens ∧ parseTopTief result.tokens = .ok result.items ∧
    Oeffentlich.huelleZu result.items = true ∧
    compileTimeSafe (uMembers (pre108 result.items)) = true ∧
    Normalization (uMembers (pre108 result.items)) result.members ∧
    ScopeStable result.derived.scope :=
  ⟨result.lexed, result.parsed, result.visibility, result.compileTime, result.normalized, result.derived.stable⟩

/-- A successful frontend uses exactly canonical name resolution and width normalization;
    visibility failures cannot be hidden by flattening the item list. -/
theorem source_names (text : String) {options : Profil.Options} (result : Source text options) :
    pre108 result.items = normTopU32 (Aufloesung.loese result.items) := by
  simp only [pre108, result.visibility, ↓reduceIte]

/-- A scalar compile-time call from the original source has a complete safe call-hull derivation
    before normalization, so a later baseline evaluator is never the first contract check. -/
theorem source_constant_hull (text : String) {options : Profil.Options} (result : Source text options)
    (name : String) (ty : STyp) (expr : SExpr)
    (hm : SItemTief.constT name ty (.one expr) ∈ uMembers (pre108 result.items))
    (callee : String) (hc : callee ∈ calls expr) :
    SafeHull (uMembers (pre108 result.items)) [] callee := by
  have h := compileTimeSafe_constants result.compileTime hm
  exact safeConstantName_sound _ _ _ _ ((List.all_eq_true.mp h) callee hc)

/-- The original-source guard covers every scalar leaf in nested constant arrays, before
    the frozen uKonstArrays/uKonstFns path can evaluate it. -/
theorem source_constant_leaf_hull (text : String) {options : Profil.Options} (result : Source text options)
    (name : String) (ty : STyp) (value : SKonstWert) (expr : SExpr)
    (hm : SItemTief.constT name ty value ∈ uMembers (pre108 result.items))
    (leaf : ConstantLeaf expr value) (callee : String) (hc : callee ∈ calls expr) :
    SafeHull (uMembers (pre108 result.items)) [] callee := by
  have h := safeConstantValue_leaf _ leaf (compileTimeSafe_constants result.compileTime hm)
  exact safeConstantName_sound _ _ _ _ ((List.all_eq_true.mp h) callee hc)

/-- Runtime elaboration receives source-derived scopes whose scalar/function origin is proved
    over the original declarations, after eliminating alias normalization from those facts. -/
def Source.scopes {text : String} {options : Profil.Options} (result : Source text options) : Scopes (uMembers (pre108 result.items)) :=
  result.derived.scope

end Gabbro.Stage0.Frontend
