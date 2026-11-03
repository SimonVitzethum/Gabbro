module
public import Grammatik.Parser.Item.ElementTief.Kopf.Teil2
public import Grammatik.Parser.Elab.Uebersetze.Eingebaut
public import Grammatik.Parser.Namen.References
@[expose] public section
namespace Gabbro.Grammatik.Parser.Instantiation

/-- One structural traversal supplies both independent postconditions. -/
structure SurfaceFacts where
  ordinary : Bool := true
  references : List String := []
  deriving Repr

def merge (a b : SurfaceFacts) : SurfaceFacts :=
  ⟨a.ordinary && b.ordinary, a.references ++ b.references⟩

def gather (facts : List SurfaceFacts) : SurfaceFacts := facts.foldr merge {}

def optional {α : Type} (inspect : α → SurfaceFacts) (value : Option α) : SurfaceFacts :=
  gather (value.toList.map inspect)

/-- Generated targets must never be hidden by a surface binder or builtin spelling. -/
def generatedName (name : String) : Bool :=
  "$generic$".toList.isPrefixOf name.toList || "$literal$".toList.isPrefixOf name.toList ||
    "__gabbro_module_".toList.isPrefixOf name.toList ||
    "$spec$".toList.isPrefixOf name.toList || "#tagged-".toList.isPrefixOf name.toList

/-- These are surface builtin/conversion heads, not direct global function references.
    Nominal constructors are supplied from the unit's type declarations. The ordinary checker
    still checks their arity, operand types, contracts and legality. -/
def builtinName (name : String) : Bool :=
  ["Held", "Some", "None"].contains name || istIntWort name || istZuckerBreite name ||
    (Uebersetze.uBitEin name).isSome || (Uebersetze.uRotEin name).isSome

structure Scope where
  constructors : List String := []
  /-- `&Table` uses the same fnref surface constructor as `&function`. -/
  carriers : List String := []
  locals : List String := []

/-- Local function-pointer calls and builtin/constructor applications keep their existing rules.
    Every other named call or function address is a direct global reference, including unknown
    names (they are not filtered out by a declaration lookup). -/
def reference (scope : Scope) (name : String) : SurfaceFacts :=
  if !generatedName name && (scope.locals.contains name || builtinName name ||
      scope.constructors.contains name) then {}
  else ⟨true, [name]⟩

def Scope.bind (scope : Scope) (names : List String) : Scope :=
  { scope with locals := names ++ scope.locals }

/-- These positions are unambiguously global function names, not overloaded call heads. -/
def globalReference (name : String) : SurfaceFacts := ⟨true, [name]⟩

mutual
def expression (scope : Scope) : SExpr → SurfaceFacts
  | .lit _ | .float _ | .tru | .fls | .variable _ | .res | .why _ _ => {}
  | .field e _ | .arrow e _ | .un _ e | .old e => expression scope e
  | .index a b | .bin _ a b => merge (expression scope a) (expression scope b)
  | .call name args => merge (reference scope name) (expressions scope args)
  | .fnref name => if scope.carriers.contains name then {} else globalReference name
  | .built _ args => expressions scope args
  | .ext .instantiate _ args | .ext .dyn _ args => merge ⟨false, []⟩ (expressions scope args)
  | .ext .all (binder :: _ :: _) args | .ext .any (binder :: _ :: _) args |
    .ext .count (binder :: _ :: _) args => quantified scope binder args
  | .ext _ _ args => expressions scope args

def expressions (scope : Scope) : List SExpr → SurfaceFacts
  | [] => {}
  | e :: rest => merge (expression scope e) (expressions scope rest)

def quantified (scope : Scope) (binder : String) : List SExpr → SurfaceFacts
  | [] => {}
  | [body] => expression (scope.bind [binder]) body
  | e :: rest => merge (expression scope e) (quantified scope binder rest)
end

/-- Raw type/header strings are opaque fields of the existing surface AST, not new AST forms.
    Function literals are represented only inside explicit generic argument spellings; rejecting
    their enclosing application constructors removes them, including unused applications. -/
def inspectType (scope : Scope) : STyp → SurfaceFacts
  | .atom _ | .path _ | .index _ _ | .raw _ => {}
  | .ptr _ _ ty | .wrap ty => inspectType scope ty
  | .range ty lo hi _ => gather [inspectType scope ty, expression scope lo, expression scope hi]
  | .array ty n => merge (inspectType scope ty) (expression scope n)
  | .embed ty _ scale => merge (inspectType scope ty) (optional (expression scope) scale)
  | .str n => expression scope n
  | .entry _ result => optional (inspectType scope) result
  | .dyn _ _ => ⟨false, []⟩

def effect (scope : Scope) : SEffekt → SurfaceFacts
  | .reads e | .writes e | .locks _ e | .takes e | .posts e => expression scope e
  | .masks _ | .allocs _ | .borrows _ | .moves _ | .mints _ | .loops | .pure => {}
  | .param _ => ⟨false, []⟩
  | .instanceEffects _ types => merge ⟨false, []⟩ (gather (types.map (inspectType scope)))

def clause (scope : Scope) : SKlausel → SurfaceFacts
  | .needs e | .gives e | .cost e | .drops e => expression scope e
  | .effs effects => gather (effects.map (effect scope))
  | .keeps _ | .refs _ | .induc _ | .load _ | .part _ | .arch _ | .moves _ _ |
    .quits _ | .limit _ => {}

def signature (scope : Scope) (sig : FnSig) : SurfaceFacts :=
  let scope := scope.bind (sig.params.map Prod.fst)
  gather [⟨sig.generics.isEmpty, []⟩, gather (sig.params.map (fun p => inspectType scope p.2)),
    optional (inspectType scope) sig.res, gather (sig.klauseln.map (clause scope))]

mutual
def constant (scope : Scope) : SKonstWert → SurfaceFacts
  | .one e => expression scope e
  | .rows rows => constants scope rows
def constants (scope : Scope) : List SKonstWert → SurfaceFacts
  | [] => {}
  | value :: rest => merge (constant scope value) (constants scope rest)
end

def field (scope : Scope) (f : SFeld) : SurfaceFacts :=
  merge (inspectType scope f.ftyp) (optional (expression scope) f.wo)

def invariant (scope : Scope) (i : SGruppenInv) : SurfaceFacts :=
  merge (expression scope i.kosten) (expression scope i.pred)

def transition (scope : Scope) (t : STrans) : SurfaceFacts :=
  gather [gather (t.schritte.map fun (a, b, c) =>
      gather [expression scope a, expression scope b, expression scope c]),
    optional (expression scope) t.voraus, gather (t.wirkung.map (effect scope))]

end Gabbro.Grammatik.Parser.Instantiation
