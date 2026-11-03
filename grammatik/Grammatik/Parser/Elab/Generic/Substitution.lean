module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
public import Grammatik.Parser.Elab.Konst.Ersetzung
@[expose] public section
namespace Gabbro.Grammatik.Parser.Generic

/-- Simultaneous surface substitution; replacements are not substituted again. -/
def expression (values : List (String × SExpr)) : SExpr → SExpr
  | .variable n => match values.find? (fun p => strEq p.1 n) with
    | some p => p.2
    | none => .variable n
  | .field e n => .field (expression values e) n
  | .index e i => .index (expression values e) (expression values i)
  | .arrow e n => .arrow (expression values e) n
  | .un op e => .un op (expression values e)
  | .bin op a b => .bin op (expression values a) (expression values b)
  | .call n args => .call n (args.map (expression values))
  | .built n args => .built n (args.map (expression values))
  | .old e => .old (expression values e)
  | .ext k ns args => .ext k ns (args.map (expression values))
  | e => e

/-- Substitute both kinds of parameters in structured surface types. -/
def surfaceType (types : List (String × STyp)) (values : List (String × SExpr)) :
    STyp → STyp
  | .atom n => match types.find? (fun p => strEq p.1 n) with
    | some p => p.2
    | none => .atom n
  | .ptr s r t => .ptr s r (surfaceType types values t)
  | .range t lo hi ex => .range (surfaceType types values t)
      (expression values lo) (expression values hi) ex
  | .array t n => .array (surfaceType types values t) (expression values n)
  | .wrap t => .wrap (surfaceType types values t)
  | .embed t bits scale => .embed (surfaceType types values t) bits
      (scale.map (expression values))
  | .str n => .str (expression values n)
  | .entry args result => .entry args (result.map (surfaceType types values))
  | t => t

/-- Generic arguments use the same certified call substitution as ordinary source
    values before bounded integer evaluation. Expansion cannot erase an unchecked call. -/
def constantArgument (lo hi : Int) (fns : List Uebersetze.UKonstFn)
    (env : List (String × Int)) (arg : SExpr) : Except String Int := do
  let functions := fns.map (fun fn => { fn with constants := env ++ fn.constants })
  let replaced ← Konst.ersetzeSExpr functions arg
  match Uebersetze.uKonstWert lo hi [] env 64 replaced with
  | some n => .ok n
  | none => .error "generic constant argument: C17 evaluation failed or exceeded its bound"

example : beqSTyp
    (surfaceType [("T", .atom "u32")] [("N", .lit 8)]
      (.array (.atom "T") (.variable "N")))
    (.array (.atom "u32") (.lit 8)) = true := rfl

example : constantArgument 0 100 [] [] (.bin "+" (.lit 3) (.lit 5)) = .ok 8 := rfl

end Gabbro.Grammatik.Parser.Generic
