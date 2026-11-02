module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The pure arithmetic surface tree retained by a measure. Unlike `SExpr` this has decidable
    equality, preserving the existing decidable equality of `UFn` without a classical instance. -/
inductive UMeasure
  | lit : Nat → UMeasure
  | «variable» : String → UMeasure
  | bin : String → UMeasure → UMeasure → UMeasure
  | un : String → UMeasure → UMeasure
  deriving DecidableEq, Repr

def UMeasure.source : UMeasure → SExpr
  | .lit n => .lit n
  | .variable name => .variable name
  | .bin op a b => .bin op a.source b.source
  | .un op a => .un op a.source

/-- Preserve source spelling and operands; storage, old-state and calls have no measure rule. -/
def uMeasureSource : SExpr → Except String UMeasure
  | .lit n => .ok (.lit n)
  | .variable name => .ok (.variable name)
  | .bin op a b => do pure (.bin op (← uMeasureSource a) (← uMeasureSource b))
  | .un op a => do pure (.un op (← uMeasureSource a))
  | .old _ => .error "old-state read in decreases"
  | .call _ _ => .error "unsupported call in decreases"
  | _ => .error "unsupported expression or storage read in decreases"

/-- This intermediate retains the original source expression exactly, rather than a guessed parameter.
    (Structural recursion on the operands: `SExpr` is nested, so `induction` does not apply.) -/
theorem uMeasureSource_exact : ∀ (source : SExpr) (measure : UMeasure),
    uMeasureSource source = .ok measure → measure.source = source
  | .lit n, measure, lowered => by
      simp only [uMeasureSource, Except.ok.injEq] at lowered; subst lowered; rfl
  | .variable name, measure, lowered => by
      simp only [uMeasureSource, Except.ok.injEq] at lowered; subst lowered; rfl
  | .bin op a b, measure, lowered => by
      cases ha : uMeasureSource a with
      | error error => simp only [uMeasureSource, ha, bind, Except.bind] at lowered; cases lowered
      | ok x =>
        cases hb : uMeasureSource b with
        | error error => simp only [uMeasureSource, ha, hb, bind, Except.bind] at lowered; cases lowered
        | ok y =>
          simp only [uMeasureSource, ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowered
          subst measure
          simp only [UMeasure.source, uMeasureSource_exact a x ha, uMeasureSource_exact b y hb]
  | .un op a, measure, lowered => by
      cases ha : uMeasureSource a with
      | error error => simp only [uMeasureSource, ha, bind, Except.bind] at lowered; cases lowered
      | ok x =>
        simp only [uMeasureSource, ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowered
        subst measure
        simp only [UMeasure.source, uMeasureSource_exact a x ha]
  | .float _, _, lowered | .tru, _, lowered | .fls, _, lowered | .field _ _, _, lowered
  | .index _ _, _, lowered | .arrow _ _, _, lowered | .call _ _, _, lowered | .fnref _, _, lowered
  | .built _ _, _, lowered | .old _, _, lowered | .res, _, lowered | .why _ _, _, lowered
  | .ext _ _ _, _, lowered => by simp [uMeasureSource] at lowered

end Gabbro.Grammatik.Parser.Uebersetze
