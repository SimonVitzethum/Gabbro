module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The pure arithmetic surface tree retained by a measure. Unlike `SExpr` this has decidable
    equality, preserving the existing decidable equality of `UFn` without a classical instance. -/
inductive UMeasure
  | lit : Nat → UMeasure
  | variable : String → UMeasure
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

/-- This intermediate retains the original source expression exactly, rather than a guessed parameter. -/
theorem uMeasureSource_exact (source : SExpr) (measure : UMeasure)
    (lowered : uMeasureSource source = .ok measure) : measure.source = source := by
  induction source generalizing measure with
  | lit n => cases lowered; rfl
  | variable name => cases lowered; rfl
  | bin op a b iha ihb =>
    cases ha : uMeasureSource a with
    | error error => simp only [uMeasureSource, ha, bind, Except.bind] at lowered; cases lowered
    | ok x =>
      cases hb : uMeasureSource b with
      | error error => simp only [uMeasureSource, ha, hb, bind, Except.bind] at lowered; cases lowered
      | ok y =>
        simp only [uMeasureSource, ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowered
        subst measure
        simp only [UMeasure.source, iha _ ha, ihb _ hb]
  | un op a ih =>
    cases ha : uMeasureSource a with
    | error error => simp only [uMeasureSource, ha, bind, Except.bind] at lowered; cases lowered
    | ok x =>
      simp only [uMeasureSource, ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowered
      subst measure
      simp only [UMeasure.source, ih _ ha]
  | _ => cases lowered

end Gabbro.Grammatik.Parser.Uebersetze
