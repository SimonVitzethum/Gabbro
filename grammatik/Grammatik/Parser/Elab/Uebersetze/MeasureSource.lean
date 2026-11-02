module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section

set_option maxRecDepth 100000

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The pure arithmetic surface tree retained by a measure. Unlike `SExpr` this has decidable
    equality, preserving the existing decidable equality of `UFn` without a classical instance.
    `conv` is an integer conversion `T(e)`: the name travels, the target range is resolved
    against the unit aliases at collection (`uMeasureClause`) and at lowering
    (`lowerExpression` reads `fn.measureTypes`). -/
inductive UMeasure
  | lit : Nat → UMeasure
  | variable : String → UMeasure
  | bin : String → UMeasure → UMeasure → UMeasure
  | un : String → UMeasure → UMeasure
  | conv : String → UMeasure → UMeasure
  deriving DecidableEq, Repr

def UMeasure.source : UMeasure → SExpr
  | .lit n => .lit n
  | .variable name => .variable name
  | .bin op a b => .bin op a.source b.source
  | .un op a => .un op a.source
  | .conv f a => .call f [a.source]

mutual
/-- Preserve source spelling and operands; storage, old-state and calls have no measure rule.
    A single-argument call travels opaquely as a conversion; whether its head names a type
    is decided against the unit aliases in `uMeasureClause`, never guessed here. -/
def uMeasureSource : SExpr → Except String UMeasure
  | .lit n => .ok (.lit n)
  | .variable name => .ok (.variable name)
  | .bin op a b => do pure (.bin op (← uMeasureSource a) (← uMeasureSource b))
  | .un op a => do pure (.un op (← uMeasureSource a))
  | .call f args => uMeasureCall f args
  | .old _ => .error "old-state read in decreases"
  | _ => .error "unsupported expression or storage read in decreases"
/-- A call in a measure is an integer conversion with exactly one argument; anything else,
    including a bare name applied to several arguments, is a call and stays refused. -/
def uMeasureCall : String → List SExpr → Except String UMeasure
  | f, [a] => (uMeasureSource a).map (.conv f ·)
  | _, _ => .error "unsupported call in decreases"
end

mutual
/-- This intermediate retains the original source expression exactly, rather than a guessed parameter. -/
theorem uMeasureSource_exact (source : SExpr) (measure : UMeasure)
    (lowered : uMeasureSource source = .ok measure) : measure.source = source := by
  cases source with
  | lit n => cases lowered; rfl
  | float _ => cases lowered
  | tru => cases lowered
  | fls => cases lowered
  | variable name => cases lowered; rfl
  | field _ _ => cases lowered
  | index _ _ => cases lowered
  | arrow _ _ => cases lowered
  | un op a =>
    cases ha : uMeasureSource a with
    | error error => simp only [uMeasureSource, ha, bind, Except.bind] at lowered; cases lowered
    | ok x =>
      simp only [uMeasureSource, ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowered
      subst measure
      simp only [UMeasure.source, uMeasureSource_exact a x ha]
  | bin op a b =>
    cases ha : uMeasureSource a with
    | error error => simp only [uMeasureSource, ha, bind, Except.bind] at lowered; cases lowered
    | ok x =>
      cases hb : uMeasureSource b with
      | error error => simp only [uMeasureSource, ha, hb, bind, Except.bind] at lowered; cases lowered
      | ok y =>
        simp only [uMeasureSource, ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at lowered
        subst measure
        simp only [UMeasure.source, uMeasureSource_exact a x ha, uMeasureSource_exact b y hb]
  | call f args =>
    simp only [uMeasureSource] at lowered
    exact uMeasureCall_exact f args measure lowered
  | fnref _ => cases lowered
  | built _ _ => cases lowered
  | old _ => cases lowered
  | res => cases lowered
  | why _ _ => cases lowered
  | ext _ _ _ => cases lowered
/-- A collected call round-trips exactly: the conversion spelling is the original call. -/
theorem uMeasureCall_exact (f : String) (args : List SExpr) (measure : UMeasure)
    (lowered : uMeasureCall f args = .ok measure) : measure.source = .call f args := by
  cases args with
  | nil => cases lowered
  | cons a rest =>
    cases rest with
    | cons _ _ => cases lowered
    | nil =>
      cases ha : uMeasureSource a with
      | error error => simp only [uMeasureCall, ha] at lowered; cases lowered
      | ok x =>
        have hconv : uMeasureCall f [a] = .ok (.conv f x) := by simp only [uMeasureCall, ha]
        rw [hconv, Except.ok.injEq] at lowered
        subst measure
        simp only [UMeasure.source, uMeasureSource_exact a x ha]
end

end Gabbro.Grammatik.Parser.Uebersetze
