module
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
public import Grammatik.Logik.Terminierung.Mass
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- Source arithmetic denotation over the entry environment. There is no storage, old-state,
    result or call rule. Name resolution is witnessed at the original parameter position. -/
inductive SourceValue {u : UProg} {Γ : Ctx} (fn : UFn)
    (constants : List (String × Int)) (env : Env (declOf u) Γ) : SExpr → Int → Prop
  | literal (n : Nat) : SourceValue fn constants env (.lit n) (Int.ofNat n)
  | parameter (name : String) (j : Nat) (lo hi : Int) (v : Var Γ (.int lo hi))
      (found : fn.params[j]? = some (name, .int lo hi))
      (position : lowVar Γ j (.int lo hi) = .ok v) :
      SourceValue fn constants env (.variable name) (env.get v).n
  | constant (name : String) (z : Int)
      (unbound : fn.params.findIdx? (fun p => p.1 == name) = none)
      (found : constants.filter (fun p => p.1 == name) = [(name, z)]) :
      SourceValue fn constants env (.variable name) z
  | add {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "+" a b) (x + y)
  | sub {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "-" a b) (x - y)
  | mul {a b : SExpr} {x y : Int} : SourceValue fn constants env a x →
      SourceValue fn constants env b y → SourceValue fn constants env (.bin "*" a b) (x * y)
  | neg {a : SExpr} {x : Int} (op : String) (spelling : op = "-" ∨ op = "-()") :
      SourceValue fn constants env a x → SourceValue fn constants env (.un op a) (-x)

/-- A typed term together with its independent source denotation and empty footprint. -/
structure Expression (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (source : SExpr) where
  side : LowSide u Γ Λ
  footprint : side.term.orte = []
  denotes : ∀ (entry state : World (declOf u)) (env : Env (declOf u) Γ),
    SourceValue fn fn.measureConstants env source (eval entry side.term state env).n

/-- Checked parameter resolution never silently selects between duplicate entry names. -/
def parameter (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (name : String) :
    Except String (Expression u Γ Λ fn (.variable name)) :=
  match hp : fn.params.findIdx? (fun p => p.1 == name) with
  | none =>
    match hc : fn.measureConstants.filter (fun p => p.1 == name) with
    | [(n, z)] =>
      if hn : n = name then
        .ok { side := ⟨(z, z), Expr.lit z⟩, footprint := rfl,
              denotes := fun _ _ _ => SourceValue.constant name z hp (by simpa only [hn] using hc) }
      else .error "ambiguous constant in decreases"
    | _ => .error "unknown or ambiguous entry name in decreases"
  | some j =>
    if (fn.params.filter (fun p => p.1 == name)).length != 1 then
      .error "ambiguous entry parameter in decreases"
    else
      match ht : fn.params[j]? with
      | some (n, .int lo hi) =>
        if hn : n = name then
          match hv : lowVar Γ j (.int lo hi) with
          | .error error => .error error
          | .ok v =>
            .ok { side := ⟨(lo, hi), Expr.var v⟩, footprint := rfl,
                  denotes := fun _ _ _ => SourceValue.parameter name j lo hi v
                    (by simpa only [hn] using ht) hv }
        else .error "entry parameter mismatch in decreases"
      | _ => .error "decreases parameter is not an integer"

/-- Source arithmetic is lowered compositionally with the existing typed arithmetic operators.
    Unsupported operators and calls are explicit refusals, including calls hidden below arithmetic. -/
def lowerExpression (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) :
    (source : SExpr) → Except String (Expression u Γ Λ fn source)
  | .lit n => .ok { side := ⟨(Int.ofNat n, Int.ofNat n), Expr.lit (Int.ofNat n)⟩,
      footprint := rfl, denotes := fun _ _ _ => SourceValue.literal n }
  | .variable name => parameter u Γ Λ fn name
  | .bin "+" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    pure { side := x.side.plus y.side,
           footprint := by change x.side.term.orte ++ y.side.term.orte = []; rw [x.footprint, y.footprint]; rfl,
           denotes := fun entry state env => SourceValue.add (x.denotes entry state env) (y.denotes entry state env) }
  | .bin "-" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    pure { side := x.side.minus y.side,
           footprint := by change x.side.term.orte ++ y.side.term.orte = []; rw [x.footprint, y.footprint]; rfl,
           denotes := fun entry state env => SourceValue.sub (x.denotes entry state env) (y.denotes entry state env) }
  | .bin "*" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    pure { side := x.side.times y.side,
           footprint := by change x.side.term.orte ++ y.side.term.orte = []; rw [x.footprint, y.footprint]; rfl,
           denotes := fun entry state env => SourceValue.mul (x.denotes entry state env) (y.denotes entry state env) }
  | .un op a => do
    if hs : op = "-" ∨ op = "-()" then
      let x ← lowerExpression u Γ Λ fn a
      pure { side := x.side.minusEins,
             footprint := x.footprint,
             denotes := fun entry state env => SourceValue.neg op hs (x.denotes entry state env) }
    else throw "unsupported unary operator in decreases"
  | .old _ => .error "old-state read in decreases"
  | .call _ _ => .error "unsupported call in decreases"
  | _ => .error "unsupported expression or storage read in decreases"

/-- Successful lowering preserves the written source expression in every world and entry environment. -/
theorem lowerExpression_denotes (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (source : SExpr) (term : Expression u Γ Λ fn source)
    (_lowered : lowerExpression u Γ Λ fn source = .ok term)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) :
    SourceValue fn fn.measureConstants env source (eval entry term.side.term state env).n :=
  term.denotes entry state env

end Gabbro.Grammatik.Parser.Measures
