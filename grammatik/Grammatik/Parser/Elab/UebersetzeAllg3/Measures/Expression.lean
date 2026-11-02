module
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
public import Grammatik.Logik.Terminierung.Mass
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Values
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.ValuesBits
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

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
        .ok { side := ⟨(z, z), Expr.lit z⟩, footprint := rfl, denotes := fun _ _ _ => SourceValue.constant name z hp (by simpa only [hn] using hc) }
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
            .ok { side := ⟨(lo, hi), Expr.var v⟩, footprint := rfl, denotes := fun _ _ _ => SourceValue.parameter name j lo hi v
                    (by simpa only [hn] using ht) hv }
        else .error "entry parameter mismatch in decreases"
      | _ => .error "decreases parameter is not an integer"

mutual
/-- Source arithmetic is lowered compositionally with the existing typed arithmetic operators.
    Unsupported operators and calls are explicit refusals, including calls hidden below arithmetic. -/
def lowerExpression (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) :
    (source : SExpr) → Except String (Expression u Γ Λ fn source)
  | .lit n => .ok { side := ⟨(Int.ofNat n, Int.ofNat n), Expr.lit (Int.ofNat n)⟩, footprint := rfl, denotes := fun _ _ _ => SourceValue.literal n }
  | .variable name => parameter u Γ Λ fn name
  | .bin "+" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    pure { side := x.side.plus y.side, footprint := (by change x.side.term.orte ++ y.side.term.orte = []; rw [x.footprint, y.footprint]; rfl), denotes := fun entry state env => SourceValue.add (x.denotes entry state env) (y.denotes entry state env) }
  | .bin "-" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    pure { side := x.side.minus y.side, footprint := (by change x.side.term.orte ++ y.side.term.orte = []; rw [x.footprint, y.footprint]; rfl), denotes := fun entry state env => SourceValue.sub (x.denotes entry state env) (y.denotes entry state env) }
  | .bin "*" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    pure { side := x.side.times y.side,
           footprint := by change x.side.term.orte ++ y.side.term.orte = []; rw [x.footprint, y.footprint]; rfl,
           denotes := fun entry state env => SourceValue.mul (x.denotes entry state env) (y.denotes entry state env) }
  | .bin "/" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.durch x.side y.side with
    | .ok s => pure { side := s,
        footprint := durch_orte x.footprint y.footprint h,
        denotes := fun entry state env => durch_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .bin "%" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.rest x.side y.side with
    | .ok s => pure { side := s,
        footprint := rest_orte x.footprint y.footprint h,
        denotes := fun entry state env => rest_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .bin "&" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.and x.side y.side with
    | .ok s => pure { side := s,
        footprint := band_orte x.footprint y.footprint h,
        denotes := fun entry state env => band_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .bin "|" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.or x.side y.side with
    | .ok s => pure { side := s,
        footprint := bor_orte x.footprint y.footprint h,
        denotes := fun entry state env => bor_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .bin "^" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.xoder x.side y.side with
    | .ok s => pure { side := s,
        footprint := bxor_orte x.footprint y.footprint h,
        denotes := fun entry state env => bxor_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .bin "<<" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.links x.side y.side with
    | .ok s => pure { side := s,
        footprint := links_orte x.footprint y.footprint h,
        denotes := fun entry state env => links_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .bin ">>" a b => do
    let x ← lowerExpression u Γ Λ fn a
    let y ← lowerExpression u Γ Λ fn b
    match h : LowSide.rechts x.side y.side with
    | .ok s => pure { side := s,
        footprint := rechts_orte x.footprint y.footprint h,
        denotes := fun entry state env => rechts_denotes h a b entry state env
          (x.denotes entry state env) (y.denotes entry state env) }
    | .error e => .error e
  | .un op a => do
    if hs : op = "-" ∨ op = "-()" then
      let x ← lowerExpression u Γ Λ fn a
      pure { side := x.side.minusEins, footprint := x.footprint, denotes := fun entry state env => SourceValue.neg op hs (x.denotes entry state env) }
    else throw "unsupported unary operator in decreases"
  | .old _ => .error "old-state read in decreases"
  | .call f args => lowerConvCall u Γ Λ fn f args
  | _ => .error "unsupported expression or storage read in decreases"
/-- A conversion `T(e)`: the head must name a type of the declaration's entry alias scope,
    and the operand must fit its range; anything else stays a refused call. -/
def lowerConvCall (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (f : String) :
    (args : List SExpr) → Except String (Expression u Γ Λ fn (.call f args))
  | [a] => do
    let x ← lowerExpression u Γ Λ fn a
    match uTypName fn.measureTypes f with
    | .ok (lo, hi) =>
      match h : LowSide.conv lo hi x.side with
      | .ok s => pure { side := s,
          footprint := conv_orte x.footprint h,
          denotes := fun entry state env => conv_denotes h a f entry state env
            (x.denotes entry state env) }
      | .error e => .error e
    | .error _ => .error "unsupported call in decreases"
  | _ => .error "unsupported call in decreases"
end

/-- Successful lowering preserves the written source expression in every world and entry environment. -/
theorem lowerExpression_denotes (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (source : SExpr) (term : Expression u Γ Λ fn source)
    (_lowered : lowerExpression u Γ Λ fn source = .ok term)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) :
    SourceValue fn fn.measureConstants env source (eval entry term.side.term state env).n :=
  term.denotes entry state env

end Gabbro.Grammatik.Parser.Measures
