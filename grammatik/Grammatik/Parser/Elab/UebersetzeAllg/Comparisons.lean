module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- Compare already lowered values, preserving all errors and type checks. Boolean equality
    uses the existing conditional and negation, without a scalar encoding or a model extension. -/
def lowVglWert (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} (op : String)
    (a b : Except String (LowWert u Γ Λ)) : Except String (Expr (declOf u) Γ Λ .bool) :=
    match a, b with
    | .ok ⟨.bool, x⟩, .ok ⟨.bool, y⟩ => do
      u.exportGate
      match op with
      | "==" => .ok (Expr.wenn x y (Expr.not y))
      | "!=" => .ok (Expr.not (Expr.wenn x y (Expr.not y)))
      | _ => .error "source export: truth values have no ordering"
    | .ok ⟨.fl _ _, x⟩, .ok ⟨.fl _ _, y⟩ =>
      match op with
      | "<" => .ok (Expr.fllt x y)
      | "<=" => .ok (Expr.flle x y)
      | ">" => .ok (Expr.fllt y x)
      | ">=" => .ok (Expr.flle y x)
      | _ => .error "float: comparison without canonical G form"
    | .ok ⟨.str _, x⟩, .ok ⟨.str _, y⟩ => do
      u.exportGate
      match op with
      | "==" => .ok (Expr.strEq x y)
      | "!=" => .ok (Expr.not (Expr.strEq x y))
      | "<" => .ok (Expr.strLt x y)
      | "<=" => .ok (Expr.or (Expr.strLt x y) (Expr.strEq x y))
      | ">" => .ok (Expr.strLt y x)
      | ">=" => .ok (Expr.or (Expr.strLt y x) (Expr.strEq x y))
      | _ => .error "operator without G form"
    | .ok ⟨.ref region, x⟩, .ok ⟨.ref other, y⟩ => do
      u.exportGate
      if same : other = region then
        match op with
        | "==" => .ok (Expr.refEq x (same ▸ y))
        | "!=" => .ok (Expr.not (Expr.refEq x (same ▸ y)))
        | _ => .error "source export: reference ordering has no canonical G form"
      else .error "source export: reference equality requires the same region"
    | _, _ =>
    match zahlVon a with
    | .error e => .error e
    | .ok s1 =>
      match zahlVon b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

/-- Boolean comparisons keep the actual typed terms and the original export gate. -/
theorem lowVglWert_bool (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (x y : Expr (declOf u) Γ Λ .bool) (gate : u.exportGate = .ok ()) :
    lowVglWert u "==" (.ok ⟨.bool, x⟩) (.ok ⟨.bool, y⟩) =
      .ok (Expr.wenn x y (Expr.not y)) ∧
    lowVglWert u "!=" (.ok ⟨.bool, x⟩) (.ok ⟨.bool, y⟩) =
      .ok (Expr.not (Expr.wenn x y (Expr.not y))) := by
  simp [lowVglWert, gate, bind, Except.bind, pure, Except.pure]

/-- Equality sugar compares truth values; it never turns them into numbers. -/
theorem bool_equality_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (x y : Expr D Γ Λ .bool) (entry state : World D) (env : Env D Γ) :
    wahr? (eval entry (Expr.wenn x y (Expr.not y)) state env) =
      (wahr? (eval entry x state env) == wahr? (eval entry y state env)) := by
  simp only [eval]
  generalize eval entry x state env = a
  generalize eval entry y state env = b
  revert a b
  intro (a : Bool) (b : Bool)
  cases a <;> cases b <;> rfl

end Gabbro.Grammatik.Parser.UebersetzeAllg
