/-
  File:      Grammatik/Parser/Elab/UebersetzeSum.lean
  Subject:   T3 PART 6c: generic lowering of tagged values (`Ty.sum cs`, `tagged type M = { Leer, Kurz(T) }`).
             A value is a variable of type `sum cs` or a case: `Expr.case cs i nutz` with the payload expression
             `NutzlastExpr.val e` (the case has a payload range) or `NutzlastExpr.empty`; the specification `cs`
             is the list of payload ranges of the declaration (`USum.spec`).
-/
module
public import Grammatik.Parser.Elab.UebersetzeAllg2
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The payload expression of the case `i` of the specification `cs`: absent, or a number inside the range. -/
def lowNutz (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (cs : List (Option Ty)) (i : Fin cs.length) (p : Option USide) :
    Except String (NutzlastExpr (declOf u) Γ Λ (cs.get i)) :=
  match hc : cs.get i, p with
  | none, none => .ok NutzlastExpr.empty
  | some τ, some s =>
    match lowWertAtE u Γ Λ fn none τ s with
    | .error e => .error e
    | .ok e => .ok (NutzlastExpr.val e)
  | _, _ => .error "payload of a case without G form"

/-- A tagged value of the declaration at `sidx` (positions of parameters shift by `sh`, see `lowIdx`). -/
def lowSVal (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (sidx : Nat)
    (hs : sidx < u.sums.length) :
    USVal → Except String (Expr (declOf u) Γ Λ (.sum (u.sums.get ⟨sidx, hs⟩).spec))
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.sum m) =>
        if m == sidx then
          match lowVar Γ (sh + j) (.sum (u.sums.get ⟨sidx, hs⟩).spec) with
          | .error e => .error e
          | .ok v => .ok (Expr.var v)
        else .error "tagged value of a foreign type"
      | _ =>
        match lowVar Γ (sh + j) (.sum (u.sums.get ⟨sidx, hs⟩).spec) with
        | .ok v => .ok (Expr.var v)
        | .error e => .error e
  | .fall i pl =>
    if hi : i < (u.sums.get ⟨sidx, hs⟩).spec.length then
      match lowNutz u Γ Λ fn (u.sums.get ⟨sidx, hs⟩).spec ⟨i, hi⟩ pl with
      | .error e => .error e
      | .ok nz => .ok (Expr.case (D := declOf u) _ ⟨i, hi⟩ nz)
    else .error "case outside the tagged type"
  | .slot b f ix =>
    match lowDurchWert u Γ Λ fn sh b f ix with
    | some (.ok w) =>
      if h : w.ty = .sum (u.sums.get ⟨sidx, hs⟩).spec then .ok (h ▸ w.term) else .error "tagged value of a foreign type"
    | some (.error e) => .error e
    | none => .error "tagged value without G form"
  | .tab b f ix =>
    match lowTabWert u Γ Λ fn sh b f ix with
    | some (.ok w) =>
      if h : w.ty = .sum (u.sums.get ⟨sidx, hs⟩).spec then .ok (h ▸ w.term) else .error "tagged value of a foreign type"
    | some (.error e) => .error e
    | none => .error "tagged value without G form"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
