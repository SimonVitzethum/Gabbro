/-
  File:      Grammatik/Parser/Elab/UebersetzeOpt.lean
  Subject:   T3 PART 6b: generic lowering of option values (`Ty.opt n`, `option index into T`). An option value
             is `None` (`Expr.none`), `Some(i)` (`Expr.some` of an index expression of the table), an option
             variable (a parameter or a `let`) or the read of an option field through a pointer (`Expr.thru`) or
             at a table (`Expr.slot`). The field's type is `typAt u t f = .opt n` with `n` the count of the table
             the option indexes (`OptHit`); the term is cast along that fact, as the integer reads are
             (`durchTerm`, `slotTerm`).
-/
import Grammatik.Parser.Elab.UebersetzeAllg

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-- An option field read through a pointer parameter, at its type `opt n`. -/
def durchTermO (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (num : Nat) (h : num < u.tabs.length)
    (oh : OptHit u ⟨num, h⟩) {w : Bool} (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.opt oh.n) := by
  rw [← oh.hopt]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) oh.idx i hL

/-- An option field read at a table, at its type `opt n`. -/
def slotTermO (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (t : Fin u.tabs.length) (oh : OptHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.opt oh.n) := by
  rw [← oh.hopt]
  exact Expr.slot (D := declOf u) t oh.idx i hL

/-- An option value over the table `num` (positions of parameters shift by `sh`, see `lowIdx`). -/
def lowOpt (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (num : Nat) (hnum : num < u.tabs.length) :
    UOpt → Except String (Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hnum⟩)))
  | .nichts => .ok (Expr.none (D := declOf u) _)
  | .etwas ix =>
    match lowIdx u Γ Λ fn sh ⟨num, hnum⟩ ix with
    | .error e => .error e
    | .ok i => .ok (Expr.some (D := declOf u) i)
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.opt m) =>
        if m == num then
          match lowVar Γ (sh + j) (.opt ((declOf u).count ⟨num, hnum⟩)) with
          | .error e => .error e
          | .ok v => .ok (Expr.var v)
        else .error "option of a foreign table"
      | _ => .error "option without G form"
  | .slot b f ix =>
    match paramPos fn.params b with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.ptr pnum w) =>
        if h : pnum < u.tabs.length then
          match fieldHitO u ⟨pnum, h⟩ f with
          | .error e => .error e
          | .ok oh =>
            if hn : oh.n = (declOf u).count ⟨num, hnum⟩ then
              match lowVar Γ (sh + j) (.ptr pnum w) with
              | .error e => .error e
              | .ok pv =>
                match lowIdx u Γ Λ fn sh ⟨pnum, h⟩ ix with
                | .error e => .error e
                | .ok i =>
                  if hL : (∀ wdd ∈ (declOf u).braucht ⟨pnum, h⟩, Res.von (declOf u) wdd ∈ Λ) then
                    .ok (by rw [← hn]; exact durchTermO u Γ Λ pnum h oh pv i hL)
                  else .error "access without held guard"
            else .error "option of a foreign table"
        else .error "pointer table unknown"
      | _ => .error "place without G form"
  | .tab b f ix =>
    match tabIdx u.tabs b with
    | .error e => .error e
    | .ok t =>
      match fieldHitO u t f with
      | .error e => .error e
      | .ok oh =>
        if hn : oh.n = (declOf u).count ⟨num, hnum⟩ then
          match lowIdx u Γ Λ fn sh t ix with
          | .error e => .error e
          | .ok i =>
            if hL : (∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) then
              .ok (by rw [← hn]; exact slotTermO u Γ Λ t oh i hL)
            else .error "access without held guard"
        else .error "option of a foreign table"

end Gabbro.Grammatik.Parser.UebersetzeAllg
