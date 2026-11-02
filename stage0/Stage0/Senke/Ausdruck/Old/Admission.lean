/- Source admission and the distinct, broader domain of the canonical typed model. -/
module
public import Stage0.Senke.Ausdruck.Old.Source
@[expose] public section

namespace Gabbro.Stage0.OldSource
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- `elabFn` uses `uBool` for requires; `uInv`, `uSperrInvs`, assertions,
    conditions and loop invariants use the same gate. Only ensures use `uSichert`
    without this exclusion. Thus a successful source predicate outside ensures
    contains neither old nor result, including occurrences below binders/builtins.

    This is a SOURCE restriction. Raw `Expr.oldG`/`Expr.oldS` have no clause index,
    and `AkzeptiertX` does not impose this syntactic restriction on `Programm`.
    G evaluates ordinary body expressions and invariant checks as `eval σ e σ ρ`:
    old there reads the current world. Only ensures use a distinct entry world. -/
theorem uBool_no_entry (ctx : UCtx) (source : SExpr) (predicate : UEns)
    (accepted : uBool ctx source = .ok predicate) : ensAltErg predicate = false := by
  unfold uBool at accepted
  cases lowered : uSichert {ctx with res := none, resBool := false} source with
  | error message => simp [lowered] at accepted
  | ok value =>
    simp only [lowered] at accepted
    split at accepted
    · cases accepted
    · next absent =>
      cases accepted
      cases detected : ensAltErg value
      · rfl
      · exact False.elim (absent detected)

/-- The numeric body-side gate enforces the same restriction before typed lowering. -/
theorem lowSideVal_no_entry (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (source : USide) (value : LowSide u Γ Λ)
    (accepted : lowSideVal u Γ Λ fn source = .ok value) : seiteAltErg source = false := by
  unfold lowSideVal at accepted
  split at accepted
  · cases accepted
  · next absent =>
    cases detected : seiteAltErg source
    · rfl
    · exact False.elim (absent detected)

/-- A successful ordinary predicate cannot be an entry-reading comparison. -/
theorem uBool_entry_unreachable (ctx : UCtx) (source : SExpr) (predicate : UEns)
    (accepted : uBool ctx source = .ok predicate) (entry : ensAltErg predicate = true) : False := by
  rw [uBool_no_entry ctx source predicate accepted] at entry
  cases entry

/-- The source gate is inhabited, and detects an old occurrence beneath an integer builtin. -/
theorem uBool_no_entry_zeuge :
    uBool ({names := [], kinds := [], types := [], tabs := [], locks := [], held := [],
      res := none, fname := "", alias := [], lits := []} : UCtx) (.bin "==" (.lit 0) (.lit 0)) = .ok (.cmp "==" (.lit 0) (.lit 0)) ∧
    ensAltErg (.cmp "==" (.ib1 .clz 8 (.old "T" "value" (.lit 0))) (.lit 0)) = true := by
  exact ⟨by decide +kernel, rfl⟩

end Gabbro.Stage0.OldSource
