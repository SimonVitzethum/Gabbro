module

public import Grammatik.Parser.Elab.Uebersetze.Akku.Expand
import all Grammatik.Parser.Elab.Uebersetze.Akku.Expand
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Kontext.ZeigerTexte
import all Grammatik.Parser.Elab.Uebersetze.Einheit.ReturnCalls
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.SondeCode
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle

public section
namespace Gabbro.Grammatik.Parser.Uebersetze

-- Unfold one equation of the actual mutual reader at a time. In particular,
-- each equation first matches the actual fuel instead of forcing a large
-- numeral to unify with a successor pattern. All callbacks remain canonical.
private theorem row_nil (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) :
    uAnwReihe tabs heads fuel ctx [] = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => .ok ([], ctx) := by
  cases fuel with
  | zero => simp only [uAnwReihe]
  | succ fuel =>
    simp only [uAnwReihe]

private theorem row_cons (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (statement : SAnw) (rest : List SAnw) :
    uAnwReihe tabs heads fuel ctx (statement :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => (do
        let (before, ctx, statement) ← expandFoldStmt ctx statement
        let (code, ctx) ← uAnwReiheCore tabs heads (fuel + 1) ctx (statement :: rest)
        pure (before ++ code, ctx)) := by
  cases fuel with
  | zero => simp only [uAnwReihe]
  | succ fuel =>
    simp only [uAnwReihe]

private theorem core_bind (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (mutable : Bool) (name : String)
    (ty : Option STyp) (value : SExpr) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.bind mutable name ty value :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => (do
        let (statement, next) ← uBindWert ctx tabs heads mutable name ty value
        let (code, ending) ← uAnwReihe tabs heads fuel
          (foldBindingContext ctx next statement) rest
        pure (statement :: code, ending)) := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    simp only [uAnwReiheCore]
    cases uBindWert ctx tabs heads mutable name ty value with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨statement, next⟩
      dsimp only [bind, Except.bind]
      cases uAnwReihe tabs heads fuel (foldBindingContext ctx next statement) rest <;> rfl

private theorem core_trim (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (name range : String) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.trimReq (.variable name) range :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => (do
        let (lo, hi, next) ← uNarrowKopf ctx name range
        let (code, ending) ← uAnwReihe tabs heads fuel next rest
        pure ([UStmt.narrowReqBeg name lo hi] ++ code, ending)) := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    simp only [uAnwReiheCore]
    cases uNarrowKopf ctx name range with
    | error _ => rfl
    | ok triple =>
      rcases triple with ⟨lo, hi, next⟩
      dsimp only [bind, Except.bind]
      cases uAnwReihe tabs heads fuel next rest <;> rfl

private theorem core_locks (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (name : String) (body rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx
      (.locks false (.variable name) (.block body none) :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => (match ctx.locks.find? (fun lock => strEq lock.name name) with
        | none => .error ("lock unknown: " ++ name)
        | some _ => do
          let (code, _) ← uAnwReihe tabs heads fuel { ctx with held := name :: ctx.held } body
          let (tail, ending) ← uAnwReihe tabs heads fuel ctx rest
          pure ([UStmt.lockBeg name] ++ code ++ [UStmt.blkEnd] ++ tail, ending)) := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    simp only [uAnwReiheCore, Bool.false_eq_true, ite_false]
    cases ctx.locks.find? (fun lock => strEq lock.name name) with
    | none => rfl
    | some _ =>
      cases uAnwReihe tabs heads fuel { ctx with held := name :: ctx.held } body with
      | error _ => rfl
      | ok pair =>
        rcases pair with ⟨code, next⟩
        simp only [uFoldEndeStmt, expandFoldEnd, uEndeStmt, bind, Except.bind,
          pure, Except.pure, List.append_nil]
        cases uAnwReihe tabs heads fuel ctx rest <;> rfl

private theorem core_call (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (name : String) (args : List SExpr) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.call name args :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => (do
        let statement ← uAnw1 ctx tabs heads (.call name args)
        let (code, ending) ← uAnwReihe tabs heads fuel ctx rest
        pure (statement :: code, ending)) := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    simp only [uAnwReiheCore]
    cases uAnw1 ctx tabs heads (.call name args) with
    | error _ => rfl
    | ok statement => cases uAnwReihe tabs heads fuel ctx rest <;> rfl

private theorem core_set (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (target value : SExpr) (op : String) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.set target op value :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => (do
        let statement ← uAnw1 ctx tabs heads (.set target op value)
        let (code, ending) ← uAnwReihe tabs heads fuel ctx rest
        pure (statement :: code, ending)) := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    simp only [uAnwReiheCore]
    cases uAnw1 ctx tabs heads (.set target op value) with
    | error _ => rfl
    | ok statement => cases uAnwReihe tabs heads fuel ctx rest <;> rfl

-- Select the actual conditional's predecessor only after inspecting its fuel;
-- its recursive callback remains the same production reader.
private theorem core_cond (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (condition : SExpr) (body : List SAnw)
    (ending : Option SEnde) (alternatives : List SAnw)
    (fallback : Option SAnw) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx
      (.cond condition (.block body ending) alternatives fallback :: rest) = match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => uCond (uAnwReihe tabs heads fuel)
          ctx condition body ending alternatives fallback rest := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    exact uAnwReiheCore_cond tabs heads fuel ctx condition body ending alternatives fallback rest

-- The mandatory shadowing gate inspects user bodies through this same bounded
-- collector. Keep its list callbacks at the original, unevaluated fuel too.
private theorem bound_names_select (fuel : Nat) (statement : SAnw) :
    uAkkuBinder fuel statement = match fuel with
      | 0 => []
      | fuel + 1 => match statement with
        | .bind _ name _ _ => [name]
        | .bindElse name _ _ reason body => name :: reason :: uAkkuBinder fuel body
        | .bindLib _ name _ _ | .bindQ _ name _ _ => [name]
        | .alloc _ name _ _ _ continuation =>
          name :: (match continuation with | none => [] | some body => uAkkuBinder fuel body)
        | .allocVon _ name _ _ | .await name _ _ _ | .swap name _ _ _ => [name]
        | .arm _ name body => (match name with | none => [] | some name => [name]) ++
            uAkkuBinder fuel body
        | .each name _ _ _ _ _ _ body => name :: uAkkuBinder fuel body
        | .bindAxiomOpt name _ _ => [name]
        | .callIndElse _ _ reason body | .callElse _ _ reason body =>
          reason :: uAkkuBinder fuel body
        | .bindAxiomOptElse name _ _ reason body => name :: reason :: uAkkuBinder fuel body
        | .cond _ yes alternatives no =>
          uAkkuBinder fuel yes ++ alternatives.flatMap (uAkkuBinder fuel) ++
            (match no with | none => [] | some body => uAkkuBinder fuel body)
        | .elsif _ body => uAkkuBinder fuel body
        | .cases _ arms => arms.flatMap (uAkkuBinder fuel)
        | .boundedLoop raw body => (boundedLoopLocals raw).map Prod.fst ++ uAkkuBinder fuel body
        | .retry _ body | .loop _ body | .trim _ _ body | .locks _ _ body |
          .watch _ body | .waive _ body | .grow _ _ body | .child body => uAkkuBinder fuel body
        | .block statements _ => statements.flatMap (uAkkuBinder fuel)
        | _ => [] := by
  cases fuel <;> cases statement <;> rfl

-- The unit collects these source descriptors before and after elaborating its
-- functions. Select their real fuel before forming a recursive list callback.
private theorem pointer_source_select (fuel : Nat) (statement : SAnw) :
    uZeigerAnw fuel statement = match fuel with
      | 0 => []
      | fuel + 1 => match statement with
        | .bind _ _ (some ty) _ => uZeigerTexte [ty]
        | .bindElse _ (some ty) _ _ body => uZeigerTexte [ty] ++ uZeigerAnw fuel body
        | .callIndElse _ _ _ body | .callElse _ _ _ body => uZeigerAnw fuel body
        | .bindElse _ none _ _ body => uZeigerAnw fuel body
        | .bindQ _ _ (some ty) _ | .bindAxiomOpt _ (some ty) _ => uZeigerTexte [ty]
        | .bindAxiomOptElse _ ty _ _ body => uZeigerTexte ty.toList ++ uZeigerAnw fuel body
        | .await _ ty _ _ | .swap _ ty _ _ | .allocVon _ _ ty _ => uZeigerTexte ty.toList
        | .cond _ yes alternatives no =>
          uZeigerAnw fuel yes ++ alternatives.flatMap (uZeigerAnw fuel) ++
            (match no with | some body => uZeigerAnw fuel body | none => [])
        | .elsif _ body => uZeigerAnw fuel body
        | .cases _ arms => arms.flatMap (uZeigerAnw fuel)
        | .arm _ _ body | .each _ _ _ _ _ _ _ body | .boundedLoop _ body | .retry _ body | .loop _ body |
          .waive _ body | .trim _ _ body | .locks _ _ body | .watch _ body => uZeigerAnw fuel body
        | .alloc _ _ ty _ _ body => uZeigerTexte ty.toList ++
            (body.map (uZeigerAnw fuel)).getD []
        | .grow _ _ body | .child body => uZeigerAnw fuel body
        | .block statements _ => statements.flatMap (uZeigerAnw fuel)
        | _ => [] := by
  cases fuel <;> rfl

private theorem start_source_select (fuel : Nat) (statement : SAnw) :
    uStartNamen fuel statement = match fuel with
      | 0 => []
      | fuel + 1 => match statement with
        | .start names => names
        | .block statements _ => statements.flatMap (uStartNamen fuel)
        | .cond _ yes alternatives no =>
          uStartNamen fuel yes ++ alternatives.flatMap (uStartNamen fuel) ++
            (no.map (uStartNamen fuel)).getD []
        | .elsif _ body | .each _ _ _ _ _ _ _ body | .boundedLoop _ body | .retry _ body | .loop _ body |
          .locks _ _ body | .trim _ _ body => uStartNamen fuel body
        | .cases _ arms => arms.flatMap (uStartNamen fuel)
        | .arm _ _ body => uStartNamen fuel body
        | _ => [] := by
  cases fuel <;> cases statement <;> rfl

-- These are the actual clause shapes of the two uses and three generated
-- functions. They introduce neither preconditions nor postconditions, even
-- when the surrounding context carries specification functions.
private theorem clauses_nil (ctx : UCtx) : elabKlauseln ctx [] = .ok ([], []) := by
  cases empty : ctx.specs.isEmpty <;>
    simp only [elabKlauseln, empty, Bool.false_eq_true, ite_false, ite_true, uSpecKlauseln] <;> rfl

private theorem clauses_effect (ctx : UCtx) (effects : List SEffekt) :
    elabKlauseln ctx [.effs effects] = .ok ([], []) := by
  cases empty : ctx.specs.isEmpty <;>
    simp only [elabKlauseln, empty, Bool.false_eq_true, ite_false, ite_true, uSpecKlauseln] <;> rfl

private theorem clauses_cost (ctx : UCtx) (cost : SExpr) :
    elabKlauseln ctx [.cost cost] = .ok ([], []) := by
  cases empty : ctx.specs.isEmpty <;>
    simp only [elabKlauseln, empty, Bool.false_eq_true, ite_false, ite_true, uSpecKlauseln] <;> rfl

private theorem clauses_effect_cost (ctx : UCtx) (effects : List SEffekt) (cost : SExpr) :
    elabKlauseln ctx [.effs effects, .cost cost] = .ok ([], []) := by
  cases empty : ctx.specs.isEmpty <;>
    simp only [elabKlauseln, empty, Bool.false_eq_true, ite_false, ite_true, uSpecKlauseln] <;> rfl

-- These source endings contain no call or fold. The ordinary uEnde invocation
-- in elabFn still checks their actual result types and keeps every refusal.
private theorem return_none (ctx : UCtx) (heads : List UFnKopf) :
    expandReturnCall ctx heads none = .ok ([], ctx, none) := by
  unfold expandReturnCall
  cases uEnde ctx none <;> rfl

private theorem return_empty (ctx : UCtx) (heads : List UFnKopf) :
    expandReturnCall ctx heads (some (.ret none)) = .ok ([], ctx, some (.ret none)) := by
  unfold expandReturnCall
  cases uEnde ctx (some (.ret none)) <;> rfl

private theorem return_variable (ctx : UCtx) (heads : List UFnKopf) (name : String) :
    expandReturnCall ctx heads (some (.ret (some (.variable name)))) =
      .ok ([], ctx, some (.ret (some (.variable name)))) := by
  unfold expandReturnCall
  cases uEnde ctx (some (.ret (some (.variable name)))) <;> rfl

private theorem fold_end_none (ctx : UCtx) :
    expandFoldEnd ctx none = .ok ([], ctx, none) := rfl

private theorem fold_end_empty (ctx : UCtx) :
    expandFoldEnd ctx (some (.ret none)) = .ok ([], ctx, some (.ret none)) := rfl

private theorem fold_end_variable (ctx : UCtx) (name : String) :
    expandFoldEnd ctx (some (.ret (some (.variable name)))) =
      .ok ([], ctx, some (.ret (some (.variable name)))) := rfl

-- No synthetic probe or wrapper is generated when the actual check list is
-- empty; in particular the absent phases need not inspect any function body.
private theorem sonden_nil (functions : List UFn) (heads : List UFnKopf) :
    uSondenFns functions heads [] = .ok [] := rfl

private theorem wrappers_nil (functions : List UFn) (heads : List UFnKopf) :
    uTorHuellen functions heads [] = .ok [] := rfl

end Gabbro.Grammatik.Parser.Uebersetze
