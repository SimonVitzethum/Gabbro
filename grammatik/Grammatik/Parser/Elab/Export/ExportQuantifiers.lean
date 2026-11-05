module
public import Grammatik.Parser.Elab.Export.ExportRelations
import all Grammatik.Parser.Elab.Export.ExportRelations
import all Grammatik.Parser.Item.ElementTief.Defs1a
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

private theorem lowIdx_syntax (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (shift : Nat) (table : Fin u.tabs.length) (source : UIdx)
    (value : Expr (declOf u) Γ Λ (.index ((declOf u).count table)))
    (lowered : lowIdx u Γ Λ fn shift table source = .ok value) : IndexSyntax value := by
  cases source with
  | lit number =>
    simp only [lowIdx] at lowered
    split at lowered
    · split at lowered
      · cases lowered
        exact .widen _ _ _ (.literal _)
      · contradiction
    · contradiction
  | param name =>
    simp only [lowIdx] at lowered
    split at lowered
    · contradiction
    · split at lowered
      · split at lowered
        · contradiction
        · cases lowered
          exact .var _
      · split at lowered
        · split at lowered
          · split at lowered
            · split at lowered
              · contradiction
              · cases lowered
                exact .widen _ _ _ (.var _)
            · contradiction
          · contradiction
        · contradiction
      · contradiction

/-- Every successfully exported index has the same value after insertion of the quantifier
    binder. This is the small expression fragment the actual index exporter can produce. -/
theorem index_scope (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (shift : Nat)
    (table : Fin u.tabs.length) (source : UIdx)
    (value : Expr (declOf u) Γ Λ (.index ((declOf u).count table)))
    (lowered : lowIdx u Γ Λ fn shift table source = .ok value)
    {binderTy : Ty} (binder : Wert (declOf u) binderTy)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) :
    eval entry value.weaken state (.cons binder env) = eval entry value state env :=
  indexSyntax_scope (lowIdx_syntax u Γ Λ fn shift table source value lowered) binder entry state env

/-- The original seed is resolved before entering the binder, even when both names coincide. -/
theorem tree_quantifier_export (ctx : UCtx) (universal reverse : Bool) (binder : String)
    (source body : SExpr) (table edge : String) (number : Nat) (seed : UIdx) (predicate : UEns)
    (found : uTreeDomain ctx source = .ok (table, number, seed, edge))
    (lowered : uSichert {ctx with names := binder :: ctx.names, kinds := .index number :: ctx.kinds, types := Ty.index ((ctx.tabs[number]?).map (·.count) |>.getD 0) :: ctx.types, bits := 0 :: ctx.bits} body = .ok predicate) :
    uSichert ctx (.ext (if universal then .all else .any)
      [binder, if reverse then "ancestors" else "descendants"] [source, body]) =
      .ok (.filtered universal table binder edge reverse seed predicate) := by
  cases universal <;> cases reverse
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals unfold uSichert
  all_goals simp [found, lowered, bind, Except.bind, pure, Except.pure]

/-- Both result scope and the outer seed retain their original positions. Only the predicate
    is lowered under the freshly inserted index; the filter uses a genuine weakening. -/
theorem tree_quantifier_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn fnR : UFn) (er : Option Ty) (universal reverse : Bool) (name binder field : String)
    (source : UIdx) (body : UEns) (table : Fin u.tabs.length) (edge : SelfEdge u table field)
    (seed : Expr (declOf u) Γ Λ (.index ((declOf u).count table)))
    (predicate : Expr (declOf u) (.index ((declOf u).count table) :: Γ) Λ .bool)
    (gate : u.exportGate = .ok ()) (found : tabIdx u.tabs name = .ok table)
    (typed : selfEdge u table field = .ok edge)
    (outer : lowIdx u Γ Λ fn (if er.isSome then 1 else 0) table source = .ok seed)
    (result : ergAlsParam u fn er = .ok fnR)
    (guard : ∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ)
    (inner : lowEns u (.index ((declOf u).count table) :: Γ) Λ
      (fnR.mitIndex binder table.val ((declOf u).count table)) none body = .ok predicate) :
    lowEns u Γ Λ fn er (.filtered universal name binder field reverse source body) =
      (let filter : Expr (declOf u) (.index ((declOf u).count table) :: Γ) Λ .bool := if reverse then Expr.reaches table edge.field edge.self (.var .here) seed.weaken guard
        else Expr.reaches table edge.field edge.self seed.weaken (.var .here) guard
       .ok (if universal then Expr.forallSlots table (Expr.impl filter predicate) guard
         else Expr.existsSlots table (Expr.and filter predicate) guard)) := by
  simp only [lowEns, gate, bind, Except.bind, found, typed, outer, result, guard,
    ↓reduceDIte, inner, pure, Except.pure]
  split
  · rfl
  · contradiction

theorem tree_quantifier_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (universal reverse : Bool) (name binder field : String)
    (source : UIdx) (body : UEns) (value : Expr (declOf u) Γ Λ .bool)
    (h : lowEns u Γ Λ fn er (.filtered universal name binder field reverse source body) = .ok value) :
    u.exportGate = .ok () := by
  cases gate : u.exportGate with
  | error error => simp only [lowEns, gate, bind, Except.bind] at h; contradiction
  | ok unit => cases unit; rfl

/-- The finite filter uses the original seed under every binder, including a source binder
    that shadows its spelling. The bounded path relation is exactly the model's kette. -/
theorem tree_quantifier_meaning (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (shift : Nat) (table : Fin u.tabs.length) (edge : SelfEdge u table field)
    (source : UIdx) (seed : Expr (declOf u) Γ Λ (.index ((declOf u).count table)))
    (lowered : lowIdx u Γ Λ fn shift table source = .ok seed)
    (predicate : Expr (declOf u) (.index ((declOf u).count table) :: Γ) Λ .bool)
    (guard : darf (declOf u) table Λ) (universal reverse : Bool)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) :
    (let filter : Expr (declOf u) (.index ((declOf u).count table) :: Γ) Λ .bool := if reverse then Expr.reaches table edge.field edge.self (.var .here) seed.weaken guard
      else Expr.reaches table edge.field edge.self seed.weaken (.var .here) guard
     eval entry (if universal then Expr.forallSlots table (Expr.impl filter predicate) guard
       else Expr.existsSlots table (Expr.and filter predicate) guard) state env) =
    (let accepts := fun index : Zahl 0 ((declOf u).count table - 1) =>
       kette (fun number => edge.self ▸ state.slots table number edge.field) ((declOf u).count table).toNat
         (if reverse then index.n else (eval entry seed state env).n)
         (if reverse then (eval entry seed state env).n else index.n)
     if universal then (alleIndizes ((declOf u).count table)).all
       (fun index => !accepts index || wahr? (eval entry predicate state (.cons index env)))
     else (alleIndizes ((declOf u).count table)).any
       (fun index => accepts index && wahr? (eval entry predicate state (.cons index env)))) := by
  have shifted (index : Zahl 0 ((declOf u).count table - 1)) :=
    index_scope u Γ Λ fn shift table source seed lowered (binderTy := .index ((declOf u).count table)) index entry state env
  cases universal <;> cases reverse <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Expr.impl, eval, shifted, wahr?] <;> rfl <;> try rfl

/-- Expanding a filtered body preserves its statements in order and every explicit exit. -/
theorem traversal_filter_export (predicate : UEns) (body : List UStmt) :
    uFilteredBody (some predicate) body = [.ifBeg predicate] ++ body ++ [.ifElse, .blkEnd] := by rfl

/-- The production statement exporter keeps the invariant in the outer scope and keeps
    leave/next/return inside the filtered body, under the same loop resource discipline.
    The ending certificate includes the production fold expansion and its checks. -/
theorem traversal_export (tabs : List UTab) (heads : List UFnKopf) (fuel : Nat) (ctx : UCtx)
    (binder : String) (origin : Option SExpr) (kind : String) (subject : SExpr) (mode raw : String)
    (invariant : Option SExpr) (statements : List SAnw) (ending : Option SEnde) (rest : List SAnw)
    (loopHeader : UStmt) (loopCtx bodyCtx endCtx : UCtx) (filter : Option UEns)
    (body exits tail : List UStmt)
    (header : uLoopExport ctx binder origin kind subject mode raw invariant = .ok (loopHeader, loopCtx, filter))
    (inside : uAnwReihe tabs heads fuel loopCtx statements = .ok (body, bodyCtx))
    (exit : uFoldEndeStmt bodyCtx ending = .ok exits)
    (outside : uAnwReihe tabs heads fuel ctx rest = .ok (tail, endCtx)) :
    uAnwReihe tabs heads (fuel + 1) ctx
      (.each binder origin kind subject mode raw invariant (.block statements ending) :: rest) =
      .ok ([loopHeader] ++ uFilteredBody filter (body ++ exits) ++ [.blkEnd] ++ tail, endCtx) := by
  have unchanged : expandFoldStmt ctx
      (.each binder origin kind subject mode raw invariant (.block statements ending)) =
      .ok ([], ctx, .each binder origin kind subject mode raw invariant (.block statements ending)) := rfl
  rw [uAnwReihe, unchanged]
  simp only [bind, Except.bind]
  simp only [uAnwReiheCore, header, inside, exit, outside, pure, Except.pure, List.nil_append]

/-- The consuming header retains the domain filter, canonical declared relation and
    state-reading measure. There is no source predicate invention or initial snapshot. -/
theorem consuming_header_export (ctx context : UCtx) (binder table predecessor field : String)
    (origin : Option SExpr) (kind : String) (subject : SExpr) (raw : String)
    (invariant : Option SExpr) (inv : UEns) (filter : Option UEns) (mass : USide)
    (effects : String)
    (clauses : uConsumingClauses ctx raw = .ok (mass, effects))
    (domain : uUnvisitedLoopExport ctx binder origin kind subject "unvisited" "" invariant =
      .ok (.loopBeg binder table inv, context, filter))
    (declared : uConsumingEdge ctx table = .ok field)
    (privateName : predecessor = "#consume:predecessor") :
    uLoopExport ctx binder origin kind subject "consuming" raw invariant =
      .ok (.consumeLoopBeg binder table predecessor (filter.getD .tru)
        (.reach table field (.param predecessor) (.param binder)) inv mass effects,
        {context with loops := ("#consume:" ++ binder) :: ctx.loops}, none) := by
  subst predecessor
  have consuming : ("consuming" != "consuming") = false := bne_self_eq_false _
  simp only [uLoopExport, consuming, Bool.false_eq_true, ↓reduceIte,
    clauses, domain, declared, bind, Except.bind, pure, Except.pure]

/-- The production structured lowerer constructs exactly the canonical current-state
    consuming term. All expression checks and the resource-preserving body are premises. -/
theorem consuming_traversal_lower {loop : Bool} (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (top : AtTop u caller Λ)
    (binder table predecessor : String) (member edge inv : UEns) (mass : USide)
    (effects : String) (rest remaining : List UStmt) (t : Fin u.tabs.length)
    (membership : Expr (declOf u) (.index ((declOf u).count t) :: Γ) Λ .bool)
    (relation : Expr (declOf u) (.index ((declOf u).count t) :: .index ((declOf u).count t) :: Γ) Λ .bool)
    (invariant : Expr (declOf u) Γ Λ .bool) (bound : Int)
    (measure : Expr (declOf u) Γ Λ (.int 0 bound))
    (body : Block (declOf u) (verOf u caller) true (.index ((declOf u).count t) :: Γ) Λ Λ)
    (found : tabIdx u.tabs table = .ok t)
    (touches : lowConsumingEffects u fn table effects = .ok ())
    (outer : lowEns u Γ Λ fn none inv = .ok invariant)
    (measured : lowConsumingMass u Γ Λ fn mass = .ok ⟨bound, measure⟩)
    (members : lowEns u (.index ((declOf u).count t) :: Γ) Λ
      (fn.mitIndex binder t.val ((declOf u).count t)) none member = .ok membership)
    (edges : lowEns u (.index ((declOf u).count t) :: .index ((declOf u).count t) :: Γ) Λ
      ((fn.mitIndex binder t.val ((declOf u).count t)).mitIndex predecessor t.val ((declOf u).count t))
      none edge = .ok relation)
    (inside : lowSeqL (l := true) u caller (.index ((declOf u).count t) :: Γ)
      (fn.mitIndex binder t.val ((declOf u).count t)) fuel Λ top rest =
        .ok (⟨Λ, body⟩, .blkEnd :: remaining)) :
    lowStructL (l := loop) u caller Γ fn (fuel + 1) Λ top
      (.consumeLoopBeg binder table predecessor member edge inv mass effects) rest =
      .ok (⟨Λ, .consumeTraverse t membership relation invariant bound measure body⟩, remaining) := by
  simp only [lowStructL_succ, lowStructStep, lowStufe_seq, found, touches, outer,
    measured, members, edges, inside, bind, Except.bind, pure, Except.pure, dif_pos]

/-- The exported consuming term uses the existing dynamic selector and decrease checks,
    including logical failure and every body outcome; it has no finite-sweep shortcut. -/
theorem consuming_traversal_meaning {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (table : D.Tab)
    (member : Expr D (.index (D.count table) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count table) :: .index (D.count table) :: Γ) Λ .bool)
    (invariant : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count table) :: Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : World D) (env : Env D Γ) :
    execStmt oracle passes calls (l := l)
      (.consumeTraverse table member edge invariant bound mass body) state env =
      verbrauchLauf table (fun state env => execBlock oracle passes calls body state env)
        (fun state env => let observed := state.lese Λ invariant.orte
          (observed, wahr? (eval observed invariant observed env)))
        (verbrauchSel table member edge)
        (fun state env => let observed := state.lese Λ mass.orte
          (observed, (eval observed mass observed env).n))
        bound ((D.count table).toNat + bound.toNat + 1) state env := by rfl

/-- A skipped node still records the filter's reads. Every body outcome, including early
    exits and failures, is returned unchanged when the node is selected. -/
theorem filtered_step_meaning {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (predicate : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : World D) (env : Env D Γ) :
    execBlock oracle passes calls (.cons (.ite predicate body .nil) .nil) state env =
      (let observed := state.lese Λ predicate.orte
       if wahr? (eval observed predicate observed env) then
         execBlock oracle passes calls body observed env else .ok observed env) := by
  by_cases selected : wahr? (eval (state.lese Λ predicate.orte) predicate
      (state.lese Λ predicate.orte) env) = true
  · simp only [execBlock, execStmt, selected, ↓reduceIte]
    cases execBlock oracle passes calls body (state.lese Λ predicate.orte) env <;> rfl
  · simp only [execBlock, execStmt, selected, ↓reduceIte]
    rfl

/-- The complete finite traversal is exactly G's existing traversal with a filtered step.
    Invariant reads/checks, the declared count and all exit handling stay in traverseLauf. -/
theorem filtered_traversal_meaning {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (table : D.Tab) (invariant : Expr D Γ Λ .bool)
    (predicate : Expr D (.index (D.count table) :: Γ) Λ .bool)
    (body : Block D V true (.index (D.count table) :: Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : World D) (env : Env D Γ) :
    execStmt oracle passes calls (l := l)
      (.traverse table invariant (.cons (.ite predicate body .nil) .nil)) state env =
      traverseLauf
        (fun state env => let observed := state.lese Λ predicate.orte
          if wahr? (eval observed predicate observed env) then
            execBlock oracle passes calls body observed env else .ok observed env)
        (fun state env => let observed := state.lese Λ invariant.orte
          (observed, wahr? (eval observed invariant observed env)))
        (alleIndizes (D.count table)) state env := by
  simp only [execStmt] <;> try rfl
  congr 1
  funext state env
  exact filtered_step_meaning predicate body oracle passes calls state env

end Gabbro.Grammatik.Parser.ExportPreservation
