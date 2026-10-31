/- Reconstruct start arguments already accepted by the canonical frontend as canonical
   closed expressions. No source evaluator or alternative execution semantics is introduced. -/
import Grammatik.Parser.Elab.UebersetzeAllg

namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Reification of exactly the existing `uStartArg` cases into the language's own typed syntax.
    In particular a pointer is a declared carrier capability, never an integer address. -/
def expression (u : UProg) (ty : Ty) (arg : SExpr)
    (accepted : uStartArg u.tabs ty arg = true) : Expr (declOf u) [] [] ty := by
  cases ty <;> cases arg <;> simp only [uStartArg] at accepted
  all_goals try contradiction
  case int.lit lo hi n =>
    have h := of_decide_eq_true accepted
    exact .widen h.1 h.2 (.lit n)
  case int.un lo hi op a =>
    cases a <;> try simp only at accepted
    all_goals try contradiction
    all_goals
      split at accepted <;> simp_all
      exact .widen accepted.1 accepted.2 (.lit _)
  case bool.tru => exact .tru
  case bool.fls => exact .fls
  case opt.call n name args => exact .none n
  case ptr.fnref n rw name =>
    by_cases hn : n < u.tabs.length
    · exact Expr.ptrOf (D := declOf u) (⟨n, hn⟩ : Fin u.tabs.length) n
        (by simp only [declOf, dite_eq_left hn]) rw
    · have hh : u.tabs[n]? = none := List.getElem?_eq_none (by omega)
      simp only [hh, Bool.false_eq_true] at accepted

/-- Reified numeric arguments retain the exact source numeral, not a default initial value. -/
theorem expression_literal (u : UProg) (lo hi : Int) (n : Nat)
    (accepted : uStartArg u.tabs (.int lo hi) (.lit n) = true)
    (before world : World (declOf u)) :
    (eval before (expression u (.int lo hi) (.lit n) accepted) world .nil).n = (n : Int) := by
  rfl

theorem expression_negative (u : UProg) (lo hi : Int) (n : Nat)
    (accepted : uStartArg u.tabs (.int lo hi) (.un "-" (.lit n)) = true)
    (before world : World (declOf u)) :
    (eval before (expression u (.int lo hi) (.un "-" (.lit n)) accepted) world .nil).n = -(n : Int) := by
  rfl

/-- A bounded negative start argument jointly witnesses acceptance and exact canonical value. -/
theorem expression_negative_zeuge (u : UProg) (world : World (declOf u)) :
    (eval world (expression u (.int (-9) 12) (.un "-" (.lit 7)) (by simp [uStartArg])) world .nil).n = -7 :=
  expression_negative u (-9) 12 7 (by simp [uStartArg]) world world

theorem expression_literal_zeuge (u : UProg) (world : World (declOf u)) :
    (eval world (expression u (.int 0 12) (.lit 7) (by simp [uStartArg])) world .nil).n = 7 :=
  expression_literal u 0 12 7 (by simp [uStartArg]) world world

/-- Canonical accepted start arguments are closed values: choosing a world cannot
    change the environment eventually encoded into a relocated root frame. -/
theorem expression_pure (u : UProg) (ty : Ty) (arg : SExpr)
    (accepted : uStartArg u.tabs ty arg = true)
    (before world before' world' : World (declOf u)) :
    eval before (expression u ty arg accepted) world .nil =
      eval before' (expression u ty arg accepted) world' .nil := by
  cases ty <;> cases arg <;> simp only [uStartArg] at accepted
  all_goals try contradiction
  all_goals try rfl
  case int.un lo hi op a =>
    cases a <;> try simp only at accepted
    all_goals try contradiction
    all_goals split at accepted <;> simp_all <;> rfl

/-- Argument environments are evaluated by the existing canonical `evalArgs`, including
    its order, and can be supplied directly to `Einheit.starts` and `RufStartG`. -/
def arguments (u : UProg) : (types : List Ty) → (args : List SExpr) →
    (checked : types.length = args.length ∧ (types.zip args).all (fun p => uStartArg u.tabs p.1 p.2) = true) →
    Args (declOf u) [] [] types
  | [], [], _ => .nil
  | ty :: types, arg :: args, checked =>
    .cons (expression u ty arg (by exact (Bool.and_eq_true_iff.mp checked.2).1))
      (arguments u types args ⟨by simpa using checked.1, by exact (Bool.and_eq_true_iff.mp checked.2).2⟩)
  | [], _ :: _, checked => by simp at checked
  | _ :: _, [], checked => by simp at checked

/-- Every complete start environment has the same canonical value in every world. -/
theorem arguments_pure (u : UProg) (types : List Ty) (args : List SExpr)
    (checked : types.length = args.length ∧
      (types.zip args).all (fun p => uStartArg u.tabs p.1 p.2) = true)
    (before world before' world' : World (declOf u)) :
    evalArgs before (arguments u types args checked) world .nil =
      evalArgs before' (arguments u types args checked) world' .nil := by
  induction types generalizing args with
  | nil =>
    cases args with
    | nil => rfl
    | cons arg args => have impossible : 0 = args.length + 1 := checked.1; omega
  | cons ty types ih =>
    cases args with
    | nil => simp at checked
    | cons arg args =>
      simp only [arguments, evalArgs]
      congr 1
      · exact expression_pure u ty arg _ before world before' world'
      · exact ih args _

/-- A start retains its original arguments and name resolution, together with the existing
    canonical source acceptance check and an argument term at the actual function signature. -/
structure Resolved (u : UProg) (name : String) (sourceArgs : List SExpr) where
  function : (declOf u).Fn
  named : fnIdx u.fns name = .ok function
  canonical : uStartMit u.tabs u.fns name sourceArgs = .ok name
  checked : ((declOf u).params function).length = sourceArgs.length ∧
    (((declOf u).params function).zip sourceArgs).all (fun p => uStartArg u.tabs p.1 p.2) = true

/-- Resolve original source arguments before any names-only root list could discard them. -/
def resolve (u : UProg) (name : String) (sourceArgs : List SExpr) :
    Except String (Resolved u name sourceArgs) := do
  match hn : fnIdx u.fns name with
  | .error e => throw e
  | .ok f =>
    match hc : uStartMit u.tabs u.fns name sourceArgs with
    | .error e => throw e
    | .ok actual =>
      if hr : actual = name then
        if ha : ((declOf u).params f).length = sourceArgs.length ∧
            (((declOf u).params f).zip sourceArgs).all (fun p => uStartArg u.tabs p.1 p.2) = true then
          pure ⟨f, hn, hc.trans (congrArg Except.ok hr), ha⟩
        else throw "ir: source start arguments differ from the canonical function signature"
      else throw "ir: canonical start name differs from its source name"

/-- The existing canonical argument evaluator supplies the semantic start environment;
    writing this full environment to the frame is the shared ABI's separate obligation. -/
def Resolved.environment {u : UProg} {name : String} {sourceArgs : List SExpr}
    (start : Resolved u name sourceArgs) (world : World (declOf u)) :
    Env (declOf u) ((declOf u).params start.function) :=
  evalArgs world (arguments u _ sourceArgs start.checked) world .nil

/-- The reconstructed environment is a valid typed G/GX start, with the exact source
    acceptance and function-name provenance retained rather than a fabricated empty environment. -/
def Resolved.start {u : UProg} {name : String} {sourceArgs : List SExpr}
    (start : Resolved u name sourceArgs) (world : World (declOf u)) :
    Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f) :=
  ⟨start.function, start.environment world⟩

/-- Source origin for one typed start. Duplicate functions with different arguments remain
    distinct entries: a names-only deduplication would lose the specified environments. -/
structure SourceStart (u : UProg) (items : List SItemTief) where
  group : List (List String × List SExpr)
  declared : SItemTief.concT group ∈ items
  path : List String
  sourceArgs : List SExpr
  member : (path, sourceArgs) ∈ group
  name : String
  pathName : path.getLast? = some name
  resolved : Resolved u name sourceArgs

/-- One source declaration is recovered without changing its member order. -/
def fromGroup (u : UProg) (items : List SItemTief)
    (group : List (List String × List SExpr)) (declared : SItemTief.concT group ∈ items) :
    Except String (List (SourceStart u items)) :=
  group.attach.mapM fun entry => do
    let path := entry.val.1
    let sourceArgs := entry.val.2
    match hp : path.getLast? with
    | none => throw "ir: concurrent start has an empty source path"
    | some name =>
      let resolved ← resolve u name sourceArgs
      pure ⟨group, declared, path, sourceArgs, entry.property, name, hp, resolved⟩

/-- A declaration contributes exactly its explicit concurrent starts. -/
def fromDeclaration (u : UProg) (items : List SItemTief)
    (item : { it // it ∈ items }) : Except String (List (SourceStart u items)) :=
  match hi : item.val with
  | .concT group => fromGroup u items group (by rw [← hi]; exact item.property)
  | _ => .ok []

/-- Recover every explicit concurrent start from the original resolved source declarations.
    This is an argument adapter only; hardware entries and dynamically created starts have
    their own contracts and are not silently included as empty argument lists. -/
def fromItems (u : UProg) (items : List SItemTief) :
    Except String (List (SourceStart u items)) := do
  let groups ← items.attach.mapM (fromDeclaration u items)
  pure groups.flatten

/-- Successful monadic reconstruction preserves an observed identity at every list position. -/
private theorem mapM_projection {α β γ ε : Type} (f : α → Except ε β)
    (left : α → γ) (right : β → γ)
    (point : ∀ a b, f a = .ok b → right b = left a)
    (xs : List α) (ys : List β) (run : xs.mapM f = .ok ys) :
    ys.map right = xs.map left := by
  induction xs generalizing ys with
  | nil =>
    change Except.ok [] = Except.ok ys at run
    cases run
    rfl
  | cons a rest ih =>
    rw [List.mapM_cons] at run
    cases ha : f a with
    | error e =>
      rw [ha] at run
      change Except.error e = Except.ok ys at run
      cases run
    | ok b =>
      rw [ha] at run
      cases hr : rest.mapM f with
      | error e =>
        rw [hr] at run
        change Except.error e = Except.ok ys at run
        cases run
      | ok bs =>
        rw [hr] at run
        change Except.ok (b :: bs) = Except.ok ys at run
        cases run
        simp only [List.map_cons, point a b ha, ih bs hr]

/-- Exact source path/argument identity, including order and multiplicity, of a recovered group. -/
theorem fromGroup_identity {u : UProg} {items : List SItemTief}
    {group : List (List String × List SExpr)} (declared : SItemTief.concT group ∈ items)
    {starts : List (SourceStart u items)} (run : fromGroup u items group declared = .ok starts) :
    starts.map (fun start => (start.path, start.sourceArgs)) = group := by
  unfold fromGroup at run
  have result := mapM_projection _ (fun entry => entry.val)
    (fun start : SourceStart u items => (start.path, start.sourceArgs)) ?_ group.attach starts run
  · simpa only [List.attach_map_subtype_val] using result
  · intro entry start success
    dsimp only at success
    split at success
    · change Except.error _ = Except.ok start at success
      cases success
    · next name hp =>
      cases hr : resolve u name entry.val.2 with
      | error e =>
        rw [hr] at success
        change Except.error e = Except.ok start at success
        cases success
      | ok resolved =>
        rw [hr] at success
        change Except.ok _ = Except.ok start at success
        cases success
        rfl

/-- The source identity sequence before elaboration: no deduplication by function name. -/
def sourceIdentities (items : List SItemTief) : List (List String × List SExpr) :=
  (items.map (fun | .concT group => group | _ => [])).flatten

/-- Every original concurrent source member occurs once in the recovered sequence, in order,
    with its exact argument tuple. Equal function names cannot collapse distinct starts. -/
theorem fromItems_identity {u : UProg} {items : List SItemTief}
    {starts : List (SourceStart u items)} (run : fromItems u items = .ok starts) :
    starts.map (fun start => (start.path, start.sourceArgs)) = sourceIdentities items := by
  have point : ∀ item bs, fromDeclaration u items item = .ok bs →
      bs.map (fun start => (start.path, start.sourceArgs)) =
        (match item.val with | .concT group => group | _ => []) := by
    intro item bs success
    unfold fromDeclaration at success
    rcases item with ⟨it, hm⟩
    cases it <;> dsimp only at success ⊢
    all_goals try (change Except.ok [] = Except.ok bs at success; cases success; rfl)
    case concT group => exact fromGroup_identity _ success
  unfold fromItems at run
  cases hg : items.attach.mapM (fromDeclaration u items) with
  | error e =>
    rw [hg] at run
    change Except.error e = Except.ok starts at run
    cases run
  | ok groups =>
    rw [hg] at run
    change Except.ok groups.flatten = Except.ok starts at run
    cases run
    rw [List.map_flatten]
    have result := mapM_projection (fromDeclaration u items)
      (fun item => match item.val with | .concT group => group | _ => [])
      (fun bs => bs.map (fun start => (start.path, start.sourceArgs))) point items.attach groups hg
    rw [result]
    unfold sourceIdentities
    exact congrArg List.flatten (List.attach_map_val (l := items)
      (f := fun (it : SItemTief) => (match it with | .concT group => group | _ => [] :
        List (List String × List SExpr))))

end Gabbro.Stage0.StartArgument
