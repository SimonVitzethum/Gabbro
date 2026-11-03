/- Reconstruct start arguments already accepted by the canonical frontend as canonical
   closed expressions. No source evaluator or alternative execution semantics is introduced. -/
module
public import Stage0.StartArgumenta
public import Grammatik.Parser.Elab.UebersetzeAllg
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg
/-- A start retains its original arguments and name resolution, together with the existing
    canonical source acceptance check and an argument term at the actual function signature. -/
structure Resolved (u : UProg) (name : String) (sourceArgs : List SExpr) where
  function : (declOf u).Fn
  named : fnIdx u.fns name = .ok function
  canonical : uStartMit u.spaces u.tabs u.fns name sourceArgs = .ok name
  checked : ((declOf u).params function).length = sourceArgs.length ∧
    (((declOf u).params function).zip sourceArgs).all (fun p => uStartArg u.spaces u.tabs p.1 p.2) = true

/-- Resolve original source arguments before any names-only root list could discard them. -/
def resolve (u : UProg) (name : String) (sourceArgs : List SExpr) :
    Except String (Resolved u name sourceArgs) := do
  match hn : fnIdx u.fns name with
  | .error e => throw e
  | .ok f =>
    match hc : uStartMit u.spaces u.tabs u.fns name sourceArgs with
    | .error e => throw e
    | .ok actual =>
      if hr : actual = name then
        if ha : ((declOf u).params f).length = sourceArgs.length ∧
            (((declOf u).params f).zip sourceArgs).all (fun p => uStartArg u.spaces u.tabs p.1 p.2) = true then
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

/-- The actual canonical start does not depend on the world chosen for closed source arguments. -/
theorem Resolved.environment_pure {u : UProg} {name : String} {sourceArgs : List SExpr}
    (start : Resolved u name sourceArgs) (world world' : World (declOf u)) :
    start.environment world = start.environment world' :=
  arguments_pure u _ sourceArgs start.checked world world world' world'

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

private def canonicalName (u : UProg) (member : List String × List SExpr) : Except String String :=
  match member.1.getLast? with
  | some name => uStartMit u.spaces u.tabs u.fns name member.2
  | none => .error "empty path in concurrent"

private theorem uSeq_append (xs ys : List (Except String α)) :
    uSeq (xs ++ ys) = (do let a ← uSeq xs; let b ← uSeq ys; pure (a ++ b)) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, uSeq]
    cases hy : uSeq ys <;> rfl
  | cons head rest ih =>
    cases head with
    | error e => rfl
    | ok a =>
      simp only [List.cons_append, uSeq]
      rw [ih]
      cases hx : uSeq rest <;> cases hy : uSeq ys <;> rfl

/-- Flattening the source concurrent groups retains the exact canonical root-name extraction,
    including failure order; source reconstruction does not introduce a new start acceptance rule. -/
private theorem canonicalNames_flat (u : UProg) (items : List SItemTief) :
    uSeq ((sourceIdentities items).map (canonicalName u)) = uNebenWurzeln u.spaces u.tabs u.fns items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp only [sourceIdentities, List.map_cons, List.flatten_cons,
      List.nil_append, List.map_append, uNebenWurzeln] at *
    all_goals try exact ih
    case concT group =>
      rw [uSeq_append, ih]
      rfl

private theorem recoveredNames (u : UProg) {items : List SItemTief} (starts : List (SourceStart u items)) :
    uSeq ((starts.map (fun start => (start.path, start.sourceArgs))).map (canonicalName u)) =
      .ok (starts.map (·.name)) := by
  induction starts with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.map_cons, canonicalName, head.pathName, head.resolved.canonical, uSeq, ih]

/-- The reconstructed typed starts correspond exactly to the existing canonical roots,
    with the same order and multiplicity. Names-only deduplication is not justified by this bridge. -/
theorem fromItems_names {u : UProg} {items : List SItemTief} {starts : List (SourceStart u items)}
    (run : fromItems u items = .ok starts) :
    uNebenWurzeln u.spaces u.tabs u.fns items = .ok (starts.map (·.name)) := by
  rw [← canonicalNames_flat u items, ← fromItems_identity run]
  exact recoveredNames u starts

end Gabbro.Stage0.StartArgument
