module
public import Stage0.Frontend.AliasOrder
public import Stage0.Frontend.Guard
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema
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


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Separate namespaces prevent a type spelling from being mistaken for a scalar binding. -/
inductive DependencyName
  | value : String → DependencyName
  | type : String → DependencyName
  | function : String → DependencyName

/-- Use the canonical kernel-computable spelling comparison in graph search. -/
def sameDependency : DependencyName → DependencyName → Bool
  | .value a, .value b | .type a, .type b | .function a, .function b => strEq a b
  | _, _ => false

def DependencyName.label : DependencyName → String
  | .value name => "constant " ++ name
  | .type name => "type " ++ name
  | .function name => "const function " ++ name

/-- Typed constructor heads depend on the owning schema. Every unresolved head
    and every wrong arity remains a function dependency; const functions win. -/
def dependencyCallReferences (declared : String → Bool)
    (owner : String → Bool → Option String) (name : String) (args : List SExpr) : List DependencyName :=
  (dependencyCallHead declared name args).flatMap fun callee =>
    if declared callee then [.function callee] else
    match args with
    | [_] => match owner callee true with
      | some schema => [.type schema]
      | none => [.function callee]
    | _ => [.function callee]

mutual
/-- Canonical scalar operands. Limit words are builtin type queries, not constant references.
    Function bodies use parameter bindings only; call nodes below track their signature scopes. -/
def valueReferences (source : SExpr) (declared : String → Bool := fun _ => false)
    (owner : String → Bool → Option String := fun _ _ => none) : List DependencyName :=
  match source with
  | .variable name => match owner name false with
    | some schema => [.type schema]
    | none => [.value name]
  | .field (.variable _) _ => []
  | .field a _ | .arrow a _ | .un _ a | .old a => valueReferences a declared owner
  | .index a b | .bin _ a b => valueReferences a declared owner ++ valueReferences b declared owner
  | .call name args => dependencyCallReferences declared owner name args ++
      valueReferenceList args declared owner
  | .built _ args | .ext _ _ args => valueReferenceList args declared owner
  | _ => []
def valueReferenceList (sources : List SExpr) (declared : String → Bool := fun _ => false)
    (owner : String → Bool → Option String := fun _ _ => none) : List DependencyName :=
  match sources with
  | [] => []
  | a :: rest => valueReferences a declared owner ++ valueReferenceList rest declared owner
end

theorem valueReferences_call (name : String) (args : List SExpr) (declared : String → Bool)
    (owner : String → Bool → Option String) :
    valueReferences (.call name args) declared owner = dependencyCallReferences declared owner name args ++
      valueReferenceList args declared owner := rfl

/-- Bounds and counts use the same original operands as canonical type elaboration. Range
    bases contribute too: uTypIn resolves the base before admitting its numeric bounds. -/
def typeReferences (source : STyp) (declared : String → Bool := fun _ => false)
    (owner : String → Bool → Option String := fun _ _ => none) : List DependencyName :=
  match source with
  | .atom name => [.type name]
  | .range base lo hi _ => typeReferences base declared owner ++
      valueReferences lo declared owner ++ valueReferences hi declared owner
  | .array element count => typeReferences element declared owner ++ valueReferences count declared owner
  | .wrap ty | .embed ty _ _ => typeReferences ty declared owner
  | .str count => valueReferences count declared owner
  | _ => []

mutual
/-- Every row leaf remains in the graph, including unused constant arrays. -/
def payloadReferences (source : SKonstWert) (declared : String → Bool := fun _ => false)
    (owner : String → Bool → Option String := fun _ _ => none) : List DependencyName :=
  match source with
  | .one expr => valueReferences expr declared owner
  | .rows rows => payloadReferenceList rows declared owner
def payloadReferenceList (sources : List SKonstWert) (declared : String → Bool := fun _ => false)
    (owner : String → Bool → Option String := fun _ _ => none) : List DependencyName :=
  match sources with
  | [] => []
  | row :: rest => payloadReferences row declared owner ++ payloadReferenceList rest declared owner
end

/-- Use only the canonical complete schemas. Ambiguous names have no guessed
    owner; the ordinary unresolved-name edge and final typed checks remain. -/
def taggedConstructorOwner (schemas : List (USum STyp)) (name : String) (payload : Bool) : Option String :=
  match schemas.filter (fun schema => schema.cases.any (fun entry =>
      strEq entry.1 name && entry.2.isSome == payload)) with
  | [schema] => some schema.name
  | _ => none

/-- Every resolved owner is an actual original case with the requested payload
    presence. No type-name default or guessed case can produce an edge. -/
theorem taggedConstructorOwner_sound {schemas : List (USum STyp)} {name owner : String} {payload : Bool}
    (resolved : taggedConstructorOwner schemas name payload = some owner) :
    ∃ schema ∈ schemas, schema.name = owner ∧ ∃ entry ∈ schema.cases,
      strEq entry.1 name = true ∧ (entry.2.isSome == payload) = true := by
  unfold taggedConstructorOwner at resolved
  cases selected : schemas.filter (fun schema => schema.cases.any (fun entry =>
      strEq entry.1 name && entry.2.isSome == payload)) with
  | nil => rw [selected] at resolved; cases resolved
  | cons schema rest =>
    cases rest with
    | nil =>
      rw [selected] at resolved
      have same : schema.name = owner := Option.some.inj resolved
      have member : schema ∈ schemas.filter (fun candidate => candidate.cases.any (fun entry =>
          strEq entry.1 name && entry.2.isSome == payload)) := by
        rw [selected]
        exact List.mem_cons_self
      have kept := List.mem_filter.mp member
      obtain ⟨entry, inside, matched⟩ := List.any_eq_true.mp kept.2
      exact ⟨schema, kept.1, same, entry, inside,
        (Bool.and_eq_true_iff.mp matched).1, (Bool.and_eq_true_iff.mp matched).2⟩
    | cons other tail => rw [selected] at resolved; cases resolved

/-- Source declarations and their compile-time dependencies. Function bodies cannot capture
    global constants in uKonstWert; only calls and signature types contribute global edges. -/
def dependencyDeclarations (items : List SItemTief) : List (DependencyName × List DependencyName) :=
  let declared := fun name => items.any fun
    | .fnT sig _ => sig.art == "const" && strEq sig.name name
    | _ => false
  let schemas := uSumSchemas items
  let owner := fun name payload =>
    if !payload && items.any (fun | .constT declared _ _ => strEq declared name | _ => false) then none
    else match schemas with
      | .ok values => taggedConstructorOwner values name payload
      | .error _ => none
  let head := dependencyCallReferences declared owner
  let constructor := fun name => items.any fun
    | .typeT flags declared [] [] (some (.raw _)) => strEq declared name &&
        !flags.any (fun flag => strEq flag "tagged" || strEq flag "linear")
    | _ => false
  let resolve : DependencyName → DependencyName := fun reference => match reference with
    | .function name => if constructor name then .type name else reference
    | _ => reference
  (items.filterMap fun
    | .typeT _ name [] _ (some ty@(.atom _))
    | .typeT _ name [] _ (some ty@(.range _ _ _ _)) => some (.type name, typeReferences ty declared owner)
    | .typeT flags name [] [] (some (.raw _)) =>
      if flags.any (strEq "tagged") then
        match schemas with
        | .ok values => match values.find? (fun schema => strEq schema.name name) with
          | some schema => some (.type name, schema.cases.flatMap (fun entry =>
              entry.2.toList.flatMap (fun ty => typeReferences ty declared owner)))
          | none => none
        -- A schema error is never converted into a schema or constructor edge.
        -- The canonical uSums phase still reports that original failure.
        | .error _ => none
      else if flags.any (strEq "linear") then none
      else match expandRecord (items.length + 1) items [] name with
        | .ok fields => some (.type name, fields.flatMap (fun field => typeReferences field.ftyp declared owner))
        | .error _ => some (.type name, [.type name])
    | .constT name ty payload => some (.value name,
        typeReferences ty declared owner ++ payloadReferences payload declared owner)
    | .fnT sig (.block [] (some (.ret (some body)))) =>
      if sig.art == "const" then some (.function sig.name,
        sig.params.flatMap (fun p => typeReferences p.2 declared owner) ++
        (sig.res.toList.flatMap (fun ty => typeReferences ty declared owner)) ++ callsWith head body)
      else none
    | _ => none).map fun (name, deps) => (name, deps.map resolve)

def constantNames (items : List SItemTief) : List String :=
  items.filterMap fun | .constT name _ _ => some name | _ => none

def constantEdges (items : List SItemTief) : List (DependencyName × DependencyName) :=
  (dependencyDeclarations items).flatMap fun (name, deps) => deps.map (name, ·)

/-- Independently checked strict ranks exclude mixed constant/type/signature cycles. -/
def ConstantAcyclic (items : List SItemTief) : Prop :=
  ∃ rank : DependencyName → Nat, ∀ edge ∈ constantEdges items, rank edge.2 < rank edge.1

theorem ConstantAcyclic.no_cycle {items : List SItemTief} (h : ConstantAcyclic items)
    (name : DependencyName) :
    ¬ Relation.TransGen (fun a b => (a, b) ∈ constantEdges items) name name := by
  obtain ⟨rank, hr⟩ := h
  intro cycle
  have decreases {a b : DependencyName}
      (path : Relation.TransGen (fun a b => (a, b) ∈ constantEdges items) a b) : rank b < rank a := by
    induction path with
    | single edge => exact hr _ edge
    | tail _ edge ih => exact Nat.lt_trans (hr _ edge) ih
  exact Nat.lt_irrefl _ (decreases cycle)

/-- Search candidates carry no trust: the edge rank check below is independent of this DFS.
    Completed nodes are memoized so shared dependency diamonds are visited once. Active names
    still diagnose cycles before lookup; missing values/functions retain their exact spelling. -/
def constantDepth (items : List SItemTief) : Nat → List DependencyName →
    List (DependencyName × Nat) → DependencyName →
    Except String (Nat × List (DependencyName × Nat))
  | 0, _, _, _ => .error "compile-time constant dependency depth exhausted"
  | fuel + 1, active, resolved, name =>
    if active.any (sameDependency name) then .error ("compile-time dependency cycle at " ++ name.label)
    else match resolved.find? (fun entry => sameDependency entry.1 name) with
    | some entry => .ok (entry.2, resolved)
    | none => match (dependencyDeclarations items).find? (fun entry => sameDependency entry.1 name) with
      | none => match name with
        | .type _ => .ok (0, resolved)
        | _ => .error ("unresolved compile-time dependency: " ++ name.label)
      | some entry => do
        let (depth, next) ← entry.2.foldlM (fun (depth, known) dependency => do
          let (value, known) ← constantDepth items fuel (name :: active) known dependency
          pure (max depth value, known)) (0, resolved)
        let value := depth + 1
        pure (value, (name, value) :: next)

structure ConstantOrder (items : List SItemTief) where
  ordered : List SItemTief
  permutation : ordered.Perm items
  acyclic : ConstantAcyclic items
  unique : (constantNames items).Nodup

/-- Reuse the proved stable declaration permutation; no runtime item is moved or rewritten. -/
def orderConstants (items : List SItemTief) : Except String (ConstantOrder items) :=
  if hn : (constantNames items).Nodup then do
    let nodes := (dependencyDeclarations items).map (·.1)
    let depths ← nodes.foldlM (fun known name => do
      let (_, next) ← constantDepth items (nodes.length + 2) [] known name
      pure next) []
    let rank := fun name => ((depths.find? (fun entry => sameDependency entry.1 name)).map (·.2)).getD 0
    if h : (constantEdges items).all (fun edge => rank edge.2 < rank edge.1) then
      let priority := fun item => match item with
        | .constT name _ _ => rank (.value name)
        | _ => 0
      let ordered := aliasRankOrder priority items
      pure ⟨ordered.val, ordered.property, ⟨rank, by
        intro edge hm
        exact of_decide_eq_true (List.all_eq_true.mp h edge hm)⟩, hn⟩
    else throw "compile-time constant dependency ranks are inconsistent"
  else .error "compile-time constant dependency ordering requires unique constant names"

/-- Both a forward scalar edge and a range-bound edge inhabit the generic cycle exclusion. -/
theorem ConstantAcyclic.no_cycle_zeuge :
    let items := [SItemTief.constT "ANSWER" (.atom "Bound") (.one (.variable "LIMIT")),
      .typeT [] "Bound" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "LIMIT") false)),
      .constT "LIMIT" (.atom "u8") (.one (.lit 42))]
    ∃ order : ConstantOrder items, orderConstants items = .ok order ∧
      ¬ Relation.TransGen (fun a b => (a, b) ∈ constantEdges items) (.value "ANSWER") (.value "ANSWER") := by
  dsimp only
  refine ⟨(orderConstants _).toOption.get (by decide +kernel), ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · exact ((orderConstants _).toOption.get (by decide +kernel)).acyclic.no_cycle _

/-- Unused cycles cannot be hidden behind a candidate fixed point. -/
theorem orderConstants_cycle_zeuge :
    orderConstants [SItemTief.constT "A" (.atom "u8") (.one (.variable "B")),
      .constT "B" (.atom "u8") (.one (.variable "A"))] =
      .error "compile-time dependency cycle at constant A" := by rfl

/-- Removing a constructor head retains nested function and original value edges. -/
theorem option_dependencies_zeuge :
    valueReferences (.call "Some" [.call "work" [.variable "LIMIT"]]) =
      [.function "work", .value "LIMIT"] ∧
    valueReferences (.call "None" []) = [] ∧
    valueReferences (.call "Some" [.lit 1]) (fun name => strEq name "Some") =
      [.function "Some"] := ⟨rfl, rfl, rfl⟩

/-- A malformed constructor or an unknown head is never silently removed. -/
theorem option_wrong_arity_zeuge :
    valueReferences (.call "Some" []) = [.function "Some"] ∧
    valueReferences (.call "Some" [.lit 1, .lit 2]) = [.function "Some"] ∧
    valueReferences (.call "None" [.lit 1]) = [.function "None"] ∧
    valueReferences (.call "unknown" []) = [.function "unknown"] := ⟨rfl, rfl, rfl, rfl⟩

/-- Constructor operands cannot hide an unresolved call or an unused user cycle. -/
theorem option_nested_unresolved_zeuge :
    orderConstants [.constT "K" (.atom "u8") (.one (.call "Some" [.call "missing" []]))] =
      .error "unresolved compile-time dependency: const function missing" := by rfl

theorem option_nested_cycle_zeuge :
    let fn := SItemTief.fnT ⟨"const", "loop", [], some (.atom "u8"), none, [], []⟩
      (.block [] (some (.ret (some (.call "Some" [.call "loop" []])))))
    orderConstants [fn] = .error "compile-time dependency cycle at const function loop" := by rfl

theorem option_declared_cycle_zeuge :
    let fn := SItemTief.fnT ⟨"const", "Some", [("x", .atom "u8")], some (.atom "u8"), none, [], []⟩
      (.block [] (some (.ret (some (.call "Some" [.variable "x"])))))
    orderConstants [fn] = .error "compile-time dependency cycle at const function Some" := by rfl

/-- The schema controls arity; nested calls and variable operands remain intact. -/
theorem tagged_dependencies_zeuge :
    let schema : USum STyp := ⟨"Choice", [("Empty", none), ("Data", some (.atom "u8"))]⟩
    let owner := taggedConstructorOwner [schema]
    valueReferences (.call "Data" [.call "work" [.variable "LIMIT"]]) (fun _ => false) owner =
      [.type "Choice", .function "work", .value "LIMIT"] ∧
    valueReferences (.variable "Empty") (fun _ => false) owner = [.type "Choice"] ∧
    valueReferences (.call "Data" []) (fun _ => false) owner = [.function "Data"] ∧
    valueReferences (.call "Empty" [.lit 1]) (fun _ => false) owner = [.function "Empty"] ∧
    valueReferences (.call "Data" [.lit 1]) (fun name => strEq name "Data") owner =
      [.function "Data"] := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tagged_ambiguous_owner_zeuge :
    taggedConstructorOwner
      [⟨"First", [("Data", some (.atom "u8"))]⟩,
       ⟨"Second", [("Data", some (.atom "u8"))]⟩] "Data" true = none := rfl

end Gabbro.Stage0.Frontend
