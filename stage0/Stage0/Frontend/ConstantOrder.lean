module
public import Stage0.Frontend.AliasOrder
public import Stage0.Frontend.Guard
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

mutual
/-- Canonical scalar operands. Limit words are builtin type queries, not constant references.
    Function bodies use parameter bindings only; call nodes below track their signature scopes. -/
def valueReferences : SExpr → List DependencyName
  | .variable name => [.value name]
  | .field (.variable _) _ => []
  | .field a _ | .arrow a _ | .un _ a | .old a => valueReferences a
  | .index a b | .bin _ a b => valueReferences a ++ valueReferences b
  | .call name args => .function name :: valueReferenceList args
  | .built _ args | .ext _ _ args => valueReferenceList args
  | _ => []
def valueReferenceList : List SExpr → List DependencyName
  | [] => []
  | a :: rest => valueReferences a ++ valueReferenceList rest
end

/-- Bounds and counts use the same original expression operands as canonical type elaboration.
    Range bases do not contribute: uFeldTyp/uTyp determine ranges from their bounds alone. -/
def typeReferences : STyp → List DependencyName
  | .atom name => [.type name]
  | .range _ lo hi _ => valueReferences lo ++ valueReferences hi
  | .array element count => typeReferences element ++ valueReferences count
  | .wrap ty | .embed ty _ _ => typeReferences ty
  | .str count => valueReferences count
  | _ => []

mutual
/-- Every row leaf remains in the graph, including unused constant arrays. -/
def payloadReferences : SKonstWert → List DependencyName
  | .one expr => valueReferences expr
  | .rows rows => payloadReferenceList rows
def payloadReferenceList : List SKonstWert → List DependencyName
  | [] => []
  | row :: rest => payloadReferences row ++ payloadReferenceList rest
end

/-- Source declarations and their compile-time dependencies. Function bodies cannot capture
    global constants in uKonstWert; only calls and signature types contribute global edges. -/
def dependencyDeclarations (items : List SItemTief) : List (DependencyName × List DependencyName) :=
  items.filterMap fun
    | .typeT _ name [] _ (some ty@(.atom _))
    | .typeT _ name [] _ (some ty@(.range _ _ _ _)) => some (.type name, typeReferences ty)
    | .constT name ty payload => some (.value name, typeReferences ty ++ payloadReferences payload)
    | .fnT sig (.block [] (some (.ret (some body)))) =>
      if sig.art == "const" then some (.function sig.name,
        sig.params.flatMap (fun p => typeReferences p.2) ++
        (sig.res.toList.flatMap typeReferences) ++ (calls body).map DependencyName.function)
      else none
    | _ => none

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

end Gabbro.Stage0.Frontend
