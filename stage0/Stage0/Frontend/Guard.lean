module
public import Stage0.Frontend.Functions
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

/-- Only the exact option constructors lack a function dependency. An actual
    const declaration keeps priority, as in canonical const substitution.
    Wrong arities and every other name retain the ordinary function edge. -/
def dependencyCallHead (declared : String → Bool) (name : String) (args : List SExpr) : List String :=
  if declared name then [name] else
  match name, args with
  | "Some", [_] | "None", [] => []
  | _, _ => [name]

mutual
/-- One traversal retains every operand while the caller classifies call heads. -/
def callsWith {α : Type} (head : String → List SExpr → List α) : SExpr → List α
  | .call name args => head name args ++ callsListWith head args
  | .field a _ | .arrow a _ | .un _ a | .old a => callsWith head a
  | .index a b | .bin _ a b => callsWith head a ++ callsWith head b
  | .built _ args | .ext _ _ args => callsListWith head args
  | _ => []
def callsListWith {α : Type} (head : String → List SExpr → List α) : List SExpr → List α
  | [] => []
  | a :: rest => callsWith head a ++ callsListWith head rest
end

/-- The safety hull conservatively retains all original call-shaped heads,
    including absent constructor names; its existing guarantees are unchanged. -/
def calls (expr : SExpr) : List String := callsWith (fun name _ => [name]) expr

def callsList (args : List SExpr) : List String := callsListWith (fun name _ => [name]) args

theorem calls_call (name : String) (args : List SExpr) :
    calls (.call name args) = name :: callsList args := rfl

/-- Static call-hull check, not execution. Each newly visited name consumes one unit of fuel;
    a source unit has at most items.length distinct declared functions. -/
def safeConstantName (items : List SItemTief) : Nat → List String → String → Bool
  | fuel, visited, name =>
    if visited.contains name then true else
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match items.find? (fun
        | .fnT sig _ => sig.art == "const" && sig.name == name
        | _ => false) with
      | some (.fnT sig (.block [] (some (.ret (some body))))) =>
        evaluationClauses sig.klauseln &&
          (calls body).all (safeConstantName items fuel (name :: visited))
      | some _ => false
      | none => true

/-- A syntactic call-hull derivation. Every fresh function body has proved-safe clauses;
    revisiting a name closes a graph cycle rather than executing source code. -/
inductive SafeHull (items : List SItemTief) : List String → String → Prop
  | seen {visited name} : visited.contains name = true → SafeHull items visited name
  | absent {visited name} :
      items.find? (fun | .fnT sig _ => sig.art == "const" && sig.name == name | _ => false) = none →
      SafeHull items visited name
  | body {visited name sig expr} :
      items.find? (fun | .fnT sig _ => sig.art == "const" && sig.name == name | _ => false) =
        some (.fnT sig (.block [] (some (.ret (some expr))))) →
      evaluationClauses sig.klauseln = true →
      (∀ callee ∈ calls expr, SafeHull items (name :: visited) callee) →
      SafeHull items visited name

theorem safeConstantName_sound (items : List SItemTief) (fuel : Nat)
    (visited : List String) (name : String) (h : safeConstantName items fuel visited name = true) :
    SafeHull items visited name := by
  induction fuel generalizing visited name with
  | zero =>
    by_cases hv : visited.contains name = true
    · exact .seen hv
    · simp only [safeConstantName, hv, ↓reduceIte, Bool.false_eq_true] at h
  | succ fuel ih =>
    by_cases hv : visited.contains name = true
    · exact .seen hv
    · simp only [safeConstantName, hv, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i sig expr hf
        have hh : evaluationClauses sig.klauseln = true ∧
            (calls expr).all (safeConstantName items fuel (name :: visited)) = true := by
          simpa only [Bool.and_eq_true] using h
        exact .body hf hh.1 (fun callee hc => ih _ _ ((List.all_eq_true.mp hh.2) callee hc))
      · contradiction
      · rename_i hf
        exact .absent hf

mutual
/-- The check covers nested constant rows as well as scalar initializers. -/
def safeConstantValue (items : List SItemTief) : SKonstWert → Bool
  | .one expr => (calls expr).all (safeConstantName items (items.length + 1) [])
  | .rows values => safeConstantValues items values
def safeConstantValues (items : List SItemTief) : List SKonstWert → Bool
  | [] => true
  | value :: rest => safeConstantValue items value && safeConstantValues items rest
end

/-- A scalar expression at any depth of the canonical nested constant payload. -/
inductive ConstantLeaf (expr : SExpr) : SKonstWert → Prop
  | one : ConstantLeaf expr (.one expr)
  | row {value values} : value ∈ values → ConstantLeaf expr value → ConstantLeaf expr (.rows values)

theorem safeConstantValues_member (items : List SItemTief) (values : List SKonstWert)
    (h : safeConstantValues items values = true) (value : SKonstWert) (hm : value ∈ values) :
    safeConstantValue items value = true := by
  induction values with
  | nil => simp at hm
  | cons head rest ih =>
    have hh : safeConstantValue items head = true ∧ safeConstantValues items rest = true :=
      by simpa only [safeConstantValues, Bool.and_eq_true] using h
    rcases List.mem_cons.mp hm with he | hr
    · subst value; exact hh.1
    · exact ih hh.2 hr

theorem safeConstantValue_leaf (items : List SItemTief) {value : SKonstWert} {expr : SExpr}
    (leaf : ConstantLeaf expr value) (h : safeConstantValue items value = true) :
    (calls expr).all (safeConstantName items (items.length + 1) []) = true := by
  induction leaf with
  | one => exact h
  | row hm _ ih => exact ih (safeConstantValues_member items _ h _ hm)

/-- Guard the original declarations before any baseline constant evaluator is called. -/
def compileTimeSafe (items : List SItemTief) : Bool :=
  items.all fun
    | .constT _ _ value => safeConstantValue items value
    | _ => true

/-- Every original constant, including its nested rows and transitive call hull, passes the guard. -/
theorem compileTimeSafe_constants {items : List SItemTief} (h : compileTimeSafe items = true)
    {name : String} {ty : STyp} {value : SKonstWert} (hm : SItemTief.constT name ty value ∈ items) :
    safeConstantValue items value = true := by
  exact (List.all_eq_true.mp h) _ hm

/-- Two nested rows and an actual declared pure const function satisfy the same leaf guard. -/
theorem safeConstantValue_leaf_zeuge :
    let fn := SItemTief.fnT ⟨"const", "identity", [("x", .atom "u8")], some (.atom "u8"), none, [], []⟩
      (.block [] (some (.ret (some (.variable "x")))))
    let expr := SExpr.call "identity" [.lit 42]
    let payload := SKonstWert.rows [.rows [.one expr]]
    ConstantLeaf expr payload ∧ safeConstantValue [fn] payload = true ∧ SafeHull [fn] [] "identity" := by
  dsimp only
  have leaf : ConstantLeaf (.call "identity" [.lit 42]) (.rows [.rows [.one (.call "identity" [.lit 42])]]) :=
    .row (value := .rows [.one (.call "identity" [.lit 42])]) (by simp)
      (.row (value := .one (.call "identity" [.lit 42])) (by simp) .one)
  refine ⟨leaf, by decide, ?_⟩
  apply safeConstantName_sound _ 2 [] "identity"
  decide

end Gabbro.Stage0.Frontend
