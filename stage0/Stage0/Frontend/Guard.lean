import Stage0.Frontend.Functions

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

mutual
/-- Direct calls nested anywhere in a compile-time expression. Variable spellings are not calls. -/
def calls : SExpr → List String
  | .call name args => name :: callsList args
  | .field a _ | .arrow a _ | .un _ a | .old a => calls a
  | .index a b | .bin _ a b => calls a ++ calls b
  | .built _ args | .ext _ _ args => callsList args
  | _ => []
def callsList : List SExpr → List String
  | [] => []
  | a :: rest => calls a ++ callsList rest
end

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

end Gabbro.Stage0.Frontend
