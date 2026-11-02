module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Expression
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- The exact component type required by `Mass`, at entry parameters and entry resources. -/
abbrev Component (u : UProg) (f : (declOf u).Fn) :=
  Σ hi : Int, {e : Expr (declOf u) ((declOf u).params f)
    (Signatur.anfang (declOf u) ((declOf u).signatur f)) (.int 0 hi) // e.orte = []}

/-- Absence stays empty; a written expression denotes precisely the sole exported component. -/
def SourceTuple (u : UProg) (f : (declOf u).Fn) (tuple : List (Component u f)) : Prop :=
  match (fnAt u f).decreases with
  | none => tuple = []
  | some source => ∃ c : Component u f, tuple = [c] ∧
      ∀ (entry state : World (declOf u)) (env : Env (declOf u) ((declOf u).params f)),
        SourceValue (fnAt u f) (fnAt u f).measureConstants env source.source
          (eval entry c.2.1 state env).n

structure At (u : UProg) (f : (declOf u).Fn) where
  tuple : List (Component u f)
  source : SourceTuple u f tuple

/-- A source measure is widened only after its inferred lower bound is proved nonnegative. -/
def lowerAt (u : UProg) (f : (declOf u).Fn) : Except String (At u f) :=
  match hs : (fnAt u f).decreases with
  | none => .ok ⟨[], by simp only [SourceTuple, hs]⟩
  | some source => do
    let expression ← lowerExpression u ((declOf u).params f)
      (Signatur.anfang (declOf u) ((declOf u).signatur f)) (fnAt u f) source.source
    if hn : 0 ≤ expression.side.range.1 then
      let term := Expr.widen hn (Int.le_refl expression.side.range.2) expression.side.term
      have footprint : term.orte = [] := expression.footprint
      let component : Component u f := ⟨expression.side.range.2, term, footprint⟩
      pure ⟨[component], by
        simp only [SourceTuple, hs]
        exact ⟨component, rfl, expression.denotes⟩⟩
    else throw "decreases measure may be negative at entry"

/-- The exported measure and source denotation for every declared function. -/
structure Export (u : UProg) where
  mass : Mass (declOf u)
  source : ∀ f, SourceTuple u f (mass f)

/-- Collect an indexed family once, preserving the type at each function index. -/
def collect : (n : Nat) → (T : Fin n → Type) → ((i : Fin n) → Except String (T i)) →
    Except String ((i : Fin n) → T i)
  | 0, _, _ => pure (fun i => nomatch i)
  | n + 1, T, get => do
    let head ← get 0
    let tail ← collect n (fun i => T i.succ) (fun i => get i.succ)
    pure (Fin.cases head tail)

/-- Lower all original measures over the complete function enumeration; none is guessed. -/
def lowerMeasures (u : UProg) : Except String (Export u) := do
  let entries ← collect u.fns.length (At u) (lowerAt u)
  pure ⟨fun f => (entries f).tuple, fun f => (entries f).source⟩

/-- Source equality remains available independently of the caller that consumes the exported unit. -/
theorem lowerMeasures_source (u : UProg) (exported : Export u)
    (_lowered : lowerMeasures u = .ok exported) (f : (declOf u).Fn) :
    SourceTuple u f (exported.mass f) := exported.source f

/-- An absent clause is exactly the empty tuple, even in a unit with other measures. -/
theorem lowerMeasures_absent (u : UProg) (exported : Export u) (f : (declOf u).Fn)
    (absent : (fnAt u f).decreases = none) : exported.mass f = [] := by
  have h := exported.source f
  simpa only [SourceTuple, absent] using h

/-- Check equal tuple lengths on cycles using every function, including functions without clauses. -/
def cycleLengths (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u)) : Bool :=
  (List.finRange u.fns.length).all fun f => (List.finRange u.fns.length).all fun g =>
    !(zykS P (List.finRange u.fns.length) f g) || decide ((m f).length = (m g).length)

theorem cycleLengths_sound (u : UProg) (P : Programm (declOf u)) (m : Mass (declOf u))
    (checked : cycleLengths u P m = true) :
    ∀ f g, zykS P (List.finRange u.fns.length) f g = true → (m f).length = (m g).length := by
  intro f g cycle
  have hf := List.all_eq_true.mp checked f (List.mem_finRange f)
  have hg := List.all_eq_true.mp hf g (List.mem_finRange g)
  simpa only [cycle, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hg

/-- Structural safety remains the ordinary checker; this gate checks only measure export and lengths. -/
def checkedProgram (u : UProg) (P : Programm (declOf u)) :
    Except String (Programm (declOf u) × List (declOf u).Fn) :=
  match lowerMeasures u with
  | .error error => .error error
  | .ok exported =>
    if cycleLengths u P exported.mass then .ok (P, List.finRange u.fns.length)
    else .error "differing decreases tuple lengths in a recursion cycle"

/-- Successful assembly of a program carries a successful exact measure export. -/
theorem checkedProgram_export (u : UProg) (P Q : Programm (declOf u)) (fs : List (declOf u).Fn)
    (checked : checkedProgram u P = .ok (Q, fs)) :
    ∃ exported, lowerMeasures u = .ok exported ∧ cycleLengths u Q exported.mass = true := by
  unfold checkedProgram at checked
  cases hm : lowerMeasures u with
  | error error => simp only [hm, reduceCtorEq] at checked
  | ok exported =>
    rw [hm] at checked
    split at checked
    next good =>
      have same : P = Q := congrArg Prod.fst (Except.ok.inj checked)
      exact ⟨exported, hm, same ▸ good⟩
    next => contradiction

/-- Extract checked data by computation; the failure branch contradicts lowering success. -/
def checkedExport (u : UProg) (success : ∃ exported, lowerMeasures u = .ok exported) :
    {exported : Export u // lowerMeasures u = .ok exported} :=
  match hm : lowerMeasures u with
  | .ok exported => ⟨exported, hm⟩
  | .error _ => by
    obtain ⟨exported, he⟩ := success
    rw [he] at hm
    cases hm

end Gabbro.Grammatik.Parser.Measures
