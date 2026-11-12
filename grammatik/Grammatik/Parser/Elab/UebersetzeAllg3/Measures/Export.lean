module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Ranks
public import Grammatik.Parser.Elab.UebersetzeAllg3.Memo
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

theorem collect_eq_sammle : ∀ (n : Nat) (T : Fin n → Type) (get : (i : Fin n) → Except String (T i)),
    collect n T get = sammle n T get
  | 0, _, _ => rfl
  | n + 1, T, get => by
    simp only [collect, sammle, collect_eq_sammle n]

/-- **Compiled code collects through a table filled once** (`sammleSchnell`). -/
@[csimp] theorem collect_eq_schnell : @collect = @sammleSchnell := by
  funext n T get
  rw [collect_eq_sammle, sammle_eq_schnell]

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

/-- Structural safety remains the ordinary checker; this gate checks only measure export and lengths. -/
def checkedProgram (u : UProg) (P : Programm (declOf u)) :
    Except String (Programm (declOf u) × List (declOf u).Fn) :=
  match lowerMeasures u with
  | .error error => .error error
  | .ok exported =>
    if cycleLengths u P exported.mass then .ok (P, List.finRange u.fns.length)
    else .error "differing decreases tuple lengths in a recursion cycle"

/-- The measure gate passes its program through unchanged. -/
theorem checkedProgram_eq {u : UProg} {P Q : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : checkedProgram u P = .ok (Q, fs)) : Q = P ∧ fs = List.finRange u.fns.length := by
  unfold checkedProgram at h
  split at h
  · cases h
  · split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h

/-- Successful assembly of a program carries a successful exact measure export. -/
theorem checkedProgram_export (u : UProg) (P Q : Programm (declOf u)) (fs : List (declOf u).Fn)
    (checked : checkedProgram u P = .ok (Q, fs)) :
    ∃ exported, lowerMeasures u = .ok exported ∧ cycleLengths u Q exported.mass = true := by
  unfold checkedProgram at checked
  cases hm : lowerMeasures u with
  | error error => simp only [hm, reduceCtorEq] at checked
  | ok exported =>
    simp only [hm] at checked
    split at checked
    · rename_i good
      have same : P = Q := congrArg Prod.fst (Except.ok.inj checked)
      exact ⟨exported, rfl, same ▸ good⟩
    · cases checked

/-- Extract checked data by computation; the failure branch contradicts lowering success. -/
def checkedExport (u : UProg) (success : ∃ exported, lowerMeasures u = .ok exported) :
    {exported : Export u // lowerMeasures u = .ok exported} :=
  match hm : lowerMeasures u with
  | .ok exported => ⟨exported, rfl⟩
  | .error _ => False.elim (by
    obtain ⟨exported, he⟩ := success
    rw [he] at hm
    cases hm)

end Gabbro.Grammatik.Parser.Measures
