module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Duties
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
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

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

def withMeasure (measure : UMeasure) : UProg :=
  { countdown with fns := [{function "countdown" "countdown" with decreases := some measure}] }

theorem duplicate_clause_zeuge :
    uMeasureClause [.drops (.variable "n"), .drops (.lit 0)] =
      .error "duplicate or ambiguous decreases clause" := by decide +kernel

theorem hidden_old_zeuge : uMeasureClause [.drops (.bin "+" (.lit 1) (.old (.variable "GLOBAL")))] =
    .error "old-state read in decreases" := by decide +kernel

theorem unsupported_call_zeuge : uMeasureClause [.drops (.bin "+" (.lit 1) (.call "helper" [.variable "n"]))] =
    .error "unsupported call in decreases" := by decide +kernel

theorem hidden_global_zeuge :
    (lowerMeasures (withMeasure (.bin "+" (.lit 1) (.variable "GLOBAL")))).toOption.isSome = false := by
  decide +kernel

theorem negative_measure_zeuge :
    (lowerMeasures (withMeasure (.un "-" (.lit 1)))).toOption.isSome = false := by decide +kernel

def unequalCycle : UProg :=
  { mutualU with fns := [function "left" "right", {function "right" "left" with decreases := none}] }

/-- A missing clause in one member of an actual mutual cycle is not guessed from its parameters. -/
theorem differing_cycle_lengths_zeuge : (lowerAllg unequalCycle).toOption.isSome = false := by decide +kernel

theorem absence_zeuge :
    let unit := {acyclic with fns := [{function "leaf" "leaf" with body := [], decreases := none}]}
    (match lowerMeasures unit with | .ok measures => (measures.mass 0).isEmpty | .error _ => false) = true := by
  decide +kernel

def unchanged : UProg :=
  { tabs := [], locks := [], fns := [{function "stay" "stay" with body := [.call "stay" [.val (.param "n")]]}] }
def increasing : UProg :=
  { tabs := [], locks := [], fns := [{function "grow" "grow" with needs := [.cmp "==" (.param "n") (.lit 0)], body := [.call "grow" [.val (.lit 1)]]}] }

instance : NeZero unchanged.fns.length := ⟨by decide⟩
instance : NeZero increasing.fns.length := ⟨by decide⟩

theorem unchanged_lowered : (lowerAllg unchanged).toOption.isSome = true := by decide +kernel
theorem increasing_lowered : (lowerAllg increasing).toOption.isSome = true := by decide +kernel

def unchangedP := program unchanged unchanged_lowered
def unchangedM := (exported unchanged unchanged_lowered).val
def increasingP := program increasing increasing_lowered
def increasingM := (exported increasing increasing_lowered).val

private def unchangedBody : RumpTy unchanged 0 :=
  .cons (.call 0 (.cons (.widen (by decide) (by decide) (.var .here)) .nil)
    (rufPasstB_ok (u := unchanged) (by decide)) (by rfl)) (.ret .empty (List.Perm.refl []))

private def increasingBody : RumpTy increasing 0 :=
  .cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 1)) .nil)
    (rufPasstB_ok (u := increasing) (by decide)) (by rfl)) (.ret .empty (List.Perm.refl []))

set_option maxRecDepth 100000 in
private theorem unchanged_function : lowerFnAt unchanged 0 = .ok (.tru, unchangedBody, .tru) := by rfl

set_option maxRecDepth 100000 in
private theorem increasing_function :
    lowerFnAt increasing 0 = .ok (.tru, increasingBody, .eq (.var .here) (.lit 0)) := by rfl

private theorem unchangedP_rumpf : unchangedP.rumpf 0 = unchangedBody :=
  program_rumpf_of_lowerFn unchanged_function

private theorem increasingP_rumpf : increasingP.rumpf 0 = increasingBody :=
  program_rumpf_of_lowerFn increasing_function

private theorem unchangedP_requires : unchangedP.requires 0 = .tru :=
  program_requires_of_lowerFn unchanged_function

private theorem increasingP_requires : increasingP.requires 0 = .eq (.var .here) (.lit 0) :=
  program_requires_of_lowerFn increasing_function

private theorem unchanged_cycle : zykS unchangedP [0] 0 0 = true := by
  simp only [zykS, zyklusMit, reachB, erreichB, erreichSchritt, ruftB, unchangedP_rumpf]
  rfl

private theorem increasing_cycle : zykS increasingP [0] 0 0 = true := by
  simp only [zykS, zyklusMit, reachB, erreichB, erreichSchritt, ruftB, increasingP_rumpf]
  rfl

set_option maxRecDepth 100000 in
private theorem unchangedM_mass : unchangedM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem increasingM_mass : increasingM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

/-- Structural measure export does not pretend to prove descent: the gate rejects unchanged arguments. -/
theorem unchanged_argument_zeuge
    (R : ∀ f : (declOf unchanged).Fn, World (declOf unchanged) →
      Env (declOf unchanged) ((declOf unchanged).params f) → RufAusgang f)
    (state : World (declOf unchanged)) :
    massTor unchangedM.mass (zykS unchangedP [0] 0)
      (unchangedM.mass.wert 0 state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)) R
      0 state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) = .logik (.abstieg 0) := by
  simp [massTor, unchanged_cycle, Mass.wert, unchangedM_mass, lexLt, eval, Env.get, Zahl.weiter]

/-- Increasing the actual argument also fails the existing gate, despite successful structural export. -/
theorem increasing_argument_zeuge
    (R : ∀ f : (declOf increasing).Fn, World (declOf increasing) →
      Env (declOf increasing) ((declOf increasing).params f) → RufAusgang f)
    (state : World (declOf increasing)) :
    massTor increasingM.mass (zykS increasingP [0] 0)
      (increasingM.mass.wert 0 state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)) R
      0 state (.cons (⟨1, by decide, by decide⟩ : Zahl 0 1) .nil) = .logik (.abstieg 0) := by
  simp [massTor, increasing_cycle, Mass.wert, increasingM_mass, lexLt, eval, Env.get, Zahl.weiter]

/-- The unchanged-call program cannot discharge the semantic duty, irrespective of its contracts' oracle. -/
theorem unchanged_no_duty_zeuge (passes : Nat) (Q : AxEns (declOf unchanged))
    (S : SperrInv (declOf unchanged))
    (T : (declOf unchanged).Tab ⊕ (declOf unchanged).Glob → Prop)
    (state : World (declOf unchanged)) :
    ¬ MassPflicht unchangedP passes Q S T unchangedM.mass (zykS unchangedP [0]) 0 := by
  intro duty
  let O : Orakel (declOf unchanged) :=
    ⟨fun a => Fin.elim0 a, fun r => Fin.elim0 r, fun r => Fin.elim0 r,
      fun g => Fin.elim0 g, fun _ => none⟩
  let R : ∀ f : (declOf unchanged).Fn, World (declOf unchanged) →
      Env (declOf unchanged) ((declOf unchanged).params f) → RufAusgang f := fun _ _ _ => .logik .schleife
  have frame : RespektiertRahmen unchangedP R := by
    constructor
    · intro f σ ρ _ σ' v h; cases h
    · intro f σ ρ σ' v h; cases h
  have noDescent : OhneAbstieg R := by intro g σ ρ h bad; cases bad
  have noPre : OhneVorbedingung R := by intro g σ ρ e h g' bad; cases h; cases bad
  have bad := duty O (fun a => Fin.elim0 a)
    ⟨fun r => Fin.elim0 r, fun g => Fin.elim0 g⟩ (fun a => Fin.elim0 a)
    (fun L => Fin.elim0 L) (fun L => Fin.elim0 L) idA (havocA_id T)
    R frame noDescent noPre state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)
    (by simp [ReqAmEintritt, unchangedP_requires, eval, wahr?]) 0 unchanged_cycle
  apply bad
  rw [unchangedP_rumpf]
  simp [unchangedBody, execEndHA, execStmtHA, unchanged_argument_zeuge,
    evalArgs, eval, Env.get, Zahl.weiter, leseA, idA, World.lese, World.merke,
    Expr.orte, Args.orte]

/-- The increasing-call program also fails the actual duty from a legal entry argument. -/
theorem increasing_no_duty_zeuge (passes : Nat) (Q : AxEns (declOf increasing))
    (S : SperrInv (declOf increasing))
    (T : (declOf increasing).Tab ⊕ (declOf increasing).Glob → Prop)
    (state : World (declOf increasing)) :
    ¬ MassPflicht increasingP passes Q S T increasingM.mass (zykS increasingP [0]) 0 := by
  intro duty
  let O : Orakel (declOf increasing) :=
    ⟨fun a => Fin.elim0 a, fun r => Fin.elim0 r, fun r => Fin.elim0 r,
      fun g => Fin.elim0 g, fun _ => none⟩
  let R : ∀ f : (declOf increasing).Fn, World (declOf increasing) →
      Env (declOf increasing) ((declOf increasing).params f) → RufAusgang f := fun _ _ _ => .logik .schleife
  have frame : RespektiertRahmen increasingP R := by
    constructor
    · intro f σ ρ _ σ' v h; cases h
    · intro f σ ρ σ' v h; cases h
  have noDescent : OhneAbstieg R := by intro g σ ρ h bad; cases bad
  have noPre : OhneVorbedingung R := by intro g σ ρ e h g' bad; cases h; cases bad
  have bad := duty O (fun a => Fin.elim0 a)
    ⟨fun r => Fin.elim0 r, fun g => Fin.elim0 g⟩ (fun a => Fin.elim0 a)
    (fun L => Fin.elim0 L) (fun L => Fin.elim0 L) idA (havocA_id T)
    R frame noDescent noPre state (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil)
    (by simp [ReqAmEintritt, increasingP_requires, eval, Env.get, wahr?]) 0 increasing_cycle
  apply bad
  rw [increasingP_rumpf]
  simp [increasingBody, execEndHA, execStmtHA, increasing_argument_zeuge,
    evalArgs, eval, Env.get, Zahl.weiter, leseA, idA, World.lese, World.merke,
    Expr.orte, Args.orte]

/-- Source provenance, ordinary structural admission and the actual duty hold jointly. -/
theorem lowerExpression_denotes_zeuge (state : World (declOf countdown)) (n : Zahl 0 1) :
    elabU countdownItems = .ok countdown ∧
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true ∧
    SourceTuple countdown 0 (countM.mass 0) ∧
    countM.mass.wert 0 state (.cons n .nil) = [n.n.toNat] ∧
    ∀ passes Q S T, MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 :=
  ⟨countdown_elaborated_zeuge, countdown_accepted_zeuge, countM.source 0,
    countdown_value_zeuge state n, countdown_duty_zeuge⟩

/-- The source-tree encoding preserves a nontrivial arithmetic expression exactly. -/
theorem uMeasureSource_exact_zeuge :
    let source := SExpr.bin "+" (.variable "n") (.lit 1)
    let measure := UMeasure.bin "+" (.variable "n") (.lit 1)
    uMeasureSource source = .ok measure ∧ measure.source = source := ⟨rfl, rfl⟩

theorem lowerAllg_measures_zeuge :
    lowerMeasures countdown = .ok countM ∧
    cycleLengths countdown countP countM.mass = true ∧
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true ∧
    ∀ passes Q S T, MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 :=
  ⟨(exported countdown countdown_lowered).property, by decide +kernel,
    countdown_accepted_zeuge, countdown_duty_zeuge⟩

theorem lowerMeasures_denotes_zeuge :
    (∃ c : Component countdown 0, countM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf countdown)) (env : Env (declOf countdown) ((declOf countdown).params 0)),
        SourceValue (fnAt countdown 0) (fnAt countdown 0).measureConstants env (.variable "n")
          (eval initial c.2.1 state env).n) ∧
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true ∧
    ∀ passes Q S T, MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 :=
  ⟨lowerMeasures_denotes countdown countM 0 [.drops (.variable "n")] (.variable "n")
      (.variable "n") rfl rfl rfl,
    countdown_accepted_zeuge, countdown_duty_zeuge⟩

end Gabbro.Grammatik.Parser.Measures.Fixtures
