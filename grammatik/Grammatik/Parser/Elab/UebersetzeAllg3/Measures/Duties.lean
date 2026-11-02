module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Fixtures
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
open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Recover the body through the generic function certificate; do not reduce program assembly. -/
private theorem countP_rumpf : countP.rumpf 0 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := countdown) (by decide)) (by rfl)) .nil) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The left member calls the right member with the literal zero. -/
private theorem mutualP_rumpf_zero : mutualP.rumpf 0 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 1 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := mutualU) (by decide)) (by rfl)) .nil) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The right member calls the left member with the literal zero. -/
private theorem mutualP_rumpf_one : mutualP.rumpf 1 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := mutualU) (by decide)) (by rfl)) .nil) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Both calls survive lowering, including the call before the final call. -/
private theorem nonTailP_rumpf : nonTailP.rumpf 0 =
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
        (rufPasstB_ok (u := nonTail) (by decide)) (by rfl))
        (.cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 0)) .nil)
          (rufPasstB_ok (u := nonTail) (by decide)) (by rfl)) .nil)) .nil)
      (.ret .empty (List.Perm.refl [])) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  rfl

set_option maxRecDepth 100000 in
private theorem acyclicP_rumpf : acyclicP.rumpf 0 = .ret .empty (List.Perm.refl []) := by
  apply program_rumpf_of_lowerFn (ens := .tru) (req := .tru)
  rfl

set_option maxRecDepth 100000 in
/-- The actual exported component is the widened entry parameter, with its original footprint proof. -/
private theorem countM_mass : countM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem mutualM_mass_zero : mutualM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem mutualM_mass_one : mutualM.mass 1 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem nonTailM_mass : nonTailM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

/-- The countdown's exported `n` is its actual nonnegative entry argument. -/
theorem countdown_value_zeuge (state : World (declOf countdown)) (n : Zahl 0 1) :
    countM.mass.wert 0 state (.cons n .nil) = [n.n.toNat] := by rfl

/-- The finite countdown satisfies the real measure duty, for all pass grants and handlers. -/
theorem countdown_duty_zeuge (passes : Nat) (Q : AxEns (declOf countdown))
    (S : SperrInv (declOf countdown)) (T : (declOf countdown).Tab ⊕ (declOf countdown).Glob → Prop) :
    MassPflicht countP passes Q S T countM.mass (zykS countP [0]) 0 := by
  intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
  rw [countP_rumpf]
  cases env with
  | cons n tail =>
    cases tail
    rcases n with ⟨n, lower, upper⟩
    have casesN : n = 0 ∨ n = 1 := by omega
    rcases casesN with zero | one
    · subst n
      simp [execEndHA, execStmtHA, execBlockHA, eval, Env.get, wahr?]
    · subst n
      intro bad
      have safe := noDescent 0 (A [] (A [] state))
        (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) target
      cases hr : R 0 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
      | why world reason => exact Fin.elim0 reason
      | _ => simp_all [execEndHA, execStmtHA, execBlockHA, massTor, Mass.wert,
          countM_mass, lexLt, eval, evalArgs, evalErg, Env.get, Expr.orte, Args.orte,
          leseA, World.lese, World.merke, wahr?, Zahl.weiter]

/-- Both functions of the mutual cycle carry the same singleton tuple. -/
theorem mutual_lengths_zeuge :
    ∀ f g, zykS mutualP [0, 1] f g = true → (mutualM.mass f).length = (mutualM.mass g).length :=
  cycleLengths_sound mutualU mutualP mutualM.mass cycleLengths_sound_zeuge

/-- Every function of the mutual cycle discharges the duty; both positive-entry calls pass `0`. -/
theorem mutual_duty_zeuge (passes : Nat) (Q : AxEns (declOf mutualU))
    (S : SperrInv (declOf mutualU)) (T : (declOf mutualU).Tab ⊕ (declOf mutualU).Glob → Prop)
    (f : (declOf mutualU).Fn) :
    MassPflicht mutualP passes Q S T mutualM.mass (zykS mutualP [0, 1]) f := by
  rcases f with ⟨index, bound⟩
  have casesF : index = 0 ∨ index = 1 := by change index < 2 at bound; omega
  rcases casesF with first | second <;> subst index
  · change MassPflicht mutualP passes Q S T mutualM.mass (zykS mutualP [0, 1]) 0
    intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
    rw [mutualP_rumpf_zero]
    cases env with
    | cons n tail =>
      cases tail
      rcases n with ⟨n, lower, upper⟩
      have casesN : n = 0 ∨ n = 1 := by omega
      rcases casesN with zero | one
      · subst n
        simp [execEndHA, execStmtHA, execBlockHA, eval, Env.get, wahr?]
      · subst n
        intro bad
        have safe := noDescent 1 (A [] (A [] state))
          (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) target
        cases hr : R 1 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
        | why world reason => exact Fin.elim0 reason
        | _ => simp_all [execEndHA, execStmtHA, execBlockHA, massTor, Mass.wert,
            mutualM_mass_zero, mutualM_mass_one, lexLt, eval, evalArgs, evalErg, Env.get,
            Expr.orte, Args.orte, leseA, World.lese, World.merke, wahr?, Zahl.weiter]
  · change MassPflicht mutualP passes Q S T mutualM.mass (zykS mutualP [0, 1]) 1
    intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
    rw [mutualP_rumpf_one]
    cases env with
    | cons n tail =>
      cases tail
      rcases n with ⟨n, lower, upper⟩
      have casesN : n = 0 ∨ n = 1 := by omega
      rcases casesN with zero | one
      · subst n
        simp [execEndHA, execStmtHA, execBlockHA, eval, Env.get, wahr?]
      · subst n
        intro bad
        have safe := noDescent 0 (A [] (A [] state))
          (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) target
        cases hr : R 0 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
        | why world reason => exact Fin.elim0 reason
        | _ => simp_all [execEndHA, execStmtHA, execBlockHA, massTor, Mass.wert,
            mutualM_mass_zero, mutualM_mass_one, lexLt, eval, evalArgs, evalErg, Env.get,
            Expr.orte, Args.orte, leseA, World.lese, World.merke, wahr?, Zahl.weiter]

/-- The first call of this cycle is not in tail position; both calls really decrease the measure. -/
theorem nonTail_duty_zeuge (passes : Nat) (Q : AxEns (declOf nonTail))
    (S : SperrInv (declOf nonTail)) (T : (declOf nonTail).Tab ⊕ (declOf nonTail).Glob → Prop) :
    MassPflicht nonTailP passes Q S T nonTailM.mass (zykS nonTailP [0]) 0 := by
  intro O _ _ _ U _ A _ R _ noDescent _ state env _ target _
  rw [nonTailP_rumpf]
  cases env with
  | cons n tail =>
    cases tail
    rcases n with ⟨n, lower, upper⟩
    have casesN : n = 0 ∨ n = 1 := by omega
    rcases casesN with zero | one
    · subst n
      simp [execEndHA, execStmtHA, execBlockHA, eval, Env.get, wahr?]
    · subst n
      intro bad
      have safe := noDescent 0 (A [] (A [] state))
        (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) target
      cases hr : R 0 (A [] (A [] state)) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
      | why world reason => exact Fin.elim0 reason
      | ok world value =>
        have safeNext := noDescent 0 (A [] world)
          (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) target
        cases hs : R 0 (A [] world) (.cons (⟨0, by decide, by decide⟩ : Zahl 0 1) .nil) with
        | why world' reason => exact Fin.elim0 reason
        | _ => simp_all [execEndHA, execStmtHA, execBlockHA, massTor, Mass.wert,
            nonTailM_mass, lexLt, eval, evalArgs, evalErg, Env.get, Expr.orte, Args.orte,
            leseA, World.lese, World.merke, wahr?, Zahl.weiter]
      | _ => simp_all [execEndHA, execStmtHA, execBlockHA, massTor, Mass.wert,
          nonTailM_mass, lexLt, eval, evalArgs, evalErg, Env.get, Expr.orte, Args.orte,
          leseA, World.lese, World.merke, wahr?, Zahl.weiter]

/-- Acyclic source functions reuse the existing vacuous-cycle theorem, with their real exported measure. -/
theorem acyclic_duty_zeuge (passes : Nat) (Q : AxEns (declOf acyclic))
    (S : SperrInv (declOf acyclic)) (T : (declOf acyclic).Tab ⊕ (declOf acyclic).Glob → Prop) :
    MassPflicht acyclicP passes Q S T acyclicM.mass (zykS acyclicP [0]) 0 :=
  massPflicht_ohne_zyklus acyclicP [0] passes Q S T acyclicM.mass 0 (by
    intro g
    have hg : g = 0 := Fin.fin_one_eq_zero g
    subst g
    have noCall : ruftB acyclicP 0 0 = false := by
      unfold ruftB
      rw [acyclicP_rumpf]
      rfl
    simp [zykS, noCall])

end Gabbro.Grammatik.Parser.Measures.Fixtures
