module
public import Bruecke.Anweisung.Zweig.Benannt
public import Bruecke.Anweisung.Lokal.Werte
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.String.Length
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.Repr
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
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

/-!
# Numeric shadowing across a branch

The whole function binds `x = 1`, shadows it with `x = 0` in the taken branch and
returns the outer `x`. The positional relation retains both entries while the branch
runs. This witnesses the new reader and relation, not yet the carried-chain premises.
-/

namespace Gabbro.Bruecke.SchattenZeuge

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

def routine : UFn :=
  { name := "shadow", params := [], kinds := [], res := some (0, 1),
    held := [], puts := [], gives := [],
    body := [.bindMut "x" 0 1 (.lit 1), .ifBeg .tru,
      .bind "x" (some (0, 0)) (.lit 0), .ifElse, .blkEnd],
    ret := .val (.param "x") }

def unit : UProg := { tabs := [], locks := [], fns := [routine] }

def body : List Gabbro.Body.Stmt :=
  [.bindName "x" (.lit (.int 1)),
    .ite (.lit (.bool true)) [.bindName "x##" (.lit (.int 0))] [],
    .ret (some (.name "x"))]

/-- The source scope and the positional reader agree on the enclosing scope after the branch. -/
theorem translation_zeuge :
    namedBody unit (routine.body.length + 1) routine (BodyNames.start routine)
      routine.body routine.ret = some body := by
  kernel_rfl

def after (s : Gabbro.Body.State) : Gabbro.Body.State :=
  ⟨s.world, Gabbro.Body.bindLocal
    (Gabbro.Body.bindLocal s.local' "x" (.int 1)) "x##" (.int 0)⟩

/-- The inner value remains in its own Body identifier; the returned value is the outer one. -/
theorem return_zeuge (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) :
    Gabbro.Body.exec ρB body s = .returned (after s) (some (.int 1)) := by
  have hne : ("x" : String) ≠ "x##" := by decide
  simp only [body, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
    Gabbro.Body.bindLocal_elsewhere _ _ _ _ hne, Gabbro.Body.bindLocal_here, after]

theorem lowered_some_zeuge : (lowerAllg unit).toOption.isSome = true := by
  decide +kernel

/-- The Body duty is proved for all initial states and all callee environments. -/
theorem routine_meets_zeuge : meetsU unit (wfU unit) routine body := by
  intro ρB s hW _
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some s' ∧
    (postU unit (wfU unit) routine s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB body s))).getD False
  rw [return_zeuge ρB s]
  refine ⟨after s, rfl, ?_⟩
  change wfU unit (after s) ∧ ∃ n : Int,
    some (Gabbro.Body.Value.int 1) = some (.int n) ∧ 0 ≤ n ∧ n ≤ 1
  exact ⟨hW, 1, rfl, by decide, by decide⟩

def one : Wert (declOf unit) (.int 0 1) := ⟨1, by decide, by decide⟩

def zero : Wert (declOf unit) (.int 0 0) := ⟨0, by decide, by decide⟩

/-- Both related values coexist; tail restores the outer relation without a freshness premise
    on the source name. This is the case the first-match relation could not express. -/
theorem relation_zeuge (β : Gabbro.Body.Binding) :
    PositionalLRel (routine.mitBindung "x" (0, 1)) ["x"] 0
      (Env.cons one Env.nil)
      (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal β "x" (.int 1)) "x##" (.int 0)) := by
  have h0 : PositionalLRel routine [] 0 (Env.nil : Env (declOf unit) []) β := by
    refine ⟨rfl, List.Pairwise.nil, ?_⟩
    intro j id hj
    cases hj
  have h1 := h0.push "x" "x" (0, 1) (by decide) one
  have h2 := h1.push "x" "x##" (0, 0) (by decide) zero
  exact h2.tail

/-- Translation, execution and the nonvacuous positional relation hold on the same fixture. -/
theorem shadowing_zeuge (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) :
    (lowerAllg unit).toOption.isSome = true ∧
      namedBody unit (routine.body.length + 1) routine (BodyNames.start routine)
        routine.body routine.ret = some body ∧
      meetsU unit (wfU unit) routine body ∧
      Gabbro.Body.exec ρB body s = .returned (after s) (some (.int 1)) ∧
      PositionalLRel (routine.mitBindung "x" (0, 1)) ["x"] 0
        (Env.cons one Env.nil) (after s).local' :=
  ⟨lowered_some_zeuge, translation_zeuge, routine_meets_zeuge,
    return_zeuge ρB s, relation_zeuge s.local'⟩

end Gabbro.Bruecke.SchattenZeuge
