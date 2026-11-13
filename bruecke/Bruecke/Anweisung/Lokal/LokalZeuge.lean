module
public import Bruecke.Anweisung.Lokal.QuelleB
import Grammatik.Kern.Taktik.KernelRfl
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

/-!
# Witness: a function with `let`, `let mut` and an assignment, carried by the bridge

`step(p : 0..10) -> 0..20 { let a = p + 1; let mut b : 0..20 = a; b = a + 1; T[0].v = b;
return b; }` -- as the elaborated unit (a lowered-unit witness, not a measured source-parser
acceptance claim). The lowering accepts it, the decided per-unit checks hold (freshness of `a`
and `b` included), `zuBody` refuses it (it has binders), `zuBodyB` gives the expected Body
program, and its duty `meetsU` is proved: the premises of `laufB`/`bruecke_nutzerB` hold
together on a body that binds, rebinds and reads its locals.

(`b = b + 1;` as in the design note is refused by the lowering itself: `b + 1` has the range
`lo + 1 .. hi + 1` of a declared `lo .. hi`, which never fits back; the witness rebinds
`b = a + 1;`, which fits.)
-/

namespace Gabbro.Bruecke.LokalZeuge

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def tafel : UTab := { name := "T", count := 1, cols := [("v", (0, 20))] }

def routine : UFn :=
  { name := "step", params := [("p", .int 0 10)], kinds := [.int], res := some (0, 20),
    held := [], puts := ["T"], gives := [],
    body := [.bind "a" none (.add (.param "p") (.lit 1)),
      .bindMut "b" 0 20 (.param "a"),
      .setVar "b" (.add (.param "a") (.lit 1)),
      .assignTab "T" "v" (.lit 0) (.param "b")],
    ret := .val (.param "b") }

def unit : UProg := { tabs := [tafel], locks := [], fns := [routine] }

def koerper : List Gabbro.Body.Stmt :=
  [.bindName "a" (.bin .add (.name "p") (.lit (.int 1))),
   .bindName "b" (.name "a"),
   .bindName "b" (.bin .add (.name "a") (.lit (.int 1))),
   .assign "T" (.lit (.int 0)) "v" (.name "b"),
   .ret (some (.name "b"))]

/-! ## 1. The translation and the decided checks -/

/-- The translation threads the scope: every local reads as a Body name. -/
theorem zuBodyB_zeuge : zuBodyB unit routine = some koerper := by kernel_rfl

/-- The old translation refuses the body: it binds. -/
theorem zuBody_zeuge : zuBody unit routine = none := by kernel_rfl

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by decide +kernel

theorem checks_zeuge :
    nullB unit = true ∧ stimmigB unit = true ∧ bindFrischAllB unit = true ∧
      rangB unit (rangAuto unit) = true ∧ ohneTransitionB unit = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 2. The duty -/

theorem step_bind_ok (ρ : Gabbro.Body.Env) (x : String) (e : Gabbro.Body.Expr)
    (s : Gabbro.Body.State) (v : Gabbro.Body.Value) (h : Gabbro.Body.eval s e = some v) :
    Gabbro.Body.step ρ (.bindName x e) s = .running ⟨s.world, Gabbro.Body.bindLocal s.local' x v⟩ := by
  simp only [Gabbro.Body.step, h]

theorem step_assign_ok (ρ : Gabbro.Body.Env) (c : String) (i : Gabbro.Body.Expr) (f : String)
    (e : Gabbro.Body.Expr) (s : Gabbro.Body.State) (k : Int) (v : Gabbro.Body.Value)
    (hi : Gabbro.Body.eval s i = some (.int k)) (he : Gabbro.Body.eval s e = some v) :
    Gabbro.Body.step ρ (.assign c i f e) s =
      .running ⟨Gabbro.Body.store s.world (.slot c k f) v, s.local'⟩ := by
  simp only [Gabbro.Body.step, hi, he]

theorem exec_ret_ok (ρ : Gabbro.Body.Env) (e : Gabbro.Body.Expr) (s : Gabbro.Body.State)
    (v : Gabbro.Body.Value) (h : Gabbro.Body.eval s e = some v) :
    Gabbro.Body.exec ρ [.ret (some e)] s = .returned s (some v) := by
  simp only [Gabbro.Body.exec, Gabbro.Body.step, h]

theorem pre_eq : preExpr routine = .hasShape "p" (.intIn 0 10) := by kernel_rfl

theorem post_eq (s s' : Gabbro.Body.State) (r : Option Gabbro.Body.Value) :
    (postU unit (wfU unit) routine s s' r).getD False =
      (wfU unit s' ∧ ∃ x, r = some (.int x) ∧ (0 : Int) ≤ x ∧ x ≤ 20) := rfl

theorem shape_eq : shapeOfU unit (.slot "T" 0 "v") = some (.intIn 0 20) := by kernel_rfl

/-- **The duty of `step`, proved**: from `p ∈ 0..10` the body binds `a = p + 1`, `b = a`, rebinds
    `b = a + 1`, writes `T[0].v = b` and returns `b = p + 2 ∈ 0..20`; the world stays typed. -/
theorem routine_meets : meetsU unit (wfU unit) routine koerper := by
  intro ρ s hW hpre
  rw [pre_eq] at hpre
  have hp : (s.local' "p").hasShape (.intIn 0 10) = true := by
    simpa only [Gabbro.Body.eval, Option.some.injEq, Gabbro.Body.Value.bool.injEq] using hpre
  show ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ koerper s) = some s' ∧
    (postU unit (wfU unit) routine s s' (Gabbro.Body.finalValue (Gabbro.Body.exec ρ koerper s))).getD False
  cases hv : s.local' "p" with
  | int n =>
    rw [hv] at hp
    have hn : 0 ≤ n ∧ n ≤ 10 := by simpa using hp
    have e1 := step_bind_ok ρ "a" (.bin .add (.name "p") (.lit (.int 1))) s (.int (n + 1))
      (by
        show Gabbro.Body.binop .add (s.local' "p") (.int 1) = _
        rw [hv]
        try rfl)
    have e2 := step_bind_ok ρ "b" (.name "a")
      ⟨s.world, Gabbro.Body.bindLocal s.local' "a" (.int (n + 1))⟩ (.int (n + 1))
      (by
        show some (Gabbro.Body.bindLocal s.local' "a" (.int (n + 1)) "a") = _
        rw [Gabbro.Body.bindLocal_here])
    have e3 := step_bind_ok ρ "b" (.bin .add (.name "a") (.lit (.int 1)))
      ⟨s.world, Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "a" (.int (n + 1))) "b"
        (.int (n + 1))⟩ (.int (n + 1 + 1))
      (by
        show Gabbro.Body.binop .add (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "a"
          (.int (n + 1))) "b" (.int (n + 1)) "a") (.int 1) = _
        rw [Gabbro.Body.bindLocal_elsewhere _ _ _ _ (by decide : ("a" : String) ≠ "b"),
          Gabbro.Body.bindLocal_here]
        try rfl)
    have e4 := step_assign_ok ρ "T" (.lit (.int 0)) "v" (.name "b")
      ⟨s.world, Gabbro.Body.bindLocal (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "a"
        (.int (n + 1))) "b" (.int (n + 1))) "b" (.int (n + 1 + 1))⟩ 0 (.int (n + 1 + 1)) rfl
      (by simp [Gabbro.Body.eval, Gabbro.Body.bindLocal_here])
    have e5 := exec_ret_ok ρ (.name "b")
      ⟨Gabbro.Body.store s.world (.slot "T" 0 "v") (.int (n + 1 + 1)),
        Gabbro.Body.bindLocal (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "a"
          (.int (n + 1))) "b" (.int (n + 1))) "b" (.int (n + 1 + 1))⟩ (.int (n + 1 + 1))
      (by simp [Gabbro.Body.eval, Gabbro.Body.bindLocal_here])
    unfold koerper
    rw [exec_cons_running ρ _ _ _ _ e1, exec_cons_running ρ _ _ _ _ e2,
      exec_cons_running ρ _ _ _ _ e3, exec_cons_running ρ _ _ _ _ e4, e5]
    refine ⟨_, rfl, ?_⟩
    rw [post_eq]
    refine ⟨?_, n + 1 + 1, rfl, by omega, by omega⟩
    show Gabbro.Body.WF (shapeOfU unit)
      (Gabbro.Body.store s.world (.slot "T" 0 "v") (.int (n + 1 + 1)))
    apply Gabbro.Body.WF_store _ _ _ _ hW
    intro sh hsh
    rw [shape_eq] at hsh
    cases hsh
    simp only [Gabbro.Body.Value.hasShape_int_intIn, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩
  | _ =>
    rw [hv] at hp
    simp at hp

/-! ## 3. Together -/

/-- **The premises of the bridge for bodies with local bindings hold together**: the unit
    lowers, passes every decided check, is refused by `zuBody` and carried by `zuBodyB`, and every
    function's duty over `zuBodyB` is proved. -/
theorem lokal_zeuge :
    (lowerAllg unit).toOption.isSome = true ∧ nullB unit = true ∧ stimmigB unit = true ∧
      bindFrischAllB unit = true ∧ rangB unit (rangAuto unit) = true ∧
      ohneTransitionB unit = true ∧ zuBody unit routine = none ∧
      ∀ c : Fin unit.fns.length, ∃ body, zuBodyB unit (fnAt unit c) = some body ∧
        meetsU unit (wfU unit) (fnAt unit c) body := by
  refine ⟨lowered_some, checks_zeuge.1, checks_zeuge.2.1, checks_zeuge.2.2.1,
    checks_zeuge.2.2.2.1, checks_zeuge.2.2.2.2, zuBody_zeuge, fun c => ?_⟩
  have hc : c = ⟨0, by decide⟩ := Fin.ext (by
    have := c.isLt
    change c.val < 1 at this
    show c.val = 0
    omega)
  subst hc
  exact ⟨koerper, zuBodyB_zeuge, routine_meets⟩

end Gabbro.Bruecke.LokalZeuge
