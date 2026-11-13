module
public import Bruecke.Anweisung.Zweig.Quelle
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
# Witness: a function that branches, carried by the bridge

`pick(k : 0..9) -> 0..9 { if k == 0 { return 0; } if k < 5 { T[0].v = k; } else { T[0].v = 5; }
T[1].v = k; return k; }` -- as the elaborated unit with narrowing off (`uCondPlain`: `ifBeg c`,
the then-statements with their ender, `ifElse`, the else-statements, `blkEnd`; a lowered-unit
witness, not a measured source-parser acceptance claim). The lowering accepts it, the decided
per-unit checks hold, `zuBodyB` refuses it (it branches), `zuBodyZ` gives the expected Body
program -- an early `return` inside a branch with an empty `else`, a non-terminal `if/else`
whose arms write a slot, a slot write after it -- and its duty `meetsU` is proved: the premises
of `laufZ`/`bruecke_nutzerZ` hold together on a body that branches.
-/

namespace Gabbro.Bruecke.ZweigZeuge

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def tafel : UTab := { name := "T", count := 2, cols := [("v", (0, 9))] }

def routine : UFn :=
  { name := "pick", params := [("k", .int 0 9)], kinds := [.int], res := some (0, 9),
    held := [], puts := ["T"], gives := [],
    body := [.ifBeg (.cmp "==" (.param "k") (.lit 0)), .ret (.val (.lit 0)), .ifElse, .blkEnd,
      .ifBeg (.cmp "<" (.param "k") (.lit 5)), .assignTab "T" "v" (.lit 0) (.param "k"),
      .ifElse, .assignTab "T" "v" (.lit 0) (.lit 5), .blkEnd,
      .assignTab "T" "v" (.lit 1) (.param "k")],
    ret := .val (.param "k") }

def unit : UProg := { tabs := [tafel], locks := [], fns := [routine] }

def koerper : List Gabbro.Body.Stmt :=
  [.ite (.bin .eq (.name "k") (.lit (.int 0))) [.ret (some (.lit (.int 0)))] [],
   .ite (.bin .lt (.name "k") (.lit (.int 5))) [.assign "T" (.lit (.int 0)) "v" (.name "k")]
     [.assign "T" (.lit (.int 0)) "v" (.lit (.int 5))],
   .assign "T" (.lit (.int 1)) "v" (.name "k"),
   .ret (some (.name "k"))]

/-! ## 1. The translation and the decided checks -/

/-- The translation reads both conditionals as Body `ite`, the early return as `ret`. -/
theorem zuBodyZ_zeuge : zuBodyZ unit routine = some koerper := by kernel_rfl

/-- The translation without conditionals refuses the body: it branches. -/
theorem zuBodyB_zeuge : zuBodyB unit routine = none := by kernel_rfl

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by decide +kernel

theorem checks_zeuge :
    nullB unit = true ∧ stimmigB unit = true ∧ bindFrischAllB unit = true ∧
      rangB unit (rangAuto unit) = true ∧ ohneTransitionB unit = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 2. The duty -/

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

theorem exec_halt (ρ : Gabbro.Body.Env) (x : Gabbro.Body.Stmt) (xs : List Gabbro.Body.Stmt)
    (s s' : Gabbro.Body.State) (v : Option Gabbro.Body.Value)
    (h : Gabbro.Body.step ρ x s = .returned s' v) :
    Gabbro.Body.exec ρ (x :: xs) s = .returned s' v := by
  simp only [Gabbro.Body.exec, h]

theorem pre_eq : preExpr routine = .hasShape "k" (.intIn 0 9) := by kernel_rfl

theorem post_eq (s s' : Gabbro.Body.State) (r : Option Gabbro.Body.Value) :
    (postU unit (wfU unit) routine s s' r).getD False =
      (wfU unit s' ∧ ∃ x, r = some (.int x) ∧ (0 : Int) ≤ x ∧ x ≤ 9) := rfl

theorem shape0 : shapeOfU unit (.slot "T" 0 "v") = some (.intIn 0 9) := by kernel_rfl

theorem shape1 : shapeOfU unit (.slot "T" 1 "v") = some (.intIn 0 9) := by kernel_rfl

/-- **The duty of `pick`, proved**: from `k ∈ 0..9`, `k = 0` returns `0` at once; otherwise the
    conditional writes `T[0].v = k` (for `k < 5`) or `5`, the body writes `T[1].v = k` and returns
    `k ∈ 0..9`; the world stays typed. -/
theorem routine_meets : meetsU unit (wfU unit) routine koerper := by
  intro ρ s hW hpre
  rw [pre_eq] at hpre
  have hp : (s.local' "k").hasShape (.intIn 0 9) = true := by
    simpa only [Gabbro.Body.eval, Option.some.injEq, Gabbro.Body.Value.bool.injEq] using hpre
  show ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρ koerper s) = some s' ∧
    (postU unit (wfU unit) routine s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρ koerper s))).getD False
  cases hv : s.local' "k" with
  | int n =>
    rw [hv] at hp
    have hn : 0 ≤ n ∧ n ≤ 9 := by simpa using hp
    by_cases h0 : n = 0
    · subst h0
      have hc : Gabbro.Body.eval s (.bin .eq (.name "k") (.lit (.int 0))) = some (.bool true) := by
        simp [Gabbro.Body.eval, Gabbro.Body.binop, hv]
      have e1 : Gabbro.Body.step ρ (.ite (.bin .eq (.name "k") (.lit (.int 0)))
          [.ret (some (.lit (.int 0)))] []) s = .returned s (some (.int 0)) := by
        rw [step_ite_wahr ρ hc]
        exact exec_ret_ok ρ _ s _ rfl
      unfold koerper
      rw [exec_halt ρ _ _ _ _ _ e1]
      refine ⟨_, rfl, ?_⟩
      rw [post_eq]
      exact ⟨hW, 0, rfl, by omega, by omega⟩
    · have hc : Gabbro.Body.eval s (.bin .eq (.name "k") (.lit (.int 0))) = some (.bool false) := by
        simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, h0]
      have e1 : Gabbro.Body.step ρ (.ite (.bin .eq (.name "k") (.lit (.int 0)))
          [.ret (some (.lit (.int 0)))] []) s = .running s := by
        simp only [step_ite_falsch ρ hc, Gabbro.Body.exec]
      obtain ⟨w, hw0, hw9, e2⟩ : ∃ w : Int, 0 ≤ w ∧ w ≤ 9 ∧
          Gabbro.Body.step ρ (.ite (.bin .lt (.name "k") (.lit (.int 5)))
            [.assign "T" (.lit (.int 0)) "v" (.name "k")]
            [.assign "T" (.lit (.int 0)) "v" (.lit (.int 5))]) s =
          .running ⟨Gabbro.Body.store s.world (.slot "T" 0 "v") (.int w), s.local'⟩ := by
        by_cases h5 : n < 5
        · have hc2 : Gabbro.Body.eval s (.bin .lt (.name "k") (.lit (.int 5))) =
              some (.bool true) := by
            simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, h5]
          refine ⟨n, hn.1, hn.2, ?_⟩
          simp only [step_ite_wahr ρ hc2, Gabbro.Body.exec,
            step_assign_ok ρ "T" (.lit (.int 0)) "v" (.name "k") s 0 (.int n) rfl
              (by simp [Gabbro.Body.eval, hv])]
        · have hc2 : Gabbro.Body.eval s (.bin .lt (.name "k") (.lit (.int 5))) =
              some (.bool false) := by
            simp [Gabbro.Body.eval, Gabbro.Body.binop, hv, h5]
          refine ⟨5, by omega, by omega, ?_⟩
          simp only [step_ite_falsch ρ hc2, Gabbro.Body.exec,
            step_assign_ok ρ "T" (.lit (.int 0)) "v" (.lit (.int 5)) s 0 (.int 5) rfl rfl]
      have e3 := step_assign_ok ρ "T" (.lit (.int 1)) "v" (.name "k")
        ⟨Gabbro.Body.store s.world (.slot "T" 0 "v") (.int w), s.local'⟩ 1 (.int n) rfl
        (by simp [Gabbro.Body.eval, hv])
      have e4 := exec_ret_ok ρ (.name "k")
        ⟨Gabbro.Body.store (Gabbro.Body.store s.world (.slot "T" 0 "v") (.int w))
          (.slot "T" 1 "v") (.int n), s.local'⟩ (.int n)
        (by simp [Gabbro.Body.eval, hv])
      unfold koerper
      rw [exec_cons_running ρ _ _ _ _ e1, exec_cons_running ρ _ _ _ _ e2,
        exec_cons_running ρ _ _ _ _ e3, e4]
      refine ⟨_, rfl, ?_⟩
      rw [post_eq]
      refine ⟨?_, n, rfl, hn.1, hn.2⟩
      show Gabbro.Body.WF (shapeOfU unit) (Gabbro.Body.store
        (Gabbro.Body.store s.world (.slot "T" 0 "v") (.int w)) (.slot "T" 1 "v") (.int n))
      refine Gabbro.Body.WF_store _ _ _ _ (Gabbro.Body.WF_store _ _ _ _ hW ?_) ?_
      · intro sh hsh
        rw [shape0] at hsh
        cases hsh
        simp only [Gabbro.Body.Value.hasShape_int_intIn, decide_eq_true_eq]
        exact ⟨hw0, hw9⟩
      · intro sh hsh
        rw [shape1] at hsh
        cases hsh
        simp only [Gabbro.Body.Value.hasShape_int_intIn, decide_eq_true_eq]
        exact ⟨hn.1, hn.2⟩
  | _ =>
    rw [hv] at hp
    simp at hp

/-! ## 3. Together -/

/-- **The premises of the bridge for bodies with conditionals hold together**: the unit lowers,
    passes every decided check, is refused by `zuBodyB` and carried by `zuBodyZ`, and every
    function's duty over `zuBodyZ` is proved. -/
theorem zweig_zeuge :
    (lowerAllg unit).toOption.isSome = true ∧ nullB unit = true ∧ stimmigB unit = true ∧
      bindFrischAllB unit = true ∧ rangB unit (rangAuto unit) = true ∧
      ohneTransitionB unit = true ∧ zuBodyB unit routine = none ∧
      ∀ c : Fin unit.fns.length, ∃ body, zuBodyZ unit (fnAt unit c) = some body ∧
        meetsU unit (wfU unit) (fnAt unit c) body := by
  refine ⟨lowered_some, checks_zeuge.1, checks_zeuge.2.1, checks_zeuge.2.2.1,
    checks_zeuge.2.2.2.1, checks_zeuge.2.2.2.2, zuBodyB_zeuge, fun c => ?_⟩
  have hc : c = ⟨0, by decide⟩ := Fin.ext (by
    have := c.isLt
    change c.val < 1 at this
    show c.val = 0
    omega)
  subst hc
  exact ⟨koerper, zuBodyZ_zeuge, routine_meets⟩

end Gabbro.Bruecke.ZweigZeuge
