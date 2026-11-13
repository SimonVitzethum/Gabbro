module

public import Bruecke.Ausdruck.Teil3
public import Bruecke.Anweisung.Zweig.Uebersetzung
import Grammatik.Kern.Taktik.KernelRfl

@[expose] public section

/-! # Comparison operators and arithmetic operands in the shared bridge reader -/

namespace Gabbro.Bruecke.VergleichZeuge

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

def routine : UFn :=
  { name := "compare", params := [("k", .int 0 9)], kinds := [.int], res := none,
    held := [], puts := [], gives := [], body := [], ret := .empty }

def arithmeticRoutine : UFn :=
  { routine with
    name := "compareArithmetic", params := [("a", .int 0 9), ("n", .int 0 9)],
    kinds := [.int, .int] }

def unit : UProg := { tabs := [], locks := [], fns := [routine, arithmeticRoutine] }

/-- Body has these operators directly, so the source operand order stays unchanged. -/
theorem ensExpr_ge_zeuge :
    ensExpr unit routine {} (.cmp ">=" (.param "k") (.lit 1)) =
      some (.bin .ge (.name "k") (.lit (.int 1)), {}) := by kernel_rfl

theorem ensExpr_gt_zeuge :
    ensExpr unit routine {} (.cmp ">" (.param "k") (.lit 0)) =
      some (.bin .gt (.name "k") (.lit (.int 0)), {}) := by kernel_rfl

theorem ensExpr_ne_zeuge :
    ensExpr unit routine {} (.cmp "!=" (.param "k") (.lit 3)) =
      some (.bin .ne (.name "k") (.lit (.int 3)), {}) := by kernel_rfl

/-- The same operand reader serves comparisons in promises and branch conditions. -/
theorem ensExpr_add_zeuge :
    ensExpr unit arithmeticRoutine {} (.cmp "<" (.add (.param "a") (.lit 1)) (.param "n")) =
      some (.bin .lt (.bin .add (.name "a") (.lit (.int 1))) (.name "n"), {}) := by kernel_rfl

theorem condZ_add_zeuge :
    condZ unit arithmeticRoutine (.cmp "<" (.add (.param "a") (.lit 1)) (.param "n")) =
      some (.bin .lt (.bin .add (.name "a") (.lit (.int 1))) (.name "n")) := by kernel_rfl

theorem ensExpr_sub_mul_zeuge :
    ensExpr unit arithmeticRoutine {}
      (.cmp ">=" (.sub (.param "a") (.lit 1)) (.mul (.param "n") (.lit 2))) =
      some (.bin .ge (.bin .sub (.name "a") (.lit (.int 1)))
        (.bin .mul (.name "n") (.lit (.int 2))), {}) := by kernel_rfl

/-- Scalar arithmetic leaves an existing accumulator untouched. -/
theorem ensSide_arithmetic_acc_zeuge :
    ensSide unit arithmeticRoutine { olds := [.lit (.int 7)], result := true }
      (.add (.param "a") (.lit 1)) =
      some (.bin .add (.name "a") (.lit (.int 1)),
        { olds := [.lit (.int 7)], result := true }) := by kernel_rfl

/-- Nested entry/result reads still need an accumulator-aware arithmetic translation. -/
theorem ensSide_nested_refused_zeuge :
    ensSide unit routine {} (.add .erg (.lit 1)) = none ∧
    ensSide unit routine {} (.add (.old "p" "v" (.lit 0)) (.lit 1)) = none :=
  ⟨by kernel_rfl, by kernel_rfl⟩

def initial : World (declOf unit) where
  slots := fun t => nomatch t
  globs := fun g => nomatch g
  spur := []

def environment : Env (declOf unit) [.int 0 9] :=
  .cons ⟨2, by decide, by decide⟩ .nil

def binding : Gabbro.Body.Binding := fun _ => .int 2

def state : Gabbro.Body.State := ⟨enc unit initial (fun _ => .absent), binding⟩

def geTerm : Expr (declOf unit) [.int 0 9] [] .bool :=
  .le (.lit 1) (.var .here)

/-- G swaps the comparison terms; Body retains the original operand order. -/
theorem lowEns_ge_zeuge :
    lowEns unit [.int 0 9] [] routine none (.cmp ">=" (.param "k") (.lit 1)) =
      .ok geTerm := by kernel_rfl

/-- Arithmetic comparison operands also use the ordinary G comparison lowering. -/
theorem lowEns_add_zeuge :
    lowEns unit [.int 0 9, .int 0 9] [] arithmeticRoutine none
      (.cmp "<" (.add (.param "a") (.lit 1)) (.param "n")) =
      .ok (Expr.lt (Expr.add (Expr.var .here) (Expr.lit 1))
        (Expr.var (.there .here))) := by kernel_rfl

/-- A closed instance of the simulation conclusion: `k = 2` makes `k >= 1` true. -/
theorem lowEns_sim_ge_zeuge :
    Gabbro.Body.eval state (.bin .ge (.name "k") (.lit (.int 1))) =
      some (.bool (wahr? (eval initial geTerm initial environment))) := by kernel_rfl

end Gabbro.Bruecke.VergleichZeuge
