module

public import Bruecke.Ausdruck.Glob
import Grammatik.Kern.Taktik.KernelRfl

@[expose] public section

/-! # Nonzero numeric-static witnesses for the bridge scaffolding -/

namespace Gabbro.Bruecke.GlobZeuge

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- One numeric static, initially seven, with no guard or table. -/
def unit : UProg :=
  { tabs := [], locks := [], fns := [],
    globs := [{ name := "counter", ty := .int 0 10, init := 7 }] }

def initial : World (declOf unit) where
  slots := fun t => nomatch t
  globs := fun ⟨n, hn⟩ => by
    cases n with
    | zero => exact ⟨7, by decide, by decide⟩
    | succ n =>
      have impossible : n + 1 < 1 := hn
      omega
  spur := []

/-- The base contains no number, so encoding seven is an observable overwrite. -/
def base : Gabbro.Body.World := fun _ => .absent

/-- The declaration, its nonzero initial value and both relations hold jointly. -/
theorem grel_encG_zeuge :
    unit.globs.length = 1 ∧ (globAt unit ⟨0, by decide⟩).init = 7 ∧
    globWert unit initial "counter" = some (.int 7) ∧
    encG unit initial base (.global "counter") = .int 7 ∧
    GRel unit initial (encG unit initial base) ∧
    WRel unit initial (encG unit initial base) :=
  ⟨by decide, by decide, by decide +kernel, by kernel_rfl,
    grel_encG unit initial base, wrel_encG unit initial base⟩

/-- The joint relation holds for the same nonzero static encoding. -/
theorem wgrel_encG_zeuge : WGRel unit initial (encG unit initial base) :=
  wgrel_enc unit initial base

/-- The concrete lowered read used by the simulation witness. -/
def read : LowSide unit [] [] :=
  { range := (0, 10), term := Expr.glob (D := declOf unit) (⟨0, by decide⟩ : Fin unit.globs.length) (by
      intro guard hg
      change guard ∈ [] at hg
      cases hg) }

/-- The numeric read really lowers and simulates under the nonempty global relation. -/
theorem lowGlobRead_sim_zeuge :
    lowGlobSide unit [] [] "counter" = .ok read ∧
    GRel unit initial (encG unit initial base) ∧
    Gabbro.Body.eval ⟨encG unit initial base, fun _ => .absent⟩ (.global "counter") =
      some (valOf (.int read.range.1 read.range.2)
        (eval initial read.term initial Env.nil)) ∧
    valOf (.int read.range.1 read.range.2) (eval initial read.term initial Env.nil) = .int 7 :=
  ⟨by kernel_rfl, grel_encG unit initial base,
    lowGlobRead_sim (g := "counter") (ls := read) (by kernel_rfl)
      initial initial Env.nil (encG unit initial base)
      (fun _ => .absent) (grel_encG unit initial base), by kernel_rfl⟩

/-- A numeric global contributes its range to the extended typing. -/
theorem shapeOfUG_zeuge :
    shapeOfUG unit (.global "counter") = some (.intIn 0 10) ∧
    Gabbro.Body.WF (shapeOfUG unit) (encG unit initial base) := by
  refine ⟨by decide +kernel, wf_of_wrel_grel unit ?_
    (wrel_encG unit initial base) (grel_encG unit initial base)⟩
  intro t
  exact Fin.elim0 t

/-- A function datum is needed only for the old reader's numeric-parameter decision. -/
def routine : UFn :=
  { name := "read", params := [], kinds := [], res := none, held := [], puts := [],
    gives := [], body := [], ret := .empty }

/-- Statics are read recursively inside arithmetic; old successful arithmetic is preserved. -/
theorem sideExprG_zeuge :
    sideExprG unit routine (.add (.glob "counter") (.conv 0 10 (.lit 2))) =
      some (.bin .add (.global "counter") (.lit (.int 2))) ∧
    sideExpr unit routine (.add (.lit 1) (.lit 2)) =
      some (.bin .add (.lit (.int 1)) (.lit (.int 2))) ∧
    sideExprG unit routine (.add (.lit 1) (.lit 2)) =
      some (.bin .add (.lit (.int 1)) (.lit (.int 2))) :=
  ⟨by kernel_rfl, by kernel_rfl, sideExprG_of_sideExpr unit routine _ _ (by kernel_rfl)⟩

/-- Boolean and aggregate declarations do not acquire numeric bridge shapes or values. -/
theorem glob_nonnumeric_zeuge :
    let unsupported : UProg := { unit with globs := [
      { name := "flag", ty := .bool, init := 1 },
      { name := "array", ty := .wert (.arr (.int 0 10) 1), init := 0 }] }
    globShape unsupported "flag" = none ∧ globShape unsupported "array" = none ∧
    ∀ σ : World (declOf unsupported),
      globWert unsupported σ "flag" = none ∧ globWert unsupported σ "array" = none := by
  refine ⟨by kernel_rfl, by kernel_rfl, ?_⟩
  intro σ
  exact ⟨by kernel_rfl, by kernel_rfl⟩

end Gabbro.Bruecke.GlobZeuge
