module

public import Grammatik.Parser.Elab.UebersetzeAllg.Eingebaut
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg.Eingebaut
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
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

@[expose] public section

/-
  C13: the lowering of `count x in D : p` as a number (`lowSeiteZ`) and its facts.

  Generic facts: the value of `Expr.count n body` is the count fold over the index domain `0 ..< n`
  (`eval_count`), and the domain has exactly `n` elements (`alleIndizes_length`), so the result lies in `0 .. n`
  (`zaehleVon_bereich`, the range the lowering carries). Fixtures (`_zeuge`) on concrete units: the cardinality the
  lowering carries for each domain (`slots of` a table of 4 slots, `descendants of` / `ancestors of` on a tree of 3,
  `elems of` an array of 2), a comparison with a count under `+`, and the refusals (an open table has no static
  cardinality). Fixtures use the canonical lowering equations.
-/

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

namespace ZaehleZeuge

/-- The value of a count is the count fold over the index domain: the bound `0 .. n` is in its type. -/
theorem eval_count {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} (n : Nat)
    (body : Expr D (Ty.index (n : Int) :: Γ) Λ .bool) (σ₀ σ : World D) (ρ : Env D Γ) :
    eval σ₀ (Expr.count n body) σ ρ = zaehleWahr n (fun k => wahr? (eval σ₀ body σ (.cons k ρ))) := rfl

/-- A lowered count carries the range `0 .. n`, `n` the cardinality of its domain. -/
theorem zaehleVon_bereich (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (n : Nat)
    (body : Expr (declOf u) (Ty.index (n : Int) :: Γ) Λ .bool) :
    (LowSide.zaehleVon u Γ Λ n body).range = (0, (n : Int)) := rfl

/-- The count never exceeds the domain: `count ≤ n`, from the type of the fold. -/
theorem zaehle_le_domain {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} (n : Nat)
    (body : Expr D (Ty.index (n : Int) :: Γ) Λ .bool) (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (Expr.count n body) σ ρ).n ≤ (n : Int) :=
  (eval σ₀ (Expr.count n body) σ ρ).le_hi

/-- The domain `0 ..< n` has exactly `n` elements: no element is lost and none is invented. -/
theorem domain_exakt (n : Nat) : (alleIndizes (n : Int)).length = n := alleIndizes_length n

/-! ## Fixtures -/

-- Keep the complete typed mutual result intact until its success/range is
-- projected. The ordinary lowerers retain every access and range check.
attribute [local cbv_eval] lowWertE.eq_def lowCmp.eq_def lowEns.eq_def
  lowArrayValue.eq_def lowSeiteZ.eq_def

/-- A table of four slots with a byte field. -/
def zU : UProg := {tabs := [{name := "T", count := 4, cols := [("v", (0, 255))]}], locks := [], fns := []}

def zF : UFn := {name := "sample", params := [], kinds := [], res := none, held := [], puts := [], gives := [], body := [], ret := .empty}

/-- The predicate `T.slots[x].v > 10` over the binder `x`. -/
def zBody : UEns := .cmp ">" (.tab "T" "v" (.param "x")) (.lit 10)

/-- A count predicate cannot read a slot at the exclusive domain bound. -/
theorem count_domain_bound_refused_zeuge :
    (lowSeiteZ zU [] [] zF none
      (.zaehle "T" "x" (.cmp ">" (.tab "T" "v" (.lit 4)) (.lit 10)))).toOption.isSome = false := by cbv

/-- The count over the slots of a table of four carries the range `0 .. 4`. -/
theorem zaehle_slots_lower_zeuge :
    (lowSeiteZ zU [] [] zF none (.zaehle "T" "x" zBody)).toOption.map (·.range) = some (0, 4) := by cbv

/-- A comparison with a count, and with a count under `+`, lowers. -/
theorem zaehle_vergleich_lower_zeuge :
    (lowEns zU [] [] zF none (.cmp "==" (.zaehle "T" "x" zBody) (.lit 2))).toOption.isSome = true ∧
    (lowEns zU [] [] zF none (.cmp "<=" (.add (.zaehle "T" "x" zBody) (.lit 1)) (.lit 5))).toOption.isSome = true := by
  cbv

/-- A table with a different count has the count's own cardinality (no shared constant). -/
theorem zaehle_slots_andere_anzahl_zeuge :
    (lowSeiteZ { zU with tabs := [{name := "T", count := 7, cols := [("v", (0, 255))]}] } [] [] zF none
      (.zaehle "T" "x" zBody)).toOption.map (·.range) = some (0, 7) := by cbv

/-- An OPEN table has no static cardinality: refused. -/
theorem zaehle_offen_abgelehnt_zeuge :
    lowSeiteZ { zU with tabs := [{name := "T", count := 0, cols := [("v", (0, 255))], von := some "provider"}] }
      [] [] zF none (.zaehle "T" "x" zBody) =
        .error "count over an open table has no static cardinality" := by cbv

/-- The tree domains: a tree of three slots, the seed an index parameter. -/
def bU : UProg := {tabs := [{name := "T", count := 3, cols := [("next", (0, 0))], opts := [("next", 0)], kanten := [("child", "next")]}], locks := [], fns := []}

def bF : UFn := {name := "sample", params := [("root", .index 3)], kinds := [.index 0], res := none, held := [], puts := [], gives := [], body := [], ret := .empty}

theorem zaehle_baum_lower_zeuge :
    (lowSeiteZ bU [.index 3] [] bF none (.zaehleBaum "T" "x" "next" false (.param "root") .tru)).toOption.map
        (·.range) = some (0, 3) ∧
    (lowSeiteZ bU [.index 3] [] bF none (.zaehleBaum "T" "x" "next" true (.param "root") .tru)).toOption.map
        (·.range) = some (0, 3) := by
  cbv
  exact ⟨rfl, rfl⟩

/-- The array domain: an array of two elements, the carrier of length two. -/
def aU : UProg := {tabs := [{name := "#array-elements:2", count := 2, cols := []}], locks := [], fns := []}

def aF : UFn := {name := "sample", params := [("data", .arr (.int 0 255) 2)], kinds := [.wert], res := none, held := [], puts := [], gives := [], body := [], ret := .empty}

theorem zaehle_feld_lower_zeuge :
    (lowSeiteZ aU [.arr (.int 0 255) 2] [] aF none
      (.zaehleFeld (.param "data") "i" (.cmp "==" (.idx (.param "data") (.param "i")) (.lit 1)))).toOption.map
        (·.range) = some (0, 2) := by cbv

end ZaehleZeuge

end Gabbro.Grammatik.Parser.UebersetzeAllg
