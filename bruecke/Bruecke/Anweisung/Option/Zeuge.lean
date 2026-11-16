module
public import Bruecke.Kette.Quelle
public import Grammatik.Parser.Stmt.LibraryFixtureProofs
public import Bruecke.Anweisung.Option.Kopf
public import Bruecke.Anweisung.Option.Werte
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
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
@[expose] public section

/-! # Joint option-value witnesses, separate from the compiler path -/
namespace Gabbro.Bruecke.OptionValueZeuge
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

attribute [local cbv_eval] lowEns.eq_def lowWertE.eq_def

/-- Both source branches update the same option local; the present branch also binds
    a block-local option. The function returns the resulting optional table index. -/
def test : UFn :=
  { name := "test", params := [("o", .opt 2)], kinds := [.opt 0],
    res := none, resOpt := some (0, 2), held := [], puts := [], gives := [],
    body := [.bindOpt "x" 0 (.var "o"), .ifBeg (.istSome (.var "x") 0),
      .bindOpt "y" 0 (.etwas (.lit 1)), .setVarOpt "x" 0 (.var "y"),
      .ifElse, .setVarOpt "x" 0 .nichts, .blkEnd], ret := .opt (.var "x") }

def unit : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("next", (0, 0))], opts := [("next", 0)] }],
    locks := [], fns := [test] }

def body : List Gabbro.Body.Stmt :=
  [.bindName "x" (.name "o"),
    .ite (.bin .ne (.name "x") (.lit .absent))
      [.bindName "y" (.someOf (.lit (.int 1))), .bindName "x" (.name "y")]
      [.bindName "x" (.lit .absent)],
    .ret (some (.name "x"))]

theorem reader_form : zuBodyZ unit test = some body := by cbv

theorem gates : stimmigB unit = true ∧ nullB unit = true := by
  constructor <;> cbv

/-- The canonical lowerer accepts the same binder, assignment, test and return fixture. -/
theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

/-- An option table field uses the ordinary declared slot place. -/
theorem field_reader :
    namedOption unit test (BodyNames.start test) (.tab "T" "next" (.lit 0)) =
      some (.place "T" (.lit (.int 0)) "next") := by cbv

theorem table_names : TabEindeutig unit := by
  constructor <;> intro t
  all_goals
    have ht : t = ⟨0, by decide⟩ := Fin.ext (by
      have h := t.isLt
      change t.val < 1 at h
      change t.val = 0
      omega)
    subst t
    cbv

/-- The generic simulation has joint, nonempty premises on a table with two slots.
    Neither the world nor the local binding is restricted to a concrete test state. -/
theorem absence_sim_zeuge (σ : World (declOf unit)) (base : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) :
    Gabbro.Body.eval ⟨encG unit σ base, β⟩ (.lit .absent) =
      some (valOf (.opt ((declOf unit).count ⟨0, by decide⟩))
        (eval σ (Expr.none (D := declOf unit) 2 : Expr (declOf unit) [] [] (.opt 2)) σ .nil)) := by
  exact lowOpt_sim (fn := { test with params := [], kinds := [] }) (sh := 0)
    (num := 0) (hn := by decide) (v := .nichts) rfl rfl table_names σ σ .nil
    ⟨encG unit σ base, β⟩ (wgrel_enc unit σ base).1 (by intro p j h; cases h)

/-- The field simulation also has joint premises: this is an actual option slot, not
    an integer slot with a placeholder range or an assumed reader result. -/
theorem field_sim_zeuge (σ : World (declOf unit)) (base : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) :
    ∃ ev : Expr (declOf unit) [] [] (.opt ((declOf unit).count ⟨0, by decide⟩)),
      lowOpt unit [] [] { test with params := [], kinds := [] } 0 0 (by decide)
        (.tab "T" "next" (.lit 0)) = .ok ev ∧
      Gabbro.Body.eval ⟨encG unit σ base, β⟩ (.place "T" (.lit (.int 0)) "next") =
        some (valOf _ (eval σ ev σ .nil)) := by
  have existsField : (lowOpt unit [] [] { test with params := [], kinds := [] }
      0 0 (by decide) (.tab "T" "next" (.lit 0))).toOption.isSome = true := by cbv
  cases h : lowOpt unit [] [] { test with params := [], kinds := [] }
      0 0 (by decide) (.tab "T" "next" (.lit 0)) with
  | error err => simp only [h, Except.toOption, Option.isSome_none, Bool.false_eq_true] at existsField
  | ok ev =>
    refine ⟨ev, (by first | exact h | rfl), ?_⟩
    exact lowOpt_sim h rfl table_names σ σ .nil ⟨encG unit σ base, β⟩
      (wgrel_enc unit σ base).1 (by intro p j hp; cases hp)

def lookup : UFn :=
  { test with
    name := "lookup", params := [], kinds := [], body := [],
    ret := .opt (.etwas (.lit 1)) }

def identity : UFn := { test with name := "identity", body := [], ret := .opt (.var "o") }

def caller : UFn :=
  { test with
    name := "caller", params := [], kinds := [],
    body := [.bindCall "answer" "lookup" [],
      .bindCall "again" "identity" [.oval (.var "answer")]], ret := .opt (.var "again") }

def callUnit : UProg := { unit with fns := [lookup, caller, identity] }

/-- The reader and canonical lowerer agree on an optional direct call result. -/
theorem result_call_reader :
    zuBodyZ callUnit caller = some
      [.bindCall "answer" "lookup" [] [] (.lit (.bool true)),
        .bindCall "again" "identity" ["o"] [.name "answer"] (.hasShape "o" .opt),
        .ret (some (.name "again"))] := by cbv

theorem result_call_lowered : (lowerAllg callUnit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 3 := bound
    have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases casesIndex with rfl | rfl | rfl <;> constructor <;> cbv

/-- Foreign option calls and reads through an unknown pointer remain explicit refusals. -/
theorem remaining_refusals :
    zuBodyZ unit { test with body := [.bindOptBeg "x" "foreign" []] } = none ∧
    namedOption unit test (BodyNames.start test) (.slot "p" "next" (.lit 0)) = none := by
  cbv

#print axioms lowOpt_sim
#print axioms lowBindOpt_named_sim
#print axioms lowSetVarOpt_named_sim

end Gabbro.Bruecke.OptionValueZeuge
