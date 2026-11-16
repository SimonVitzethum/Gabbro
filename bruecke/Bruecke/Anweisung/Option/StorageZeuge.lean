module
public import Bruecke.Kette.Quelle
public import Grammatik.Parser.Stmt.LibraryFixtureProofs
public import Bruecke.Anweisung.Option.Speichern
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

/-! # Joint witnesses for option storage and nested returns -/
namespace Gabbro.Bruecke.OptionStorageZeuge
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

attribute [local cbv_eval] lowEns.eq_def lowWertE.eq_def

/-- A two-slot linked table, a genuine read/write capability, and both option constructors.
    Both branches return from within a nested block after updating the same option field. -/
def test : UFn :=
  { name := "storage", params := [("p", .ptr (.table 0 (true, true))), ("o", .opt 2)],
    kinds := [.ptr (.table 0 (true, true)), .opt 0], res := none, resOpt := some (0, 2),
    held := [], puts := ["T"], gives := [],
    body := [.assignOpt "p" "next" (.lit 0) (.var "o"),
      .assignTabOpt "T" "next" (.lit 1) (.slot "p" "next" (.lit 0)),
      .ifBeg (.istSome (.var "o") 0), .ret (.opt (.slot "p" "next" (.lit 1))),
      .ifElse, .ret (.opt .nichts), .blkEnd], ret := .opt .nichts }

def unit : UProg :=
  { tabs := [{ name := "T", count := 2, cols := [("next", (0, 0))], opts := [("next", 0)] }],
    locks := [], fns := [test] }

def body : List Gabbro.Body.Stmt :=
  [.assign "T" (.lit (.int 0)) "next" (.name "o"),
    .assign "T" (.lit (.int 1)) "next" (.place "T" (.lit (.int 0)) "next"),
    .ite (.bin .ne (.name "o") (.lit .absent))
      [.ret (some (.place "T" (.lit (.int 1)) "next"))]
      [.ret (some (.lit .absent))],
    .ret (some (.lit .absent))]

theorem pointer_reader :
    namedOption unit test (BodyNames.start test) (.slot "p" "next" (.lit 1)) =
      some (.place "T" (.lit (.int 1)) "next") := by cbv

theorem pointer_writer :
    namedStmt unit test (BodyNames.start test) (.assignOpt "p" "next" (.lit 0) (.var "o")) =
      some (.assign "T" (.lit (.int 0)) "next" (.name "o")) := by cbv

theorem table_writer :
    namedStmt unit test (BodyNames.start test)
      (.assignTabOpt "T" "next" (.lit 1) (.slot "p" "next" (.lit 0))) =
      some (.assign "T" (.lit (.int 1)) "next" (.place "T" (.lit (.int 0)) "next")) := by cbv

theorem nested_return_reader :
    retZ unit test (BodyNames.start test) (.opt (.slot "p" "next" (.lit 1))) =
      some (.ret (some (.place "T" (.lit (.int 1)) "next"))) := by cbv

/-- These reader witnesses belong to one real body, accepted by both unit gates. -/
theorem reader_form : zuBodyZ unit test = some body := by cbv

theorem gates : stimmigB unit = true ∧ nullB unit = true := by
  constructor <;> cbv

/-- The actual canonical compiler accepts the same stores and nested option returns. -/
theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

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

theorem names_zeuge : NamenEindeutig test := by
  change (["p", "o"] : List String).Nodup
  decide

/-- The pointer simulation's lowering, reader, world and environment premises hold jointly
    for every canonical world and every typed environment, including both stored constructors. -/
theorem pointer_sim_zeuge (σ : World (declOf unit)) (base : Gabbro.Body.World)
    (ρ : Env (declOf unit) (test.params.map (·.2))) :
    ∃ ev : Expr (declOf unit) (test.params.map (·.2)) [] (.opt ((declOf unit).count ⟨0, by decide⟩)),
      lowOpt unit (test.params.map (·.2)) [] test 0 0 (by decide)
        (.slot "p" "next" (.lit 1)) = .ok ev ∧
      Gabbro.Body.eval
        ⟨encG unit σ base, Gabbro.Body.bindAll (test.params.map (·.1)) (envVals ρ) (fun _ => .absent)⟩
        (.place "T" (.lit (.int 1)) "next") = some (valOf _ (eval σ ev σ ρ)) := by
  have existsRead : (lowOpt unit (test.params.map (·.2)) [] test 0 0 (by decide)
      (.slot "p" "next" (.lit 1))).toOption.isSome = true := by cbv
  cases h : lowOpt unit (test.params.map (·.2)) [] test 0 0 (by decide)
      (.slot "p" "next" (.lit 1)) with
  | error err => simp only [h, Except.toOption, Option.isSome_none, Bool.false_eq_true] at existsRead
  | ok ev =>
    refine ⟨ev, (by first | exact h | rfl | simp_all), ?_⟩
    exact lowOpt_sim h (by cbv) table_names σ σ ρ _ (wgrel_enc unit σ base).1
      (lrel_bindAll test ρ names_zeuge rfl)

/-- The scope premise of both store simulations is satisfied by the same fixture. -/
theorem scope : UmfangB (test.params.map (·.2)) test (BodyNames.start test) :=
  UmfangB.start (u := unit) ⟨0, by decide⟩ (artB_ok (by cbv)) names_zeuge

section StoreSimulations
variable (O : Orakel (declOf unit)) (passes : Nat)
    (R : ∀ f : (declOf unit).Fn, World (declOf unit) →
      Env (declOf unit) ((declOf unit).params f) → RufAusgang f)
    (σ : World (declOf unit)) (base : Gabbro.Body.World)
    (ρ : Env (declOf unit) (test.params.map (·.2)))

/-- The pointer writer's reader, lowering and state premises have a common witness. -/
theorem pointer_store_sim_zeuge :
    ∃ (g : Stmt (declOf unit) (verOf unit ⟨0, by decide⟩) false
        (test.params.map (·.2)) [] []), ∃ σ' cn k fld value,
      lowAssignDurchOL (l := false) unit ⟨0, by decide⟩ (test.params.map (·.2)) test []
        "p" "next" (.lit 0) (.var "o") = .ok g ∧
      execStmt O passes R g σ ρ = .ok σ' ρ ∧
      WGRel unit σ' (Gabbro.Body.store (encG unit σ base) (.slot cn k fld) value) := by
  have existsWrite : (lowAssignDurchOL (l := false) unit ⟨0, by decide⟩
      (test.params.map (·.2)) test [] "p" "next" (.lit 0) (.var "o")).toOption.isSome = true := by cbv
  cases h : lowAssignDurchOL (l := false) unit ⟨0, by decide⟩
      (test.params.map (·.2)) test [] "p" "next" (.lit 0) (.var "o") with
  | error err => simp only [h, Except.toOption, Option.isSome_none, Bool.false_eq_true] at existsWrite
  | ok g =>
    have hL := lrel_bindAll test ρ names_zeuge rfl
    obtain ⟨σ', cn, k, fld, value, hex, _, hw, _⟩ :=
      lowAssignDurchO_simB ⟨0, by decide⟩ h (bst := .assign "T" (.lit (.int 0)) "next" (.name "o"))
        (by cbv) scope table_names O passes R σ ρ ⟨encG unit σ base, _⟩ (wgrel_enc unit σ base) hL
    exact ⟨g, σ', cn, k, fld, value, (by first | exact h | rfl | simp_all), hex, hw⟩

/-- The direct table writer uses the same scope and a genuine pointer option operand. -/
theorem table_store_sim_zeuge :
    ∃ (g : Stmt (declOf unit) (verOf unit ⟨0, by decide⟩) false
        (test.params.map (·.2)) [] []), ∃ σ' cn k fld value,
      lowAssignTabOL (l := false) unit ⟨0, by decide⟩ (test.params.map (·.2)) test []
        "T" "next" (.lit 1) (.slot "p" "next" (.lit 0)) = .ok g ∧
      execStmt O passes R g σ ρ = .ok σ' ρ ∧
      WGRel unit σ' (Gabbro.Body.store (encG unit σ base) (.slot cn k fld) value) := by
  have existsWrite : (lowAssignTabOL (l := false) unit ⟨0, by decide⟩
      (test.params.map (·.2)) test [] "T" "next" (.lit 1)
      (.slot "p" "next" (.lit 0))).toOption.isSome = true := by cbv
  cases h : lowAssignTabOL (l := false) unit ⟨0, by decide⟩
      (test.params.map (·.2)) test [] "T" "next" (.lit 1) (.slot "p" "next" (.lit 0)) with
  | error err => simp only [h, Except.toOption, Option.isSome_none, Bool.false_eq_true] at existsWrite
  | ok g =>
    have hL := lrel_bindAll test ρ names_zeuge rfl
    obtain ⟨σ', cn, k, fld, value, hex, _, hw, _⟩ :=
      lowAssignTabO_simB ⟨0, by decide⟩ h
        (bst := .assign "T" (.lit (.int 1)) "next" (.place "T" (.lit (.int 0)) "next"))
        (by cbv) scope table_names O passes R σ ρ ⟨encG unit σ base, _⟩ (wgrel_enc unit σ base) hL
    exact ⟨g, σ', cn, k, fld, value, (by first | exact h | rfl | simp_all), hex, hw⟩

/-- The nested-return simulation also has joint lowering and positional-state premises. -/
theorem nested_return_sim_zeuge :
    ∃ (g : Stmt (declOf unit) (verOf unit ⟨0, by decide⟩) false
        (test.params.map (·.2)) [] []), ∃ σ' v,
      lowRetStmt (l := false) unit ⟨0, by decide⟩ (test.params.map (·.2)) test [] []
        (.opt (.slot "p" "next" (.lit 1))) = .ok g ∧
      execStmt O passes R g σ ρ = .zurueck σ' v ∧ WGRel unit σ' (encG unit σ base) := by
  have existsReturn : (lowRetStmt (l := false) unit ⟨0, by decide⟩
      (test.params.map (·.2)) test [] []
      (.opt (.slot "p" "next" (.lit 1)))).toOption.isSome = true := by cbv
  cases h : lowRetStmt (l := false) unit ⟨0, by decide⟩
      (test.params.map (·.2)) test [] [] (.opt (.slot "p" "next" (.lit 1))) with
  | error err => simp only [h, Except.toOption, Option.isSome_none, Bool.false_eq_true] at existsReturn
  | ok g =>
    have hL := PositionalLRel.start names_zeuge
      (lrel_bindAll test ρ names_zeuge rfl)
    obtain ⟨σ', v, hex, hw, _⟩ := lowRet_sim ⟨0, by decide⟩ h
      (bst := .ret (some (.place "T" (.lit (.int 1)) "next")))
      (by cbv) (fun _ h => by cases h) scope table_names O passes R σ ρ ⟨encG unit σ base, _⟩ (wgrel_enc unit σ base) hL
    exact ⟨g, σ', v, (by first | exact h | rfl | simp_all), hex, hw⟩
end StoreSimulations

/-- Even when the supplied context has a pointer, inconsistent source metadata cannot
    redirect the named Body field to a different declaration. -/
theorem inconsistent_pointer_refused :
    lowOpt unit (test.params.map (·.2)) []
      { test with params := [("p", .int 0 1), ("o", .opt 2)] } 0 0 (by decide)
      (.slot "p" "next" (.lit 1)) = .error "pointer parameter kind and type disagree" := by
  cbv

/-- Both paths actually return, with a present value on the nonempty branch and absence on
    the other. This checks the nested returns beyond their syntactic reader witnesses. -/
theorem both_returns (ρB : Gabbro.Body.Env) (w : Gabbro.Body.World) (β : Gabbro.Body.Binding) :
    Gabbro.Body.finalValue (Gabbro.Body.exec ρB body
      ⟨w, Gabbro.Body.bindLocal β "o" (.present 1)⟩) = some (.present 1) ∧
    Gabbro.Body.finalValue (Gabbro.Body.exec ρB body
      ⟨w, Gabbro.Body.bindLocal β "o" .absent⟩) = some .absent := by
  constructor <;> simp [body, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
    Gabbro.Body.bindLocal, Gabbro.Body.binop, Gabbro.Body.store, Gabbro.Body.finalValue]

/-- No foreign-call semantics are invented for option-producing external calls. -/
theorem foreign_refusal : zuBodyZ unit { test with body := [.bindOptBeg "x" "foreign" []] } = none := by
  cbv

#print axioms lowOpt_sim
#print axioms lowAssignDurchO_named_sim
#print axioms lowAssignTabO_named_sim
#print axioms lowRet_sim
end Gabbro.Bruecke.OptionStorageZeuge
