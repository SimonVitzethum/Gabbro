module
public import Bruecke.Kette.RecordZeuge
import all Init.Data.String.Basic
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.Bootstrap
import all Init.Data.String.Length
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
@[expose] public section

/-! # Joint inferred-record and full local narrow-branch witnesses -/

namespace Gabbro.Bruecke.RecordBranchZeuge
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

attribute [local cbv_eval] lowWertE.eq_def lowWertAtE.eq_def lowProductArgs.eq_def

/-- A failure branch has all four local binding forms, record replacement and a record return.
    The success continuation independently infers a constructor and copies the record. -/
def clip : UFn :=
  { name := "clip"
    params := [("k", .int 0 9)]
    kinds := [.int]
    res := none
    resTy := some RecordZeuge.schema.ty
    held := []
    puts := []
    gives := []
    body := [.narrowBeg "k" 0 3,
      .bind "n" none (.lit 2),
      .bindMut "m" 0 9 (.param "n"),
      .bindB "flag" .tru,
      .bindW "out" none (.product 0 false
        [(.int 0 9, .param "m"), (.bool, .param "flag")]),
      .bindW "answer" none (.replace (.param "out") "a" (.lit 4)),
      .ret (.wert (.param "answer")), .blkEnd,
      .bindW "copy" none (.product 0 false [(.int 0 9, .lit 3), (.bool, .truth false)]),
      .bindW "alias" none (.param "copy")]
    ret := .wert (.param "alias") }

def unit : UProg := { tabs := [], locks := [], fns := [clip], records := [RecordZeuge.schema] }

def errorBody : List Gabbro.Body.Stmt :=
  [.bindName "n" (.lit (.int 2)), .bindName "m" (.name "n"),
    .bindName "flag" (.lit (.bool true)),
    .bindName "out" (.recOf [.name "m", .name "flag"]),
    .bindName "answer" (.recSet (.name "out") 0 (.lit (.int 4))),
    .ret (some (.name "answer"))]

def body : List Gabbro.Body.Stmt :=
  [narrowStep (BodyNames.start clip) "k" 0 3 (.name "k") errorBody,
    .bindName "copy" (.recOf [.lit (.int 3), .lit (.bool false)]),
    .bindName "alias" (.name "copy"), .ret (some (.name "alias"))]

/-- The inference reader and the real lowerer accept the same nonempty failure branch. -/
theorem record_branch_reader_zeuge :
    zuBodyZ unit clip = some body ∧ stimmigB unit = true ∧ bindFrischAllB unit = true := by
  exact ⟨by cbv, by cbv, by cbv⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

def program : Programm (declOf unit) := ((lowerAllg unit).toOption.get lowered_some).1
def functions : List (declOf unit).Fn := ((lowerAllg unit).toOption.get lowered_some).2

theorem lowered : lowerAllg unit = .ok (program, functions) := except_ok_get lowered_some

def failedState (s : Gabbro.Body.State) : Gabbro.Body.State :=
  ⟨s.world, Gabbro.Body.bindLocal
    (Gabbro.Body.bindLocal
      (Gabbro.Body.bindLocal
        (Gabbro.Body.bindLocal
          (Gabbro.Body.bindLocal s.local' "n" (.int 2)) "m" (.int 2)) "flag" (.bool true))
        "out" (.record [.int 2, .bool true])) "answer" (.record [.int 4, .bool true])⟩

def successState (s : Gabbro.Body.State) (n : Int) : Gabbro.Body.State :=
  ⟨s.world, Gabbro.Body.bindLocal
    (Gabbro.Body.bindLocal (Gabbro.Body.bindLocal s.local' "k##" (.int n))
      "copy" (.record [.int 3, .bool false])) "alias" (.record [.int 3, .bool false])⟩

theorem exec_error (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) :
    Gabbro.Body.exec ρB errorBody s = .returned (failedState s) (some (.record [.int 4, .bool true])) := by
  simp [errorBody, failedState, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
    Gabbro.Body.eval_recOf, Gabbro.Body.evalAll, Gabbro.Body.bindLocal_here]

theorem exec_success (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) (n : Int)
    (h : Gabbro.Body.eval s (.name "k") = some (.int n)) (hb : 0 ≤ n ∧ n ≤ 3) :
    Gabbro.Body.exec ρB body s = .returned (successState s n) (some (.record [.int 3, .bool false])) := by
  have ht := narrowTest_eval (lo := 0) (hi := 3) h
  have hf : (BodyNames.start clip).fresh "k" = "k##" := by cbv
  simp [body, narrowStep, ht, hb, hf, h, successState, Gabbro.Body.exec, Gabbro.Body.step,
    Gabbro.Body.eval, Gabbro.Body.eval_recOf, Gabbro.Body.evalAll, Gabbro.Body.bindLocal_here]

theorem exec_failure (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) (n : Int)
    (h : Gabbro.Body.eval s (.name "k") = some (.int n)) (hb : ¬ (0 ≤ n ∧ n ≤ 3)) :
    Gabbro.Body.exec ρB body s = .returned (failedState s) (some (.record [.int 4, .bool true])) := by
  have ht := narrowTest_eval (lo := 0) (hi := 3) h
  simp only [body, narrowStep, Gabbro.Body.exec, Gabbro.Body.step, ht, hb, decide_false,
    exec_error]

theorem meets : meetsU unit (wfU unit) clip body := by
  intro ρB s hW hpre
  change some (.bool ((s.local' "k").hasShape (.intIn 0 9))) = some (.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨n, hn, _, _⟩ := Gabbro.Body.Value.hasShape_intIn_true (s.local' "k") 0 9 hshape
  have hv : Gabbro.Body.eval s (.name "k") = some (.int n) := by simp only [Gabbro.Body.eval, hn]
  change ∃ t, Gabbro.Body.finalState (Gabbro.Body.exec ρB body s) = some t ∧
    wfU unit t ∧ ∃ v, Gabbro.Body.finalValue (Gabbro.Body.exec ρB body s) = some v ∧
      v.hasShape (.record [.intIn 0 9, .bool]) = true
  by_cases hb : 0 ≤ n ∧ n ≤ 3
  · rw [exec_success ρB s n hv hb]
    exact ⟨successState s n, rfl, hW, .record [.int 3, .bool false], rfl, by cbv⟩
  · rw [exec_failure ρB s n hv hb]
    exact ⟨failedState s, rfl, hW, .record [.int 4, .bool true], rfl, by cbv⟩

/-- Both branches meet the actual entry precondition and return different records. -/
theorem outcomes_zeuge (ρB : Gabbro.Body.Env) :
    Gabbro.Body.eval ⟨fun _ => .absent, fun _ => .int 2⟩ (preExpr clip) = some (.bool true) ∧
    Gabbro.Body.eval ⟨fun _ => .absent, fun _ => .int 8⟩ (preExpr clip) = some (.bool true) ∧
    Gabbro.Body.finalValue (Gabbro.Body.exec ρB body ⟨fun _ => .absent, fun _ => .int 2⟩) =
      some (.record [.int 3, .bool false]) ∧
    Gabbro.Body.finalValue (Gabbro.Body.exec ρB body ⟨fun _ => .absent, fun _ => .int 8⟩) =
      some (.record [.int 4, .bool true]) := by
  refine ⟨by cbv, by cbv, ?_, ?_⟩
  · rw [exec_success ρB ⟨fun _ => .absent, fun _ => .int 2⟩ 2 rfl (by constructor <;> omega)]; rfl
  · rw [exec_failure ρB ⟨fun _ => .absent, fun _ => .int 8⟩ 8 rfl (by omega)]; rfl

/-- The new reader forms jointly satisfy every premise of the generic canonical-body bridge. -/
theorem generic_bridge_record_branch_zeuge :
    ∀ passes c, KoerperGutR program passes c := by
  have shape : GetragenG unit (fun _ => True) :=
    getragenG_of_bools record_branch_reader_zeuge.2.1 (by cbv) record_branch_reader_zeuge.2.2
  have rank : Rang unit (rangAuto unit) := rang_of (by cbv)
  have duties : ∀ c : Fin unit.fns.length, True → ∃ bs,
      zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs := by
    intro ⟨i, hi⟩ _
    have small : i < 1 := hi
    have zero : i = 0 := by omega
    subst i
    exact ⟨body, record_branch_reader_zeuge.1, meets⟩
  exact fun passes c => bruecke_koerperGutR_G lowered shape (rangAuto unit) rank duties passes c True.intro

/-- Inferred locals are also accepted in the existing nested conditional fixture. -/
theorem inferred_nested_record_zeuge :
    let f := { RecordZeuge.nestedFields with
      body := RecordZeuge.nestedFields.body.map fun st => match st with
        | .bindW x _ v => .bindW x none v | other => other }
    let u := { RecordZeuge.nestedUnit with fns := [f] }
    (zuBodyZ u f).isSome = true ∧
      (lowBodyF u ⟨0, by simp⟩ [RecordZeuge.schema.ty] f 20 [] f.body f.ret).toBool = true := by
  cbv

/-- Missing ending statements and non-record inference remain explicit refusals. -/
theorem ending_and_type_refusals_zeuge :
    endBodyZ unit 4 clip (BodyNames.start clip)
      [.bindW "out" none (.product 0 false [(.int 0 9, .lit 2), (.bool, .truth true)]),
        .blkEnd] = none ∧
    recordBinderType unit clip none (.lit 2) = none ∧
    endBodyZ unit 4 clip (BodyNames.start clip)
      [.ifBeg .tru, .ret (.wert (.param "out")), .ifElse,
        .ret (.wert (.param "out")), .blkEnd] = none := by
  exact ⟨by cbv, by cbv, by cbv⟩

#print axioms generic_bridge_record_branch_zeuge
end Gabbro.Bruecke.RecordBranchZeuge
