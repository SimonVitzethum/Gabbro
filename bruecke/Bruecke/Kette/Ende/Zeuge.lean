module
public import Bruecke.Kette.Formen.ZeugenSchritte
public import Bruecke.Kette.Ende.Simulation
public import Bruecke.Anweisung.Option.Zeuge
public import Bruecke.Anweisung.Option.StorageZeuge
public import Bruecke.Kette.Formen.OptionZeuge
public import Bruecke.Kette.Formen.ReasonZeuge
public import Bruecke.Kette.Formen.TagZeuge
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

/-! # Nonvacuous terminal-conditional witnesses

These witnesses cover the elaborated source model. The generic simulation is
`laufEndSeq_G`, connected through `lauf_G`; none of these values enters that proof.
-/

namespace Gabbro.Bruecke.EndeZeuge

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

attribute [local cbv_eval] Nat.log2_def lowEns.eq_def lowCmp.eq_def lowWertE.eq_def

def pick : UFn :=
  { name := "pick", params := [("b", .bool)], kinds := [.bool], res := some (0, 2),
    held := [], puts := [], gives := [],
    body := [.ifEnde (.var "b"), .bind "x" none (.lit 1), .ret (.val (.param "x")),
      .ifElse, .bind "x" none (.lit 2), .ret (.val (.param "x")), .blkEnd],
    ret := .keins }

def truth : UFn :=
  { name := "truth", params := [("b", .bool)], kinds := [.bool], res := none, resBool := true,
    held := [], puts := [], gives := [],
    body := [.ifEnde (.var "b"), .ret (.bool .tru), .ifElse, .ret (.bool .fls), .blkEnd],
    ret := .keins }

def stop : UFn :=
  { name := "stop", params := [("b", .bool)], kinds := [.bool], res := none,
    held := [], puts := [], gives := [],
    body := [.ifEnde (.var "b"), .ret .empty, .ifElse, .ret .empty, .blkEnd],
    ret := .keins }

def nested : UFn :=
  { name := "nested", params := [("b", .bool)], kinds := [.bool], res := some (0, 2),
    held := [], puts := [], gives := [],
    body := [.ifEnde (.var "b"), .ifEnde .tru, .ret (.val (.lit 1)), .ifElse,
      .ret (.val (.lit 0)), .blkEnd, .ifElse, .ret (.val (.lit 2)), .blkEnd],
    ret := .keins }

def unit : UProg := { tabs := [], locks := [], fns := [pick, truth, stop, nested] }

def pickBody : List Gabbro.Body.Stmt :=
  [.ite (.name "b")
    [.bindName "x" (.lit (.int 1)), .ret (some (.name "x"))]
    [.bindName "x##" (.lit (.int 2)), .ret (some (.name "x##"))]]

def truthBody : List Gabbro.Body.Stmt :=
  [.ite (.name "b") [.ret (some (.lit (.bool true)))] [.ret (some (.lit (.bool false)))]]

def stopBody : List Gabbro.Body.Stmt := [.ite (.name "b") [.ret none] [.ret none]]

def nestedBody : List Gabbro.Body.Stmt :=
  [.ite (.name "b") [.ite (.lit (.bool true)) [.ret (some (.lit (.int 1)))]
    [.ret (some (.lit (.int 0)))]] [.ret (some (.lit (.int 2)))]]

theorem readers : zuBodyZ unit pick = some pickBody ∧ zuBodyZ unit truth = some truthBody ∧
    zuBodyZ unit stop = some stopBody ∧ zuBodyZ unit nested = some nestedBody :=
  ⟨by cbv, by cbv, by cbv, by cbv⟩

theorem lowered_some : (lowerAllg unit).toOption.isSome = true := by
  apply Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs.lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 4 := bound
    have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl
    all_goals constructor <;> cbv

theorem checks : nullB unit = true ∧ stimmigB unit = true ∧
    bindFrischAllB unit = true ∧ rangB unit (rangAuto unit) = true ∧ ohneTransitionB unit = true :=
  ⟨by cbv, by cbv, by cbv, by cbv, by cbv⟩

def after (s : Gabbro.Body.State) (b : Bool) : Gabbro.Body.State :=
  ⟨s.world, if b then Gabbro.Body.bindLocal s.local' "x" (.int 1)
    else Gabbro.Body.bindLocal s.local' "x##" (.int 2)⟩

theorem pick_exec (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) (b : Bool)
    (hb : s.local' "b" = .bool b) :
    Gabbro.Body.exec ρB pickBody s = .returned (after s b) (some (.int (if b then 1 else 2))) := by
  cases b <;> simp only [pickBody, after, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
    Gabbro.Body.bindLocal_here, hb, Bool.false_eq_true, ↓reduceIte]

theorem pick_meets : meetsU unit (wfU unit) pick pickBody := by
  intro ρB s hW hpre
  change some (.bool ((s.local' "b").hasShape .bool)) = some (.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨b, hb⟩ := Gabbro.Body.Value.hasShape_bool_true (s.local' "b") hshape
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB pickBody s) = some s' ∧
    (postU unit (wfU unit) pick s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB pickBody s))).getD False
  rw [pick_exec ρB s b hb]
  refine ⟨after s b, rfl, hW, (if b then 1 else 2), rfl, ?_, ?_⟩ <;> cases b <;> decide

theorem truth_meets : meetsU unit (wfU unit) truth truthBody := by
  intro ρB s hW hpre
  change some (.bool ((s.local' "b").hasShape .bool)) = some (.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨b, hb⟩ := Gabbro.Body.Value.hasShape_bool_true (s.local' "b") hshape
  have hex : Gabbro.Body.exec ρB truthBody s = .returned s (some (.bool b)) := by
    cases b <;> simp only [truthBody, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
      hb, Bool.false_eq_true, ↓reduceIte]
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB truthBody s) = some s' ∧
    (postU unit (wfU unit) truth s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB truthBody s))).getD False
  rw [hex]
  exact ⟨s, rfl, hW, b, rfl⟩

theorem stop_meets : meetsU unit (wfU unit) stop stopBody := by
  intro ρB s hW hpre
  change some (.bool ((s.local' "b").hasShape .bool)) = some (.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨b, hb⟩ := Gabbro.Body.Value.hasShape_bool_true (s.local' "b") hshape
  have hex : Gabbro.Body.exec ρB stopBody s = .returned s none := by
    cases b <;> simp only [stopBody, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
      hb, Bool.false_eq_true, ↓reduceIte]
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB stopBody s) = some s' ∧
    (postU unit (wfU unit) stop s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB stopBody s))).getD False
  rw [hex]
  exact ⟨s, rfl, hW⟩

theorem nested_meets : meetsU unit (wfU unit) nested nestedBody := by
  intro ρB s hW hpre
  change some (.bool ((s.local' "b").hasShape .bool)) = some (.bool true) at hpre
  have hshape := Option.some.inj hpre
  injection hshape with hshape
  obtain ⟨b, hb⟩ := Gabbro.Body.Value.hasShape_bool_true (s.local' "b") hshape
  have hex : Gabbro.Body.exec ρB nestedBody s = .returned s (some (.int (if b then 1 else 2))) := by
    cases b <;> simp only [nestedBody, Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval,
      hb, Bool.false_eq_true, ↓reduceIte]
  change ∃ s', Gabbro.Body.finalState (Gabbro.Body.exec ρB nestedBody s) = some s' ∧
    (postU unit (wfU unit) nested s s'
      (Gabbro.Body.finalValue (Gabbro.Body.exec ρB nestedBody s))).getD False
  rw [hex]
  refine ⟨s, rfl, hW, (if b then 1 else 2), rfl, ?_, ?_⟩ <;> cases b <;> decide

/-- All carried-function duties hold jointly on a lowered unit with terminal branches. -/
theorem terminal_zeuge : GetragenG unit (fun _ => True) ∧
    (lowerAllg unit).toOption.isSome = true ∧ rangB unit (rangAuto unit) = true ∧
    (∀ c : Fin unit.fns.length, ∃ bs,
      zuBodyZ unit (fnAt unit c) = some bs ∧ meetsU unit (wfU unit) (fnAt unit c) bs) := by
  refine ⟨getragenG_of_bools (by cbv) (by cbv) (by cbv), lowered_some, checks.2.2.2.1, ?_⟩
  intro ⟨c, hc⟩
  rcases c with _ | _ | _ | _ | c
  · exact ⟨pickBody, readers.1, pick_meets⟩
  · exact ⟨truthBody, readers.2.1, truth_meets⟩
  · exact ⟨stopBody, readers.2.2.1, stop_meets⟩
  · exact ⟨nestedBody, readers.2.2.2, nested_meets⟩
  · have h : c + 4 < 4 := hc
    omega

/-- Extra top-level statements after the closing marker are still refused. -/
theorem continuation_refused :
    zuBodyZ unit { truth with body := truth.body ++ [.call "truth" [.bval .tru]] } = none := by cbv


/-- The terminal path retains the table of a direct option result through another
    call, a local binding, a local update and both kinds of field update. -/
def optionEnd : UFn :=
  { OptionStorageZeuge.test with name := "terminal",
    body := [.bindCall "answer" "lookup" [],
      .bindCall "again" "identity" [.oval (.var "answer")],
      .bindOpt "local" 0 (.var "again"), .setVarOpt "local" 0 .nichts,
      .assignOpt "p" "next" (.lit 0) (.var "local"),
      .assignTabOpt "T" "next" (.lit 1) (.var "again"),
      .ret (.opt (.var "local")), .blkEnd] }

def optionUnit : UProg :=
  { OptionValueZeuge.callUnit with
    fns := [OptionValueZeuge.lookup, optionEnd, OptionValueZeuge.identity] }

def optionBody : List Gabbro.Body.Stmt :=
  [.bindCall "answer" "lookup" [] [] (.lit (.bool true)),
    .bindCall "again" "identity" ["o"] [.name "answer"] (.hasShape "o" .opt),
    .bindName "local" (.name "again"), .bindName "local" (.lit .absent),
    .assign "T" (.lit (.int 0)) "next" (.name "local"),
    .assign "T" (.lit (.int 1)) "next" (.name "again"),
    .ret (some (.name "local"))]

/-- Joint nondegenerate premises for the option-end inversion and simulations:
    two table slots, actual call results, writable storage and an explicit closer. -/
theorem lowEndL_bindOpt_ok_zeuge :
    (match lowEndL (l := false) optionUnit ⟨1, by decide⟩ (optionEnd.params.map (·.2))
        optionEnd 12 [] [] optionEnd.body with
      | .error _ => False
      | .ok (_, tail) => tail = [.blkEnd]) ∧
    (seqZ optionUnit 12 optionEnd (BodyNames.start optionEnd) optionEnd.body).map (·.1) =
      some optionBody := by
  constructor <;> cbv

/-- The three dispatch forms are ordinary structured prefixes before an explicit
    terminal return. Their existing two-arm fixtures keep every arm nonempty. -/
theorem lowEndL_struct_ok_zeuge :
    (match lowEndL (l := false) OptionZeuge.unit ⟨0, by decide⟩ (OptionZeuge.test.params.map (·.2))
        OptionZeuge.test 12 [] []
        (OptionZeuge.test.body ++ [.ret (.val (.lit 0)), .blkEnd]) with
      | .error _ => False
      | .ok (_, tail) => tail = [.blkEnd]) ∧
    (match lowEndL (l := false) ReasonZeuge.unit ⟨0, by decide⟩ (ReasonZeuge.test.params.map (·.2))
        ReasonZeuge.test 12 [] []
        (ReasonZeuge.test.body ++ [.ret (.val (.lit 0)), .blkEnd]) with
      | .error _ => False
      | .ok (_, tail) => tail = [.blkEnd]) ∧
    (match lowEndL (l := false) TagZeuge.unit ⟨0, by decide⟩ (TagZeuge.test.params.map (·.2))
        TagZeuge.test 12 [] []
        (TagZeuge.test.body ++ [.ret (.val (.lit 0)), .blkEnd]) with
      | .error _ => False
      | .ok (_, tail) => tail = [.blkEnd]) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

end Gabbro.Bruecke.EndeZeuge
