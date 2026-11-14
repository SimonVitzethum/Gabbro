/- C16 items 9/10/12 on the front end: the elaborated record keeps the declared
   identity, both verdicts elaborate to the same generated shape, and the Duty
   threads through the probe and its gate wrapper.

   The phase certificates use kernel evaluation: the `uCheck` record preserves
   the name, the claim and the counterprobe while deriving the generated
   producer and Duty names from the check name (item 9); the false-verdict probe
   elaborates to its generated producer exactly like the true one (item 12);
   and the elaborated unit carries the Duty in the probe's and the wrapper's
   `nimmt`/`gibt` (items 10/12). The kernel side of the identity,
   the completed reports and the discharge lives in
   `Kern/Syntax/Satz/PruefungAbschluss.lean`. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Proben
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.Recording
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Einheit.ReturnCalls
import all Grammatik.Parser.Elab.Generic.StaticConformance
import Grammatik.Parser.Elab.Tuples.Identity

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

attribute [local cbv_opaque] uFloatLimit

/-- The false-verdict probe: the same check with a `can_fail` body returning
    `false` -- a completed measurement with a negative verdict, never a
    missing run. -/
def probenCheckFalsch : SCheck :=
  { probenCheck with canFail := .block [] (some (.ret (some .fls))) }

-- Select the actual mutual equations before evaluating their large fuel.
-- These equations retain the original recording and elaboration callbacks.
private theorem record_block_return (heads : List UFnKopf) (check : SCheck)
    (fuel : Nat) (ctx : UCtx) (point : Nat) (value : SExpr) :
    recordCheckCode heads check fuel ctx point (.block [] (some (.ret (some value)))) =
      (match fuel with
      | 0 => .error "check recording expansion exhausted"
      | fuel + 1 => do
        let (statements, ctx, reporters, extraHeads, point) ←
          recordCheckStatements heads check fuel ctx point []
        let (body, reporter, head) ← recordCheckReturn ctx check point value
        match body with
        | .block prelude ending =>
          pure (.block (statements ++ prelude) ending, reporters ++ [reporter],
            extraHeads ++ [head], point + 1)
        | _ => .error "check reporter expansion is not a block") := by
  cases fuel <;> simp only [recordCheckCode] <;> rfl

private theorem record_statements_nil (heads : List UFnKopf) (check : SCheck)
    (fuel : Nat) (ctx : UCtx) (point : Nat) :
    recordCheckStatements heads check fuel ctx point [] = match fuel with
      | 0 => .error "check recording expansion exhausted"
      | _ + 1 => .ok ([], ctx, [], [], point) := by
  cases fuel <;> simp only [recordCheckStatements]

private theorem substitute_true (fuel : Nat) :
    checkSampleSubstitute [] fuel .tru = .tru := by
  cases fuel <;> rfl

private theorem row_nil (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) :
    uAnwReihe tabs heads fuel ctx [] = match fuel with
      | 0 => .error "nesting without G form"
      | _ + 1 => .ok ([], ctx) := by
  cases fuel <;> simp only [uAnwReihe]

private theorem row_cons (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (statement : SAnw) (rest : List SAnw) :
    uAnwReihe tabs heads fuel ctx (statement :: rest) = (match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => do
        let (before, ctx, statement) ← expandFoldStmt ctx statement
        let (code, ctx) ← uAnwReiheCore tabs heads (fuel + 1) ctx (statement :: rest)
        pure (before ++ code, ctx)) := by
  cases fuel <;> simp only [uAnwReihe]

private theorem core_bind (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (mutable : Bool) (name : String)
    (ty : Option STyp) (value : SExpr) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.bind mutable name ty value :: rest) =
      (match fuel with
      | 0 => .error "nesting without G form"
      | fuel + 1 => do
        let (statement, next) ← uBindWert ctx tabs heads mutable name ty value
        let (code, ending) ← uAnwReihe tabs heads fuel
          (foldBindingContext ctx next statement) rest
        pure (statement :: code, ending)) := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel =>
    simp only [uAnwReiheCore]
    cases uBindWert ctx tabs heads mutable name ty value with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨statement, next⟩
      dsimp only [bind, Except.bind]
      cases uAnwReihe tabs heads fuel (foldBindingContext ctx next statement) rest <;> rfl

private theorem clauses_nil (ctx : UCtx) : elabKlauseln ctx [] = .ok ([], []) := by
  cases empty : ctx.specs.isEmpty <;>
    simp only [elabKlauseln, empty, Bool.false_eq_true, ite_false, ite_true, uSpecKlauseln] <;> rfl

private theorem return_variable (ctx : UCtx) (heads : List UFnKopf) (name : String) :
    expandReturnCall ctx heads (some (.ret (some (.variable name)))) =
      .ok ([], ctx, some (.ret (some (.variable name)))) := by
  unfold expandReturnCall
  cases uEnde ctx (some (.ret (some (.variable name)))) <;> rfl

private theorem return_none (ctx : UCtx) (heads : List UFnKopf) :
    expandReturnCall ctx heads none = .ok ([], ctx, none) := by
  unfold expandReturnCall
  cases uEnde ctx none <;> rfl

attribute [local cbv_opaque] recordCheckCode recordCheckStatements checkSampleSubstitute
  uAnwReihe uAnwReiheCore elabKlauseln expandReturnCall
attribute [local cbv_eval] record_block_return record_statements_nil substitute_true
  row_nil row_cons core_bind clauses_nil return_variable return_none

-- These witnesses contain an empty gate and a check declaration. Neither item consults the
-- tuple context. Keep its eager constant/alias/type collection out of proof evaluation.
private theorem tuple_empty_gate_check (art name : String) (error : Option String)
    (generics : List SGenericParam) (check : SCheck) :
    Tuples.expand
      [.fnT { art, name, params := [], res := none, fehler := error, klauseln := [], generics }
        (.block [] none), .checkT check] =
      .ok ([.fnT { art, name, params := [], res := none, fehler := error, klauseln := [], generics }
        (.block [] none), .checkT check], []) := by
  apply Tuples.expand_of_mapM_eq_pure
  intro k
  have gate := Tuples.expandItem_empty_function k
    { art, name, params := [], res := none, fehler := error, klauseln := [], generics }
    rfl rfl rfl
  have checked := Tuples.expandItem_check k check
  simp only [List.mapM_cons, List.mapM_nil, gate, checked, pure_bind]

attribute [local cbv_opaque] Tuples.expand Tuples.prepareContext
attribute [local cbv_eval] tuple_empty_gate_check

-- Infer each complete generated result from its canonical producer, before
-- inspecting names or resource lists. No unit is reconstructed from projections.
private theorem false_probe_packet : ∃ functions : List UFn,
    uProbeFns [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 ["g"] [probenCheckFalsch] =
      .ok functions ∧ functions.map (·.name) = ["p#probe", "p#report#0"] := by
  let functions : List UFn := ?_
  have produced :
      uProbeFns [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 ["g"] [probenCheckFalsch] =
        .ok functions := by
    cbv <;> exact Eq.refl _
  exact ⟨functions, produced, by rfl⟩

private theorem true_unit_packet : ∃ unit : UProg,
    elabU [probenFn, .checkT probenCheck] = .ok unit ∧
      unit.fns.map (fun f => (f.name, f.nimmt, f.gibt)) =
        [("g", [], []), ("p#probe", ["p#duty"], ["p#duty"]),
          ("p#report#0", [], []), ("p#tor#g", ["p#duty"], ["p#duty"])] := by
  let unit : UProg := ?_
  have elaborated : elabU [probenFn, .checkT probenCheck] = .ok unit := by
    cbv <;> exact Eq.refl _
  exact ⟨unit, elaborated, by rfl⟩

private theorem false_unit_packet : ∃ unit : UProg,
    elabU [probenFn, .checkT probenCheckFalsch] = .ok unit ∧
      unit.fns.map (·.name) = ["g", "p#probe", "p#report#0", "p#tor#g"] := by
  let unit : UProg := ?_
  have elaborated : elabU [probenFn, .checkT probenCheckFalsch] = .ok unit := by
    cbv <;> exact Eq.refl _
  exact ⟨unit, elaborated, by rfl⟩

/-- The identity is preserved: the elaborated record keeps the name, the claim
    and the counterprobe, and derives the generated producer and Duty names
    from the check name. -/
example : (uCheck [] [] ["g"] ["p"] [] probenCheck).map
    (fun c => (c.name, c.claim, c.sonde, c.probe, c.duty)) =
    .ok ("p", "c", none, "p#probe", "p#duty") := by cbv

/-- The counterprobe identity travels with the record. -/
def probenCheckSonde : SCheck :=
  { probenCheck with sonde := some ("assert x", "ext") }

example : (uCheck [] [] ["g"] ["p"] [] probenCheckSonde).map (·.sonde) =
    .ok (some ("ext", "assert x")) := by cbv

/-- The floors elaborate to the retained predicates. -/
example : (uCheck [] [] ["g"] ["p"] [] { probenCheck with boden := [.tru, .fls] }).map
    (·.boeden) = .ok [.tru, .fls] := by cbv

/-- The false-verdict probe elaborates to its generated producer, exactly like
    the true one. -/
example : (uProbeFns [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 ["g"] [probenCheckFalsch]).map
    (List.map (·.name)) = .ok ["p#probe", "p#report#0"] := by
  obtain ⟨functions, produced, names⟩ := false_probe_packet
  rw [produced]
  exact congrArg Except.ok names

/-- The elaborated unit carries the Duty: the probe threads it (`nimmt` and
    `gibt`), the gate wrapper threads it too. -/
example : (elabU [probenFn, .checkT probenCheck]).map
    (fun u => u.fns.map fun f => (f.name, f.nimmt, f.gibt)) =
    .ok [("g", [], []), ("p#probe", ["p#duty"], ["p#duty"]),
      ("p#report#0", [], []), ("p#tor#g", ["p#duty"], ["p#duty"])] := by
  obtain ⟨unit, elaborated, duties⟩ := true_unit_packet
  rw [elaborated]
  exact congrArg Except.ok duties

/-- The false-verdict check elaborates to the same generated shape: the Duty
    threads through `false` returns too. -/
example : (elabU [probenFn, .checkT probenCheckFalsch]).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#report#0", "p#tor#g"] := by
  obtain ⟨unit, elaborated, names⟩ := false_unit_packet
  rw [elaborated]
  exact congrArg Except.ok names

/-- A `bool` gate derives its Duty-threading wrapper forwarding the answer:
    the wrapper binds the gate call and returns it. -/
example : uTorHuelle "p#duty" [{ torGate with resBool := true }] [] "p" "g" =
    .ok { name := "p#tor#g"
          params := []
          kinds := []
          res := none
          resBool := true
          held := []
          puts := []
          gputs := []
          nimmt := ["p#duty"]
          gibt := ["p#duty"]
          gives := []
          needs := []
          body := [.bindCall "ans" "g" []]
          ret := .bool (.var "ans") } := by cbv

end Gabbro.Grammatik.Parser.Uebersetze
