module

public import Core.Ast.Semantik.ProgramForms
public import Core.Ast.Program.LoopFrame

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

private theorem body_shape (pre body post : List Befehl) (back : Befehl)
    (inside : RueckkantenImCode body) (after : RueckkantenImCode post) :
    ∀ pc (instr : Befehl), pre.length ≤ pc → pc ≠ pre.length + body.length →
      (pre ++ body ++ [back] ++ post)[pc]? = some instr →
      instr.rueckweite ≤ pc - pre.length := by
  intro pc instr lower notBack atPC
  simp only [List.append_assoc, List.singleton_append] at atPC
  rw [List.getElem?_append_right lower] at atPC
  by_cases inBody : pc - pre.length < body.length
  · rw [List.getElem?_append_left inBody] at atPC
    exact inside _ instr atPC
  · rw [List.getElem?_append_right (Nat.le_of_not_gt inBody)] at atPC
    have splitIndex : pc - pre.length - body.length = (pc - pre.length - body.length - 1) + 1 := by omega
    rw [splitIndex, List.getElem?_cons_succ] at atPC
    exact Nat.le_trans (after _ instr atPC) (by omega)

private abbrev LoopHead (code : List Befehl) (origin : Rahmen)
    (entry key count : Nat) (frame : Rahmen) : Prop :=
  (∃ n, Rahmen.LaufN code n origin frame) ∧ frame.Aktiv ∧
    frame.pc = entry ∧ frame.fortsetzungen.length = origin.fortsetzungen.length ∧
    frame.zaehler key = some count

private theorem reachable_append (reach : ∃ n, Rahmen.LaufN code n origin frame)
    (walk : Rahmen.LaufN code m frame out) : ∃ n, Rahmen.LaufN code n origin out := by
  obtain ⟨n, front⟩ := reach
  exact ⟨n + m, front.trans walk⟩

private theorem loop_budget
    (round : ∀ count frame, LoopHead code origin entry key count frame →
      Binnen code finish frame done ∨
        ∃ next, count = next + 1 ∧
          Binnen code cycle frame (fun out => done out ∨ LoopHead code origin entry key next out))
    (head : LoopHead code origin entry key count frame) :
    Binnen code (finish + count * cycle) frame done := by
  induction count generalizing frame with
  | zero =>
    rcases round 0 frame head with terminal | ⟨next, impossible, _⟩
    · simpa only [Nat.zero_mul, Nat.add_zero] using terminal
    · omega
  | succ count ih =>
    rcases round (count + 1) frame head with ⟨n, out, cost, walk, exit⟩ | ⟨next, eq, h⟩
    · exact ⟨n, out, Nat.le_trans cost (Nat.le_add_right _ _), walk, exit⟩
    have same : next = count := by omega
    subst next
    obtain ⟨n, out, cost, walk, exit | again⟩ := h
    · refine ⟨n, out, ?_, walk, exit⟩
      rw [Nat.succ_mul]
      omega
    · obtain ⟨m, last, rest, tail, exit⟩ := ih again
      refine ⟨n + m, last, ?_, walk.trans tail, exit⟩
      rw [Nat.succ_mul]
      omega

private def TestCut (before : Rahmen) (skip count : Nat) (out : Rahmen) : Prop :=
  ¬ out.Aktiv ∨
    (out.Aktiv ∧ out.pc = before.pc + skip ∧ out.fortsetzungen = before.fortsetzungen) ∨
    ∃ next, count = next + 1 ∧ out.Aktiv ∧ out.pc = before.pc + 1 ∧
      out.fortsetzungen = before.fortsetzungen ∧ out.zaehler before.pc = some next

private theorem pass_cut (frame : Rahmen) (active : frame.Aktiv) (read : frame.zaehler frame.pc = some count)
    (bit : Bool) (skip : Nat) (handler : Option Identifier) :
    TestCut frame skip count (frame.pass bit skip handler) := by
  cases bit
  · exact .inr (.inl ⟨active, rfl, rfl⟩)
  cases count with
  | zero =>
    apply Or.inl
    simp only [Rahmen.pass, Bool.not_true, Bool.false_eq_true, if_false, read, Rahmen.halt,
      Rahmen.Aktiv, reduceCtorEq, false_and, not_false_eq_true]
  | succ n =>
    apply Or.inr
    apply Or.inr
    refine ⟨n, rfl, ?_⟩
    simp only [Rahmen.pass, Bool.not_true, Bool.false_eq_true, if_false, read, Function.update_self,
      and_true, true_and]
    exact active

private theorem halt_inactive (frame : Rahmen) (reason : Abschluss) : ¬ (frame.halt reason).Aktiv := by
  intro live
  have impossible : some reason = none := live.1
  cases impossible

private theorem while_cut (frame : Rahmen) (active : frame.Aktiv)
    (read : frame.zaehler frame.pc = some count) (skip : Nat) (handler : Identifier) :
    TestCut frame skip count ((Befehl.whileTest 0 skip handler).auswerten frame) := by
  simp only [Befehl.auswerten]
  split
  · exact pass_cut frame active read _ _ _
  · exact .inl (halt_inactive frame _)

private theorem for_cut (frame : Rahmen) (active : frame.Aktiv)
    (read : frame.zaehler frame.pc = some count) (skip : Nat) (handler : Option Identifier) :
    TestCut frame skip count ((Befehl.forTest skip handler).auswerten frame) := by
  simp only [Befehl.auswerten, Id.run]
  repeat' first
  | exact .inl (halt_inactive frame _)
  | exact pass_cut frame active read _ _ _
  | split

private theorem loop_round
    (body : SchleifenKoerper code origin 0 code.length (test + 1) back bodyBudget)
    (shape : ∀ pc b, test + 1 ≤ pc → pc ≠ back → code[pc]? = some b → b.rueckweite ≤ pc - (test + 1))
    (head : LoopHead code origin entry test count frame)
    (evaluate : Binnen code evalBudget frame (fun out =>
      ¬ out.Aktiv ∨ out.Aktiv ∧ out.pc = test ∧ out.fortsetzungen = frame.fortsetzungen ∧
        out.zaehler test = some count))
    (testAt : code[test]? = some instruction)
    (classify : ∀ atTest, atTest.Aktiv → atTest.zaehler atTest.pc = some count →
      TestCut atTest skip count (instruction.auswerten atTest))
    (leave : ∀ out, out.Aktiv → out.pc = test + skip →
      out.fortsetzungen.length = origin.fortsetzungen.length →
      Binnen code leaveBudget out (SchleifenAusgang 0 code.length origin))
    (again : ∀ (remaining : Nat) out, out.Aktiv → out.pc = back →
      out.fortsetzungen.length = origin.fortsetzungen.length →
      out.zaehler test = some remaining →
      Binnen code 1 out (fun last => SchleifenAusgang 0 code.length origin last ∨
        last.Aktiv ∧ last.pc = entry ∧ last.fortsetzungen.length = origin.fortsetzungen.length ∧
          last.zaehler test = some remaining)) :
    Binnen code (evalBudget + 1 + leaveBudget) frame (SchleifenAusgang 0 code.length origin) ∨
      ∃ next, count = next + 1 ∧
        Binnen code (evalBudget + 1 + bodyBudget + 1) frame
          (fun out => SchleifenAusgang 0 code.length origin out ∨ LoopHead code origin entry test next out) := by
  obtain ⟨n, atTest, cost, eval, stopped | ⟨live, pc, stack, counter⟩⟩ := evaluate
  · exact .inl ⟨n, atTest, by omega, eval, SchleifenAusgang.stopped stopped⟩
  have testStep := Rahmen.LaufN.eins (first := atTest) live (pc.symm ▸ testAt)
  have through := eval.trans testStep
  let tested := instruction.auswerten atTest
  have reach := reachable_append head.1 through
  rcases classify atTest live (pc.symm ▸ counter) with halted | ⟨live, atExit, same⟩ | ⟨next, countEq, live, atBody, same, remaining⟩
  · exact .inl ⟨n + 1, _, by omega, through, SchleifenAusgang.stopped halted⟩
  · have depth : tested.fortsetzungen.length = origin.fortsetzungen.length := by
      rw [same, stack, head.2.2.2.1]
    obtain ⟨m, out, exitCost, exitWalk, exited⟩ := leave tested live (atExit.trans (by rw [pc])) depth
    exact .inl ⟨n + 1 + m, out, by omega, through.trans exitWalk, exited⟩
  · have depth : tested.fortsetzungen.length = origin.fortsetzungen.length := by
      rw [same, stack, head.2.2.2.1]
    obtain ⟨m, out, bodyCost, run, exited | ⟨live, atBack, depth, countOut⟩⟩ :=
      body.zaehler shape (Nat.lt_succ_self _) reach live (atBody.trans (by rw [pc])) depth
        (pc ▸ remaining)
    · exact .inr ⟨next, countEq, n + 1 + m, out, by omega, through.trans run, .inl exited⟩
    · obtain ⟨k, last, backCost, backStep, done⟩ := again next out live atBack depth countOut
      let steps := (through.trans run).trans backStep
      rcases done with exited | newHead
      · exact .inr ⟨next, countEq, _, last, by omega, steps, .inl exited⟩
      · exact .inr ⟨next, countEq, _, last, by omega, steps, .inr ⟨reachable_append head.1 steps, newHead⟩⟩

private theorem code_lookup_middle (pre : List Befehl) (b : Befehl) (post : List Befehl)
    (atPC : pc = pre.length) : (pre ++ [b] ++ post)[pc]? = some b := by
  simpa only [List.append_assoc, List.singleton_append] using code_lookup pre b post atPC

/-- One closed bound evaluation and setup, followed by at most N+1 tests and N
    body segments. The counter survives calls through the original activation. -/
theorem boundedWhile_terminiert (a : Surface.BoundedWhileArgs scope result) (frame : Rahmen)
    (env : Umgebung scope) (initial : frame.pc = 0) (active : frame.Aktiv)
    (typed : frame.traegt env) (bodyBudget : Nat)
    (checked : frame.WaechterHalten ((boundedWhileForm scope result).fragment a).code)
    (body : let f := (boundedWhileForm scope result).fragment a
      let test := (boundedWhileForm scope result).position a
      SchleifenKoerper f.code frame 0 f.code.length (test + 1) (f.code.length - 1) bodyBudget)
    (condition : let f := (boundedWhileForm scope result).fragment a
      let test := (boundedWhileForm scope result).position a
      ∀ atTest, (∃ n, Rahmen.LaufN f.code n frame atTest) →
        atTest.pc = test → atTest.fortsetzungen.length = frame.fortsetzungen.length →
        atTest.Aktiv → ((atTest.temp 0).bind alsBoolean).isSome = true) :
    let f := (boundedWhileForm scope result).fragment a
    let N := (a.bound.wert env).wert.toNat
    let bound := (expr 0 a.bound).code.length + 1 +
      (N + 1) * ((expr 0 a.condition).code.length + 1) + N * (bodyBudget + 1)
    Binnen f.code bound frame (SchleifenAusgang 0 f.code.length frame) := by
  -- A failed condition read also ends the loop within the test budget.
  clear condition
  let lower := (expr 0 a.bound).code
  let condition := (expr 0 a.condition).code
  let inner := (bracedBlock a.body).code
  let set : Befehl := .setzePasszahl 0 (condition.length + 1)
  let test : Befehl := .whileTest 0 (inner.length + 2) a.overflow
  let jump : Befehl := .zurueckSprung (condition.length + inner.length + 1)
  let setup := lower ++ [set]
  let pre := setup ++ condition
  let bodyPre := pre ++ [test]
  let code := bodyPre ++ inner ++ [jump]
  let N := (a.bound.wert env).wert.toNat
  change Binnen code (lower.length + 1 + (N + 1) * (condition.length + 1) + N * (bodyBudget + 1))
    frame (SchleifenAusgang 0 code.length frame)
  change SchleifenKoerper code frame 0 code.length
    (lower.length + 1 + condition.length + 1) (code.length - 1) bodyBudget at body
  have setupLen : setup.length = lower.length + 1 := by simp only [setup, List.length_append, List.length_singleton]
  have bodyLen : bodyPre.length = pre.length + 1 := by simp only [bodyPre, List.length_append, List.length_singleton]
  have preLen : pre.length = setup.length + condition.length := List.length_append
  have fullLen : code.length = bodyPre.length + inner.length + 1 := by
    simp only [code, List.length_append, List.length_singleton]
  have backPC : code.length - 1 = bodyPre.length + inner.length := by omega
  have closedBody : SchleifenKoerper code frame 0 code.length (pre.length + 1)
      (bodyPre.length + inner.length) bodyBudget := by
    rw [← backPC, preLen, setupLen]
    exact body
  have shape : ∀ pc (instr : Befehl), pre.length + 1 ≤ pc → pc ≠ bodyPre.length + inner.length →
      code[pc]? = some instr → instr.rueckweite ≤ pc - (pre.length + 1) := by
    rw [← bodyLen]
    simpa only [List.append_nil] using
      body_shape bodyPre inner [] jump (braced_rueckkanten a.body) .nil
  change frame.WaechterHalten code at checked
  have lowerChecked : frame.WaechterHalten (lower ++ ([set] ++ condition ++ [test] ++ inner ++ [jump])) := by
    simpa only [code, bodyPre, pre, setup, List.append_assoc] using checked
  obtain ⟨k, atSet, cost, walk, setPC, value, preserved⟩ :=
    expr_laufN 0 a.bound env frame typed active initial ([set] ++ condition ++ [test] ++ inner ++ [jump]) lowerChecked
  change atSet.pc = lower.length at setPC
  change k ≤ lower.length at cost
  have walk' : Rahmen.LaufN code k frame atSet := by
    simpa only [code, bodyPre, pre, setup, lower, List.append_assoc] using walk
  have setAt : code[atSet.pc]? = some set := by
    simpa only [code, bodyPre, pre, setup, List.append_assoc] using
      code_lookup_middle lower set (condition ++ [test] ++ inner ++ [jump]) setPC
  let ready := set.auswerten atSet
  have introWalk := walk'.trans (.eins (active.ausdruck preserved) setAt)
  have readyDef : ready = { atSet with
      pc := atSet.pc + 1
      zaehler := Function.update atSet.zaehler pre.length (some N) } := by
    have target : atSet.pc + (condition.length + 1) = pre.length := by omega
    simp only [ready, set, Befehl.auswerten, Rahmen.zahl, value, Option.bind_some, alsGanzzahl, target, N]
  have depth : atSet.fortsetzungen.length = frame.fortsetzungen.length := by rw [preserved]
  have head : LoopHead code frame setup.length pre.length N ready := by
    refine ⟨⟨_, introWalk⟩, ?_, ?_, ?_, ?_⟩
    · rw [readyDef]
      change atSet.Aktiv
      exact active.ausdruck preserved
    · rw [readyDef]
      change atSet.pc + 1 = setup.length
      omega
    · rw [readyDef]
      exact depth
    · rw [readyDef]
      exact Function.update_self _ _ _
  have oneRound : ∀ count start, LoopHead code frame setup.length pre.length count start →
      Binnen code (condition.length + 1 + 0) start (SchleifenAusgang 0 code.length frame) ∨
      ∃ next, count = next + 1 ∧ Binnen code (condition.length + 1 + bodyBudget + 1) start
        (fun out => SchleifenAusgang 0 code.length frame out ∨ LoopHead code frame setup.length pre.length next out) := by
    intro count start h
    apply loop_round closedBody shape h (evalBudget := condition.length) (leaveBudget := 0)
      (skip := inner.length + 2) (instruction := test)
    · obtain ⟨n, out, budget, run, outcome⟩ := (expr_ausdruckscode 0 a.condition).laufN
        setup ([test] ++ inner ++ [jump]) start h.2.1 (by rw [h.2.2.1]) (by rw [h.2.2.1]; omega)
      refine ⟨n, out, ?_, ?_, ?_⟩
      · change n ≤ setup.length + condition.length - start.pc at budget
        rw [h.2.2.1] at budget
        omega
      · simpa only [code, bodyPre, pre, List.append_assoc] using run
      · rcases outcome with ⟨endPC, same⟩ | stopped
        · refine .inr ⟨h.2.1.ausdruck same, endPC.trans preLen.symm, ?_, ?_⟩
          · rw [same]
          · rw [same]
            exact h.2.2.2.2
        · exact .inl fun active => by rw [active.1] at stopped; cases stopped
    · simpa only [code, bodyPre, List.append_assoc] using
        code_lookup_middle pre test (inner ++ [jump]) rfl
    · exact fun atTest live count => while_cut atTest live count _ _
    · intro out _ pc stack
      exact ⟨0, out, Nat.zero_le _, .null, .inr (.inr (.inr ⟨stack, .inr (by omega)⟩))⟩
    · intro remaining out live pc stack count
      have jumpAt : code[out.pc]? = some jump := by
        simpa only [code, List.append_nil] using code_lookup_middle (bodyPre ++ inner) jump [] (by
          rw [List.length_append]
          exact pc)
      refine ⟨1, jump.auswerten out, Nat.le_refl _, .eins live jumpAt, .inr ⟨live, ?_, stack, count⟩⟩
      change out.pc - (condition.length + inner.length + 1) = setup.length
      omega
  obtain ⟨n, out, budget, run, exited⟩ := loop_budget oneRound head
  refine ⟨k + 1 + n, out, ?_, introWalk.trans run, exited⟩
  have mul : N * (condition.length + 1 + bodyBudget + 1) =
      N * (condition.length + 1) + N * (bodyBudget + 1) := by
    rw [Nat.add_assoc, Nat.mul_add]
  rw [Nat.succ_mul]
  rw [mul] at budget
  omega

private def ForSetupCut (before : Rahmen) (skip count : Nat) (out : Rahmen) : Prop :=
  ¬ out.Aktiv ∨
    (out.pc = before.pc + skip ∧ out.fortsetzungen = before.fortsetzungen) ∨
    (out.Aktiv ∧ out.pc = before.pc + 1 ∧ out.fortsetzungen = before.fortsetzungen ∧
      out.zaehler out.pc = some count)

private theorem for_setup_cut (frame : Rahmen) (active : frame.Aktiv) (a b : Ganzzahl)
    (readA : frame.zahl 0 = some a) (readB : frame.zahl 1 = some b)
    (index : Ty .value) (skip : Nat) (shadow missingHandler : Bool) :
    ForSetupCut frame skip (b.zahl.wert - a.zahl.wert).toNat
      ((Befehl.forAnfang 0 1 index skip shadow missingHandler).auswerten frame) := by
  simp only [Befehl.auswerten, Id.run, readA, readB]
  repeat' first
  | exact .inl (halt_inactive frame _)
  | exact .inr (.inl ⟨rfl, rfl⟩)
  | exact .inr (.inr ⟨active, rfl, rfl, Function.update_self _ _ _⟩)
  | split

private theorem for_back_cut (frame : Rahmen) (active : frame.Aktiv) (jump : Nat) (index : Ty .value) :
    let out := (Befehl.forNaechster jump index).auswerten frame
    ¬ out.Aktiv ∨ (out.Aktiv ∧ out.pc = frame.pc - jump ∧
      out.fortsetzungen = frame.fortsetzungen ∧ out.zaehler = frame.zaehler) := by
  simp only [Befehl.auswerten, Id.run]
  repeat' first
  | exact .inl (halt_inactive frame _)
  | exact .inr ⟨active, rfl, rfl, rfl⟩
  | split

/-- A half-open range evaluates its endpoints once. At most N tests admit a
    body, and each admits one increment before the final test or exit. -/
theorem forRange_terminiert (a : Surface.ForRangeArgs scope result) (frame : Rahmen)
    (env : Umgebung scope) (initial : frame.pc = 0) (active : frame.Aktiv)
    (typed : frame.traegt env) (bodyBudget : Nat)
    (checked : frame.WaechterHalten ((forRangeForm scope result).fragment a).code)
    (body : let f := (forRangeForm scope result).fragment a
      let test := (forRangeForm scope result).position a
      SchleifenKoerper f.code frame 0 f.code.length (test + 1) (f.code.length - 2) bodyBudget)
    (backEdge : let f := (forRangeForm scope result).fragment a
      ∀ back, (∃ n, Rahmen.LaufN f.code n frame back) →
        back.pc = f.code.length - 2 → back.fortsetzungen.length = frame.fortsetzungen.length →
        back.Aktiv → ∀ instruction, f.code[back.pc]? = some instruction →
        (instruction.auswerten back).Aktiv) :
    let f := (forRangeForm scope result).fragment a
    let N := ((a.upper.wert env).wert - (a.lower.wert env).wert).toNat
    let bound := (expr 0 a.lower).code.length + (expr 1 a.upper).code.length + 3 + N * (bodyBudget + 2)
    Binnen f.code bound frame (SchleifenAusgang 0 f.code.length frame) := by
  -- An increment that stops the frame also spends at most one instruction.
  clear backEdge
  let low := (expr 0 a.lower).code
  let high := (expr 1 a.upper).code
  let inner := (bracedBlock a.body).code
  let index := (rangeBinding a.name a.lo a.hi).type
  let uses := BracedBlock.rangeUses a.name a.body
  let set : Befehl := .forAnfang 0 1 index (inner.length + 4) uses.1 (uses.2 && a.overflow.isNone)
  let test : Befehl := .forTest (inner.length + 2) a.overflow
  let jump : Befehl := .forNaechster (inner.length + 1) index
  let pop : Befehl := .blockEnde 1
  let endpoints := low ++ high
  let pre := endpoints ++ [set]
  let bodyPre := pre ++ [test]
  let code := bodyPre ++ inner ++ [jump] ++ [pop]
  let N := ((a.upper.wert env).wert - (a.lower.wert env).wert).toNat
  change Binnen code (low.length + high.length + 3 + N * (bodyBudget + 2))
    frame (SchleifenAusgang 0 code.length frame)
  change SchleifenKoerper code frame 0 code.length
    (low.length + high.length + 1 + 1) (code.length - 2) bodyBudget at body
  have endLen : endpoints.length = low.length + high.length := List.length_append
  have testLen : pre.length = endpoints.length + 1 := by simp only [pre, List.length_append, List.length_singleton]
  have bodyLen : bodyPre.length = pre.length + 1 := by simp only [bodyPre, List.length_append, List.length_singleton]
  have fullLen : code.length = bodyPre.length + inner.length + 2 := by
    simp only [code, List.length_append, List.length_singleton, Nat.add_assoc, Nat.reduceAdd]
  have backPC : code.length - 2 = bodyPre.length + inner.length := by omega
  have closedBody : SchleifenKoerper code frame 0 code.length (pre.length + 1)
      (bodyPre.length + inner.length) bodyBudget := by
    rw [← backPC, testLen, endLen]
    exact body
  have shape : ∀ pc (instr : Befehl), pre.length + 1 ≤ pc → pc ≠ bodyPre.length + inner.length →
      code[pc]? = some instr → instr.rueckweite ≤ pc - (pre.length + 1) := by
    rw [← bodyLen]
    exact body_shape bodyPre inner [pop] jump (braced_rueckkanten a.body) (.single rfl)
  let rest := [set] ++ [test] ++ inner ++ [jump] ++ [pop]
  change frame.WaechterHalten code at checked
  have lowChecked : frame.WaechterHalten (low ++ (high ++ rest)) := by
    simpa only [code, bodyPre, pre, endpoints, rest, List.append_assoc] using checked
  obtain ⟨l, mid, lCost, lowRun, midPC, lowValue, midSame⟩ :=
    expr_laufN 0 a.lower env frame typed active initial (high ++ rest) lowChecked
  have highChecked : mid.WaechterHalten (low ++ high ++ rest) := by
    simpa only [List.append_assoc] using lowChecked.after lowRun.lauf
  obtain ⟨h, atSet, hCost, highRun, setPC, highValue, setSame, earlier⟩ :=
    expr_laufN_am 1 a.upper env mid (Rahmen.traegt_ausdruck typed midSame)
      (active.ausdruck midSame) low rest midPC highChecked
  change l ≤ low.length at lCost
  change h ≤ high.length at hCost
  have atEndpoints : atSet.pc = endpoints.length := setPC.trans endLen.symm
  have lowRun' : Rahmen.LaufN code l frame mid := by
    simpa only [code, bodyPre, pre, endpoints, rest, low, List.append_assoc] using lowRun
  have highRun' : Rahmen.LaufN code h mid atSet := by
    simpa only [code, bodyPre, pre, endpoints, rest, high, List.append_assoc] using highRun
  have setLive := (active.ausdruck midSame).ausdruck setSame
  have depth : atSet.fortsetzungen.length = frame.fortsetzungen.length := by rw [setSame, midSame]
  have setAt : code[atSet.pc]? = some set := by
    simpa only [code, bodyPre, pre, List.append_assoc] using
      code_lookup_middle endpoints set ([test] ++ inner ++ [jump] ++ [pop]) atEndpoints
  let ready := set.auswerten atSet
  have introWalk := (lowRun'.trans highRun').trans (.eins setLive setAt)
  let aLow : Ganzzahl := ⟨a.lo, a.loHi, a.lower.wert env⟩
  let aHigh : Ganzzahl := ⟨a.hiLo, a.hi, a.upper.wert env⟩
  have readLow : atSet.zahl 0 = some aLow := by
    rw [Rahmen.zahl, earlier 0 (Nat.zero_lt_succ _), lowValue]
    rfl
  have readHigh : atSet.zahl 1 = some aHigh := by rw [Rahmen.zahl, highValue]; rfl
  have setupCut : ForSetupCut atSet (inner.length + 4) N ready :=
    for_setup_cut atSet setLive aLow aHigh readLow readHigh index _ uses.1 _
  rcases setupCut with halted | ⟨emptyPC, emptyStack⟩ | ⟨live, readyPC, readyStack, counter⟩
  · exact ⟨l + h + 1, ready, by omega, introWalk, SchleifenAusgang.stopped halted⟩
  · refine ⟨l + h + 1, ready, by omega, introWalk, .inr (.inr (.inr ⟨?_, .inr ?_⟩))⟩
    · rw [emptyStack, depth]
    · change atSet.pc = low.length + high.length at setPC
      omega
  have entryPC : ready.pc = pre.length := by
    change atSet.pc = low.length + high.length at setPC
    omega
  have head : LoopHead code frame pre.length pre.length N ready := by
    exact ⟨⟨_, introWalk⟩, live, entryPC, (congrArg List.length readyStack).trans depth,
      entryPC ▸ counter⟩
  have oneRound : ∀ count start, LoopHead code frame pre.length pre.length count start →
      Binnen code (0 + 1 + 1) start (SchleifenAusgang 0 code.length frame) ∨
      ∃ next, count = next + 1 ∧ Binnen code (0 + 1 + bodyBudget + 1) start
        (fun out => SchleifenAusgang 0 code.length frame out ∨ LoopHead code frame pre.length pre.length next out) := by
    intro count start head
    apply loop_round closedBody shape head (evalBudget := 0) (leaveBudget := 1) (skip := inner.length + 2) (instruction := test)
    · exact ⟨0, start, Nat.le_refl _, .null, .inr ⟨head.2.1, head.2.2.1, rfl, head.2.2.2.2⟩⟩
    · simpa only [code, bodyPre, List.append_assoc] using
        code_lookup_middle pre test (inner ++ [jump] ++ [pop]) rfl
    · exact fun atTest live count => for_cut atTest live count _ _
    · intro out live pc stack
      let front := bodyPre ++ inner ++ [jump]
      have atPop : out.pc = front.length := by
        simp only [front, List.length_append, List.length_singleton]
        omega
      have popAt : code[out.pc]? = some pop := by
        simpa only [code, front, List.append_nil] using code_lookup_middle front pop [] atPop
      refine ⟨1, pop.auswerten out, Nat.le_refl _, .eins live popAt,
        .inr (.inr (.inr ⟨stack, .inr ?_⟩))⟩
      change code.length ≤ out.pc + 1
      omega
    · intro remaining out live pc stack count
      have jumpAt : code[out.pc]? = some jump :=
        code_lookup_middle (bodyPre ++ inner) jump [pop] (pc.trans List.length_append.symm)
      have step := Rahmen.LaufN.eins live jumpAt
      refine ⟨1, jump.auswerten out, Nat.le_refl _, step, ?_⟩
      rcases for_back_cut out live (inner.length + 1) index with halted | ⟨live, ret, same, counts⟩
      · exact .inl (SchleifenAusgang.stopped halted)
      · refine .inr ⟨live, ?_, (congrArg List.length same).trans stack, counts ▸ count⟩
        change ((Befehl.forNaechster (inner.length + 1) index).auswerten out).pc = pre.length
        rw [ret]
        omega
  obtain ⟨n, out, budget, run, exited⟩ := loop_budget oneRound head
  refine ⟨l + h + 1 + n, out, ?_, introWalk.trans run, exited⟩
  simp only [Nat.zero_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.reduceAdd] at budget ⊢
  omega

end Gabbro.Core.Ast.Semantik
