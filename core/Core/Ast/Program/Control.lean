module

public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Only back-edge instructions can decrease the program counter of a running
    activation. The distance is measured from the instruction itself. -/
def Befehl.rueckweite : Befehl → Nat
  | .zurueckSprung distance | .forNaechster distance _ => distance
  | _ => 0

/-- An expression instruction advances within its remaining code, changing only
    the program counter and temporary slots, or stops on an invalid operand. -/
def Befehl.Ausdrucksschritt (b : Befehl) (room : Nat) : Prop :=
  b.rueckweite = 0 ∧ ∀ frame, let out := b.auswerten frame
    (frame.pc < out.pc ∧ out.pc ≤ frame.pc + room ∧
      out = { frame with pc := out.pc, temp := out.temp }) ∨ out = frame.halt .ungueltigerWert

def Ausdruckscode (code : List Befehl) : Prop :=
  ∀ i (b : Befehl), code[i]? = some b → b.Ausdrucksschritt (code.length - i)

theorem Ausdruckscode.nil : Ausdruckscode [] := by
  intro i b lookup
  simp only [List.getElem?_nil, reduceCtorEq] at lookup

theorem Ausdruckscode.cons (head : b.Ausdrucksschritt (1 + tail.length))
    (rest : Ausdruckscode tail) : Ausdruckscode (b :: tail) := by
  intro i instruction lookup
  cases i with
  | zero =>
    have same : b = instruction := Option.some.inj lookup
    subst instruction
    simpa only [List.length_cons, Nat.sub_zero, Nat.add_comm] using head
  | succ i =>
    have h := rest i instruction lookup
    simpa only [List.length_cons, Nat.add_sub_add_right] using h

theorem Ausdruckscode.append (left : Ausdruckscode a) (right : Ausdruckscode b) :
    Ausdruckscode (a ++ b) := by
  intro i instruction lookup
  by_cases before : i < a.length
  · rw [List.getElem?_append_left before] at lookup
    obtain ⟨forward, step⟩ := left i instruction lookup
    refine ⟨forward, fun frame => ?_⟩
    rcases step frame with ⟨advances, within, preserves⟩ | stopped
    · refine .inl ⟨advances, ?_, preserves⟩
      simp only [List.length_append]
      omega
    · exact .inr stopped
  · rw [List.getElem?_append_right (Nat.le_of_not_gt before)] at lookup
    obtain ⟨forward, step⟩ := right _ instruction lookup
    refine ⟨forward, fun frame => ?_⟩
    rcases step frame with ⟨advances, within, preserves⟩ | stopped
    · refine .inl ⟨advances, ?_, preserves⟩
      simp only [List.length_append]
      omega
    · exact .inr stopped

private theorem expression_singleton (h : b.Ausdrucksschritt 1) : Ausdruckscode [b] :=
  .cons h .nil

private theorem expression_branch (slot : Nat) (bit : Bool) (tail : List Befehl)
    (right : Ausdruckscode tail) : Ausdruckscode (.springeWenn slot bit (tail.length + 1) :: tail) := by
  refine .cons ⟨rfl, fun frame => .inl ?_⟩ right
  change frame.pc < frame.pc + (if (frame.temp slot).bind alsBoolean = some bit then tail.length + 1 else 1) ∧ _
  constructor
  · split <;> omega
  constructor
  · change frame.pc + (if (frame.temp slot).bind alsBoolean = some bit then tail.length + 1 else 1) ≤ _
    split <;> omega
  · cases frame
    rfl

private theorem expression_at_slot (tree : Expr scope type) : ∀ slot,
    Ausdruckscode (expr slot tree).code := by
  refine @Expr.rec scope
    (fun _ t => ∀ slot, Ausdruckscode (expr slot t).code)
    (fun _ t => ∀ slot, Ausdruckscode (itemCode slot t).code)
    (fun _ _ t => ∀ slot, Ausdruckscode (labeledCode slot t).code)
    (fun _ t => ∀ slot, Ausdruckscode (caseCode slot t).code)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ type tree
  all_goals
    intros
    simp only [expr, itemCode, labeledCode, caseCode, Fragment.anhaengen, Fragment.einzel]
  all_goals
    first
    | exact .nil
    | rw [List.append_assoc, List.singleton_append]
      apply Ausdruckscode.append
      · solve_by_elim
      · apply expression_branch
        solve_by_elim
    | apply_rules [Ausdruckscode.append, expression_singleton]
      all_goals
        refine ⟨rfl, fun frame => ?_⟩
        first
        | exact .inl ⟨Nat.lt_succ_self _, Nat.le_refl _, by cases frame; rfl⟩
        | simp only [Befehl.auswerten, Id.run]
          repeat' first
            | exact .inr rfl
            | exact .inl ⟨Nat.lt_succ_self _, Nat.le_refl _, by cases frame; rfl⟩
            | split

theorem expr_ausdruckscode (slot : Nat) (tree : Expr scope type) :
    Ausdruckscode (expr slot tree).code :=
  expression_at_slot tree slot

def RueckkantenImCode (code : List Befehl) : Prop :=
  ∀ i (b : Befehl), code[i]? = some b → b.rueckweite ≤ i

theorem RueckkantenImCode.nil : RueckkantenImCode [] := by
  intro i b lookup
  simp only [List.getElem?_nil, reduceCtorEq] at lookup

theorem RueckkantenImCode.snoc (left : RueckkantenImCode a) (back : b.rueckweite ≤ a.length) :
    RueckkantenImCode (a ++ [b]) := by
  intro i instruction lookup
  by_cases before : i < a.length
  · exact left i instruction ((List.getElem?_append_left before).symm.trans lookup)
  · have within := (List.getElem?_eq_some_iff.mp lookup).1
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at within
    have atEnd : i = a.length := by omega
    subst i
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at lookup
    cases lookup
    exact back

theorem RueckkantenImCode.single (h : b.rueckweite = 0) : RueckkantenImCode [b] :=
  RueckkantenImCode.snoc RueckkantenImCode.nil (by rw [h]; exact Nat.zero_le _)

theorem RueckkantenImCode.append (left : RueckkantenImCode a) (right : RueckkantenImCode b) :
    RueckkantenImCode (a ++ b) := by
  intro i instruction lookup
  by_cases before : i < a.length
  · exact left i instruction ((List.getElem?_append_left before).symm.trans lookup)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt before)] at lookup
    exact Nat.le_trans (right _ instruction lookup) (Nat.sub_le _ _)

theorem Ausdruckscode.rueckkanten (code : Ausdruckscode a) : RueckkantenImCode a := by
  intro i b lookup
  rw [(code i b lookup).1]
  exact Nat.zero_le _

private theorem argsCode_rueckkanten (slot : Nat) (args : List (TypedExpr scope)) :
    RueckkantenImCode (argsCode slot args).code := by
  induction args generalizing slot with
  | nil => exact .nil
  | cons head tail ih => exact .append (expr_ausdruckscode slot head.2).rueckkanten (ih _)

private theorem expr_no_back (slot : Nat) (tree : Expr scope type) :
    RueckkantenImCode (expr slot tree).code :=
  (expr_ausdruckscode slot tree).rueckkanten

private theorem optionCode_rueckkanten (slot : Nat) (value : OptionInitializer scope count) :
    RueckkantenImCode (optionCode slot value).code := by
  cases value with
  | absent => exact .single rfl
  | present value _ => exact .snoc (expr_no_back slot value) (Nat.zero_le _)

theorem braced_rueckkanten (tree : BracedBlock result before) :
    RueckkantenImCode (bracedBlock tree).code := by
  refine @BracedBlock.rec result
    (fun _ _ t => RueckkantenImCode (stmt t).code)
    (fun _ _ t => RueckkantenImCode (block t).code)
    (fun _ t => RueckkantenImCode (bracedBlock t).code)
    (fun _ _ _ _ t => RueckkantenImCode (variantArms t).body.code)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before tree
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intro scope cond yes no yesOK noOK
    exact .append (.snoc (.append (.snoc (expr_no_back 0 cond) (Nat.zero_le _)) yesOK)
      (Nat.zero_le _)) noOK
  · intros
    exact .single rfl
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (argsCode_rueckkanten 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (argsCode_rueckkanten 0 _) (Nat.zero_le _)
  · intro scope lo hi cond bound static nonnegative handler body bodyOK
    refine .snoc (.append (.snoc (.append (.snoc (expr_no_back 0 bound) (Nat.zero_le _))
      (expr_no_back 0 cond)) (Nat.zero_le _)) bodyOK) ?_
    simp only [Befehl.rueckweite, Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_singleton]
    omega
  · intro scope lo loHi hiLo hi name ordinary low high static handler body bodyOK
    refine .snoc (.snoc (.append (.snoc (.snoc (.append (expr_no_back 0 low) (expr_no_back 1 high))
      (Nat.zero_le _)) (Nat.zero_le _)) bodyOK) ?_) (Nat.zero_le _)
    simp only [Befehl.rueckweite, Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_singleton]
    omega
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (expr_no_back 0 _) (Nat.zero_le _)
  · intros
    exact .append (.snoc (expr_no_back 0 _) (Nat.zero_le _)) ‹RueckkantenImCode _›
  · intros
    exact .snoc (optionCode_rueckkanten 0 _) (Nat.zero_le _)
  · intros
    exact .snoc (optionCode_rueckkanten 0 _) (Nat.zero_le _)
  · intros
    exact .single rfl
  · intro scope label body bodyOK
    exact .snoc bodyOK (Nat.le_refl _)
  · intro scope after form
    cases form with
    | load _ _ _ _ _ _ _ index _ =>
      exact .snoc (.snoc (expr_no_back 0 index) (Nat.zero_le _)) (Nat.zero_le _)
    | store _ _ _ index value _ =>
      exact .snoc (.append (expr_no_back 0 index) (expr_no_back 1 value)) (Nat.zero_le _)
  · intros
    exact .nil
  · intro before middle after head rest headOK restOK
    exact .append headOK restOK
  · intro before after body bodyOK
    exact .snoc bodyOK (Nat.zero_le _)
  · intros
    exact .nil
  · intro scope allow labels payloads label valid body rest bodyOK restOK
    exact .append (.snoc bodyOK (Nat.zero_le _)) restOK
  · intro scope allow labels payloads type label binder ordinary body rest bodyOK restOK
    exact .append (.snoc (.snoc bodyOK (Nat.zero_le _)) (Nat.zero_le _)) restOK
  · intros
    assumption

end Gabbro.Core.Ast.Semantik
