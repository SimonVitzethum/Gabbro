module

public import Core.Ast.Semantik.Runtime.ExpressionOperators
public import Core.Ast.Semantik.Runtime.ExpressionAggregates

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

private theorem expr_bewacht (tree : Expr scope type) (env : Umgebung scope) :
    ∀ slot, Ausdruckswert env slot tree := by
  refine @Expr.rec scope
    (fun _ tree => ∀ slot, Ausdruckswert env slot tree)
    (fun types items => ∀ slot, BewachterAusdruck env slot (itemCode slot items).code
      (fun _ => True) (ExpressionAggregates.TupleTemps slot types (items.wert env)))
    (fun _ types items => ∀ slot, BewachterAusdruck env slot (labeledCode slot items).code
      (fun _ => True) (ExpressionAggregates.TupleTemps slot types (items.wert env)))
    (fun type payload => ∀ slot, BewachterAusdruck env slot (caseCode slot payload).code
      (fun _ => True) (ExpressionAggregates.CaseTemp (type := type) slot (payload.wert env)))
    ?lit ?binary ?trueLit ?falseLit ?«variable» ?negativeLit ?neg ?not ?div ?compare ?logic
    ?arrayValue ?arrayIndex ?tupleValue ?tupleField ?recordValue ?recordField ?variantValue
    ?textLiteral ?textConcat ?textIndex ?substring ?textLength ?optionIsSome
    ?itemsEmpty ?itemsNext ?labeledEmpty ?labeledNext ?payloadNullary ?payloadValue type tree
  case lit => intro value slot; exact ExpressionOperators.literal value
  case binary =>
    intros
    rename_i op left right leftIH rightIH slot
    exact ExpressionOperators.arithmetic op (leftIH slot) (rightIH (slot + 1))
  case trueLit => intro slot; exact ExpressionOperators.trueLiteral
  case falseLit => intro slot; exact ExpressionOperators.falseLiteral
  case «variable» =>
    intros
    rename_i ref visible ordinary slot
    exact ExpressionOperators.variableRead ref visible ordinary
  case negativeLit => intro value slot; exact ExpressionOperators.negativeLiteral value
  case neg => intros; rename_i ih slot; exact ExpressionOperators.neg (ih slot)
  case not => intros; rename_i ih slot; exact ExpressionOperators.not (ih slot)
  case div =>
    intros
    rename_i nonzero leftIH rightIH slot
    exact ExpressionOperators.divide (leftIH slot) (rightIH (slot + 1)) nonzero
  case compare =>
    intros
    rename_i op left right leftIH rightIH slot
    exact ExpressionOperators.compare op (leftIH slot) (rightIH (slot + 1))
  case logic =>
    intros
    rename_i op left right leftIH rightIH slot
    exact ExpressionOperators.logic op (leftIH slot) (rightIH slot)
  case arrayValue =>
    intros
    rename_i principal fits ih slot
    exact ExpressionAggregates.arrayValue principal fits (ih slot)
  case arrayIndex =>
    intros
    rename_i lower upper baseIH indexIH slot
    exact ExpressionAggregates.arrayIndex lower upper (baseIH slot) (indexIH (slot + 1))
  case tupleValue =>
    intros
    rename_i firstIH secondIH tailIH slot
    exact ExpressionAggregates.tupleValue (firstIH slot) (secondIH (slot + 1)) (tailIH (slot + 2))
  case tupleField =>
    intros
    rename_i index ih slot
    exact ExpressionAggregates.tupleField (ih slot) index
  case recordValue =>
    intros
    rename_i ref items fields fits ih slot
    exact ExpressionAggregates.recordValue ref items fields fits (ih slot)
  case recordField =>
    intros
    rename_i field index written ih slot
    exact ExpressionAggregates.recordField (ih slot) field index written
  case variantValue =>
    intros
    rename_i ref label index written ordinary available payload ih slot
    exact ExpressionAggregates.variantValue ref label index written ordinary available payload (ih slot)
  case textLiteral => intro decoded slot; exact ExpressionOperators.textLiteral decoded
  case textConcat =>
    intros
    rename_i leftIH rightIH slot
    exact ExpressionOperators.textConcat (leftIH slot) (rightIH (slot + 1))
  case textIndex =>
    intros
    rename_i baseIH offsetIH slot
    exact ExpressionOperators.textIndex (baseIH slot) (offsetIH (slot + 1))
  case substring =>
    intros
    rename_i baseIH firstIH lastIH slot
    exact ExpressionOperators.substring (baseIH slot) (firstIH (slot + 1)) (lastIH (slot + 2))
  case textLength => intros; rename_i ih slot; exact ExpressionOperators.textLength (ih slot)
  case optionIsSome =>
    intros
    rename_i ref visible ordinary slot
    exact ExpressionOperators.optionIsSome ref visible ordinary
  case itemsEmpty => intro slot; exact ExpressionAggregates.itemsNil
  case itemsNext =>
    intros
    rename_i headIH tailIH slot
    exact ExpressionAggregates.itemsCons (headIH slot) (tailIH (slot + 1))
  case labeledEmpty => intro slot; exact ExpressionAggregates.labeledNil
  case labeledNext =>
    intros
    rename_i label head tail headIH tailIH slot
    exact ExpressionAggregates.labeledCons label (headIH slot) (tailIH (slot + 1))
  case payloadNullary => intro parens slot; exact ExpressionAggregates.caseNullary parens
  case payloadValue =>
    intros
    rename_i ih slot
    exact ExpressionAggregates.caseValue (ih slot)

/-- Evaluate an expression at its actual address with all reached guards checked. -/
theorem expr_ergebnis_typ_am (slot : Nat) (tree : Expr scope type)
    (env : Umgebung scope) (frame : Rahmen) (bound : frame.traegt env)
    (active : frame.Aktiv) (pre post : List Befehl) (entry : frame.pc = pre.length)
    (checked : frame.WaechterHalten (pre ++ (expr slot tree).code ++ post)) :
    ∃ out, Ausdrucksabschnitt (pre ++ (expr slot tree).code ++ post)
      (pre.length + (expr slot tree).code.length) slot frame out ∧ out.temp slot = some ⟨type, tree.wert env⟩ :=
  expr_bewacht tree env slot pre post frame entry active bound checked trivial

theorem expr_ergebnis_typ (slot : Nat) (tree : Expr scope type) (env : Umgebung scope)
    (frame : Rahmen) (bound : frame.traegt env) (active : frame.rueckgabe = none)
    (running : frame.stopp = none) (atStart : frame.pc = 0)
    (checked : frame.WaechterHalten (expr slot tree).code) :
    ∃ out, Rahmen.Lauf (expr slot tree).code frame out ∧
      out.pc = (expr slot tree).code.length ∧ out.temp slot = some ⟨type, tree.wert env⟩ ∧
      out.lokale = frame.lokale ∧ out.rueckgabe = none ∧
      ∀ i, i < slot → out.temp i = frame.temp i := by
  obtain ⟨out, trace, value⟩ := expr_ergebnis_typ_am slot tree env frame bound ⟨running, active⟩ [] [] atStart
    (by simpa only [List.nil_append, List.append_nil] using checked)
  exact ⟨out, by simpa only [List.nil_append, List.append_nil] using trace.walk,
    by simpa only [List.length_nil, Nat.zero_add] using trace.position, value,
    congrArg Rahmen.lokale trace.frame, (trace.aktiv ⟨running, active⟩).2, trace.lower⟩

end Gabbro.Core.Ast.Semantik
