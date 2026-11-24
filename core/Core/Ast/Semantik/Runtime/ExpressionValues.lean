module

public import Core.Ast.Semantik.Runtime.ExpressionTrace

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- The observation shared by every typed expression. -/
def TemporaryValue (slot : Nat) {type : Ty .value} (value : Wert type) (frame : Rahmen) : Prop :=
  frame.temp slot = some ⟨type, value⟩

abbrev Ausdruckswert (env : Umgebung scope) (slot : Nat) (tree : Expr scope type) : Prop :=
  BewachterAusdruck env slot (expr slot tree).code (fun _ => True) (TemporaryValue slot (tree.wert env))

theorem BewachterAusdruck.eingang
    (read : BewachterAusdruck env slot code ready observed)
    (admitFrame : ∀ before, stronger before → ready before) :
    BewachterAusdruck env slot code stronger observed := by
  intro pre post before position running typed checked entry
  exact read pre post before position running typed checked (admitFrame before entry)

theorem BewachterAusdruck.wert {type : Ty .value} (value : Wert type)
    (eval : ∀ pre post (before : Rahmen), before.pc = pre.length → before.Aktiv → before.traegt env →
      before.WaechterHalten (pre ++ [instruction] ++ post) → ready before →
      instruction.auswerten before = before.schreibe slot (some ⟨type, value⟩)) :
    BewachterAusdruck env slot [instruction] ready (TemporaryValue slot value) :=
  .schreibe (fun _ => ⟨type, value⟩) eval (fun _ _ => Function.update_self _ _ _)

theorem BewachterAusdruck.einOperand
    (operand : Ausdruckswert env slot tree) (value : Wert type)
    (eval : ∀ pre post (before : Rahmen), before.pc = pre.length → before.Aktiv → before.traegt env →
      before.WaechterHalten (pre ++ [instruction] ++ post) →
      TemporaryValue slot (tree.wert env) before →
      instruction.auswerten before = before.schreibe slot (some ⟨type, value⟩)) :
    BewachterAusdruck env slot ((expr slot tree).code ++ [instruction])
      (fun _ => True) (TemporaryValue slot value) :=
  .anhaengen operand (.wert value eval) (Nat.le_refl _) (fun _ _ _ found _ => found)

theorem BewachterAusdruck.zweiOperanden
    (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    BewachterAusdruck env slot ((expr slot a).code ++ (expr (slot + 1) b).code)
      (fun _ => True)
      (fun frame => TemporaryValue slot (a.wert env) frame ∧ TemporaryValue (slot + 1) (b.wert env) frame) := by
  refine .anhaengen left (right.eingang (fun _ _ => trivial)) (Nat.le_succ _) ?_
  intro middle after first second preserve
  exact ⟨(preserve slot (Nat.lt_succ_self _)).trans first, second⟩

theorem BewachterAusdruck.zweiOperandenWert
    (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) (value : Wert type)
    (eval : ∀ pre post (before : Rahmen), before.pc = pre.length → before.Aktiv → before.traegt env →
      before.WaechterHalten (pre ++ [instruction] ++ post) →
      (TemporaryValue slot (a.wert env) before ∧ TemporaryValue (slot + 1) (b.wert env) before) →
      instruction.auswerten before = before.schreibe slot (some ⟨type, value⟩)) :
    BewachterAusdruck env slot (((expr slot a).code ++ (expr (slot + 1) b).code) ++ [instruction])
      (fun _ => True) (TemporaryValue slot value) :=
  .anhaengen (.zweiOperanden left right) (.wert value eval) (Nat.le_refl _) (fun _ _ _ found _ => found)

theorem codeLookup_instruction {frame : Rahmen} {pre post : List Befehl} {instruction : Befehl} (position : frame.pc = pre.length) :
    (pre ++ [instruction] ++ post)[frame.pc]? = some instruction := by
  rw [position, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem guardOfInstruction {frame : Rahmen} {pre post : List Befehl} {instruction : Befehl} {demand : Bedarf} (position : frame.pc = pre.length) (active : frame.Aktiv)
    (checked : frame.WaechterHalten (pre ++ [instruction] ++ post))
    (guard : instruction.guard frame = some demand) :
    Annahme.waechterBedarf demand.1 demand.2 :=
  checked frame .start active.1 active.2 instruction (codeLookup_instruction position) demand guard

end Gabbro.Core.Ast.Semantik
