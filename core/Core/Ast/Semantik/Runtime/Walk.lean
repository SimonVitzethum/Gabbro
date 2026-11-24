module

public import Core.Ast.Semantik.Runtime.ExpressionCode
public import Core.Annahme.Waechter

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- The frame relation for expression evaluation uses the resolved de Bruijn slot
    and carries the typed incoming value at every visible binding. -/
def Rahmen.traegt (frame : Rahmen) (env : Umgebung scope) : Prop :=
  ∀ {type} (ref : Local scope type), frame.lokale[ref.index]? = some (some ⟨type, env ref⟩)

def Rahmen.Schritt (code : List Befehl) (before after : Rahmen) : Prop :=
  ∃ b, before.stopp = none ∧ before.rueckgabe = none ∧
    code[before.pc]? = some b ∧ after = b.auswerten before

inductive Rahmen.Lauf (code : List Befehl) : Rahmen → Rahmen → Prop where
  | start : Lauf code frame frame
  | schritt : Lauf code before middle → Schritt code middle after → Lauf code before after

/-- The source guards hold at every live instruction reached during this evaluation. -/
def Rahmen.WaechterHalten (code : List Befehl) (frame : Rahmen) : Prop :=
  ∀ reached, Rahmen.Lauf code frame reached → reached.stopp = none → reached.rueckgabe = none →
    ∀ b, code[reached.pc]? = some b → ∀ g : Bedarf, b.guard reached = some g →
      Annahme.waechterBedarf g.1 g.2

/-- A running frame has neither stopped nor returned. -/
def Rahmen.Aktiv (frame : Rahmen) : Prop := frame.stopp = none ∧ frame.rueckgabe = none

theorem Rahmen.Lauf.trans (left : Rahmen.Lauf code first middle)
    (right : Rahmen.Lauf code middle last) : Rahmen.Lauf code first last := by
  induction right with
  | start => exact left
  | schritt _ step ih => exact .schritt ih step

theorem Rahmen.Lauf.appendCode (walk : Rahmen.Lauf code first last) (suffix : List Befehl) :
    Rahmen.Lauf (code ++ suffix) first last := by
  induction walk with
  | start => exact .start
  | schritt _ step ih =>
    obtain ⟨instruction, live, active, lookup, rfl⟩ := step
    have inside := (List.getElem?_eq_some_iff.mp lookup).1
    have appended := (List.getElem?_append_left (l₂ := suffix) inside).trans lookup
    exact .schritt ih ⟨instruction, live, active, appended, rfl⟩

theorem Rahmen.WaechterHalten.after (checked : first.WaechterHalten code)
    (walk : Rahmen.Lauf code first middle) : middle.WaechterHalten code := by
  intro frame reached running active instruction lookup demand guard
  exact checked frame (walk.trans reached) running active instruction lookup demand guard

theorem Rahmen.WaechterHalten.prefix (checked : frame.WaechterHalten (code ++ suffix)) :
    frame.WaechterHalten code := by
  intro current reached running active instruction lookup demand guard
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  have appended := (List.getElem?_append_left (l₂ := suffix) inside).trans lookup
  exact checked current (reached.appendCode suffix) running active instruction appended demand guard

end Gabbro.Core.Ast.Semantik
