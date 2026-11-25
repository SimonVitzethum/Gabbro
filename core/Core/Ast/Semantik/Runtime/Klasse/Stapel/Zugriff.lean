/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Stapel/Zugriff.lean
  Subject:   Stack effect of the access instructions (MK-04). An access instruction binds the value it read
             into a temporary (`Rahmen.schreibe`), halts the frame, or advances the program counter; none of
             these touches the continuation stack, so the stack is unchanged, as the classes `lesen`,
             `schreiben` and `rmw` promise (`Wirkungsklasse.Stapel`).
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Stapel.Form
public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Binding the value read never changes the continuation stack. -/
theorem Rahmen.bindeGelesen_fortsetzungen (r : Rahmen) (ziel : Nat) (typ : Ty .value) (gelesen : Int) :
    (r.bindeGelesen ziel typ gelesen).fortsetzungen = r.fortsetzungen := by
  unfold Rahmen.bindeGelesen
  split <;> rfl

/-- The frame transfer of an access instruction never changes the continuation stack. -/
theorem Zugriffsform.uebertrag_fortsetzungen (z : Zugriffsform) (r : Rahmen) (gelesen : Int) :
    (z.uebertrag r gelesen).fortsetzungen = r.fortsetzungen := by
  cases z with
  | erwarte ziel region index erwartet typ modus =>
    simp only [Zugriffsform.uebertrag]
    split
    · exact r.bindeGelesen_fortsetzungen _ _ _
    · rfl
  | speichere _ _ _ _ => rfl
  | veroeffentliche _ _ _ _ => rfl
  | zaun _ => rfl
  | lade _ _ _ _ _ => exact r.bindeGelesen_fortsetzungen _ _ _
  | tausche _ _ _ _ _ _ => exact r.bindeGelesen_fortsetzungen _ _ _
  | vergleicheTausche _ _ _ _ _ _ _ => exact r.bindeGelesen_fortsetzungen _ _ _
  | holeUndAddiere _ _ _ _ _ _ => exact r.bindeGelesen_fortsetzungen _ _ _

theorem zugriffStapel (b : Befehl) (familie : b.familie = .zugriff) :
    b.Stapelwirkung b.klasse.Stapel := by
  intro frame live
  cases b with
  | zugriff form =>
    change (form.uebertrag frame 0).fortsetzungen.length ≤ frame.fortsetzungen.length + form.klasse.Stapel
    rw [form.uebertrag_fortsetzungen]
    exact Nat.le_add_right _ _
  | faden form =>
    change (form.uebertrag frame 0).fortsetzungen.length ≤ frame.fortsetzungen.length + form.klasse.Stapel
    rw [(form.uebertrag_lokal frame 0).1]
    exact Nat.le_add_right _ _
  | _ => cases familie

end Gabbro.Core.Ast.Semantik
