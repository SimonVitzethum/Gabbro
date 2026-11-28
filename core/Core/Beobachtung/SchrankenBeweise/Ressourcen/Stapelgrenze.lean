module

public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Schranken
public import Core.Ast.Semantik.Elaborierung
import Core.Ast.Program.Progress

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine
open Beobachtung

/-- A bounded transfer keeps its result if the continuation stack fits. On overflow it keeps
    the old frame and records the ordinary named overflow exit. -/
def Rahmen.begrenzeStapel (r nach : Rahmen) (n : Nat) : Rahmen :=
  if nach.fortsetzungen.length ≤ n then nach else r.halt (.ueberlauf none)

/-- Stack enforcement changes only the frame transfer. Class operands and plans still come
    from the original form. With an open ceiling the original form is used directly. -/
def Schrittform.mitStapelgrenze (F : Schrittform) : Option Nat → Schrittform
  | none => F
  | some n => { F with uebertrag := fun r live v => r.begrenzeStapel (F.uebertrag r live v) n }

theorem Schrittform.mitStapelgrenze_stapel {ι : Type} (E : Klasseneinheit ι) (F : Schrittform) :
    (F.mitStapelgrenze E.schranken.stapel).Stapelschranke E := by
  intro r live v n bound before
  rw [bound]
  change (r.begrenzeStapel (F.uebertrag r live v) n).fortsetzungen.length ≤ n
  unfold Rahmen.begrenzeStapel
  split
  · assumption
  · exact before

/-- Overflow keeps the whole continuation stack and names the exit on the refusing frame. -/
theorem Rahmen.begrenzeStapel_voll {r nach : Rahmen} {n : Nat}
    (voll : n < nach.fortsetzungen.length) :
    r.begrenzeStapel nach n = r.halt (.ueberlauf none) :=
  if_neg (Nat.not_le.mpr voll)

/-- An actual call-class step can try to push a continuation at the ceiling. With the guard
    the same private plan records the overflow while keeping the previous stack. -/
theorem stapelgrenze_erfuellbar (name : Identifier) :
    ∃ (vor roh nach : Zustand),
      let F := (Befehl.rufe name [] none).form
      (F.mitStapelgrenze (some 1)).ideal eintritt vor PUnit.unit [plan] roh ∧
      (F.mitStapelgrenze (some 0)).ideal eintritt vor PUnit.unit [plan] nach ∧
      (vor.lokal eintritt).fortsetzungen.length = 0 ∧
      (roh.lokal eintritt).fortsetzungen.length = 1 ∧
      (nach.lokal eintritt).fortsetzungen = (vor.lokal eintritt).fortsetzungen ∧
      (nach.lokal eintritt).stopp = some (.ueberlauf none) := by
  let target : Funktion := ⟨name, 1, [], none, 0, true, [], none⟩
  let r := { Rahmen.start [] with funktionen := [target] }
  let site : Rufstelle := ⟨name, [], none, none⟩
  have lookup : Funktion.finde r.funktionen name = some target :=
    List.find?_cons_of_pos (p := fun f : Funktion => f.name.val == name.val) (beq_self_eq_true _)
  have types : site.passt r.funktionen = true := by simp only [Rufstelle.passt, site, lookup] <;> rfl
  have pushed : (r.ruf name [] none).fortsetzungen.length = 1 :=
    (directCall_fortschritt r site target lookup types [] rfl (Or.inl rfl) (Or.inl rfl)).2.1
  let F := (Befehl.rufe name [] none).form
  let d := startdaten [] (fun _ => none) (some 0)
  let vor : Zustand := Maschine.Zustand.start (fun _ => r) d.status d.kerne d.rechte
    (fun _ => 0) (.leer (fun _ => 0))
  let roh := F.nach eintritt vor 0
  let nach := (F.mitStapelgrenze (some 0)).nach eintritt vor 0
  have fits : r.begrenzeStapel (r.ruf name [] none) 1 = r.ruf name [] none := by
    unfold Rahmen.begrenzeStapel
    rw [if_pos pushed.le]
  have over : r.begrenzeStapel (r.ruf name [] none) 0 = r.halt (.ueberlauf none) :=
    Rahmen.begrenzeStapel_voll (pushed.symm ▸ Nat.zero_lt_one)
  have accepted : (F.mitStapelgrenze (some 1)).nach eintritt vor 0 = roh :=
    congrArg (fun frame => { vor with lokal := Function.update vor.lokal eintritt frame }) fits
  have refused : nach.lokal eintritt = r.halt (.ueberlauf none) := by
    simpa only [nach, Schrittform.nach, Function.update_self] using over
  refine ⟨vor, roh, nach, ⟨rfl, ?_⟩, ⟨rfl, rfl⟩, rfl, ?_, ?_, ?_⟩
  · exact accepted.symm
  · simpa only [roh, Schrittform.nach, Function.update_self] using pushed
  · exact congrArg Rahmen.fortsetzungen refused
  · exact congrArg Rahmen.stopp refused

end Gabbro.Core.Ast.Semantik
