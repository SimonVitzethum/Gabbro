module

public import Core.Beobachtung.SchrankenBeweise.KostenEndlichBeweise
import Core.Ast.Semantik.Auswertung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

private theorem pruefeMass_einrichtung {u : Ast.Unit} {name : Identifier}
    {kern : FunktionsKern} {m : Measure kern.koerper.1}
    (found : findeKern u.2 name = some kern) (declared : kern.mass = some m)
    {r : Rahmen} (owner : r.funktion = some name) (value : Zahl m.lo m.hi)
    (operand : r.temp 0 = some ⟨.int m.lo m.hi, value⟩) :
    KostenEinrichtung u (.pruefeMass 0) r := by
  intro id a other lo hi named read _ lookup interval
  have sameName : name = id := Option.some.inj (owner.symm.trans named)
  subst id
  have sameKern : kern = other := Option.some.inj (found.symm.trans lookup)
  subst other
  have endpoints : some (m.lo, m.hi) = some (lo, hi) := by
    simpa only [FunktionsKern.massIntervall, declared, Option.map_some] using interval
  cases endpoints
  have exactRead : some (⟨m.lo, m.hi, value⟩ : Ganzzahl) = some a := by
    simpa only [Rahmen.zahl, operand, Option.some_bind, alsGanzzahl] using read
  cases exactRead
  exact ⟨le_rfl, le_rfl⟩

/-- Evaluate the declared measure at its entry address and execute the actual
    installer. Both a successful write and a rejected decrease preserve the
    cost invariant, including the saved frames. -/
theorem measurePrologue_kostenEinrichtung {u : Ast.Unit} {name : Identifier}
    {kern : FunktionsKern} {m : Measure kern.koerper.1}
    (found : findeKern u.2 name = some kern) (declared : kern.mass = some m)
    (env : Umgebung kern.koerper.1) (pre post : List Befehl)
    (code : (programm u).code = pre ++ (measurePrologue (some m)).code ++ post)
    (entry : Rahmen) (position : entry.pc = pre.length) (active : entry.Aktiv)
    (typed : entry.traegt env) (owner : entry.funktion = some name)
    (checked : entry.WaechterHalten (programm u).code)
    (good : (kostenGrenzen u).RahmenGut entry) :
    ∃ r, Ausdrucksabschnitt (programm u).code (pre.length + (expr 0 m.expression).code.length) 0 entry r ∧
      (programm u).code[r.pc]? = some (.pruefeMass 0) ∧
      KostenEinrichtung u (.pruefeMass 0) r ∧
      Rahmen.Lauf (programm u).code entry ((Befehl.pruefeMass 0).auswerten r) ∧
      (kostenGrenzen u).RahmenGut ((Befehl.pruefeMass 0).auswerten r) := by
  have layout : (programm u).code = pre ++ (expr 0 m.expression).code ++ (.pruefeMass 0 :: post) := by
    simpa only [measurePrologue, Fragment.anhaengen, Fragment.einzel, List.append_assoc,
      List.singleton_append] using code
  obtain ⟨r, trace, operand⟩ :=
    expr_ergebnis_typ_am 0 m.expression env entry typed active pre (.pruefeMass 0 :: post) position
      (layout ▸ checked)
  rw [← layout] at trace
  have lookup : (programm u).code[r.pc]? = some (.pruefeMass 0) := by
    rw [layout, trace.position, ← List.length_append,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have named : r.funktion = some name := (congrArg Rahmen.funktion trace.frame).trans owner
  have install := pruefeMass_einrichtung found declared named (m.expression.wert env) operand
  have atWrite : (kostenGrenzen u).RahmenGut r := by
    rw [trace.frame]
    exact good
  have running := trace.aktiv active
  exact ⟨r, trace, lookup, install, trace.walk.schritt ⟨_, running.1, running.2, lookup, rfl⟩,
    atWrite.auswerten install.gueltig _⟩

end Gabbro.Core.Beobachtung
