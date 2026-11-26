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
    simpa only [Rahmen.zahl, operand, Option.bind, alsGanzzahl] using read
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
    KostenGrenzen.auswerten atWrite install.gueltig _⟩

private theorem loop_left {a b : Fragment} {pc : Nat} {limit : SchleifenGrenze}
    (atTest : (pc, limit) ∈ a.schleifen) : (pc, limit) ∈ (a.anhaengen b).schleifen :=
  List.mem_append_left _ atTest

private theorem loop_right {a b : Fragment} {pc : Nat} {limit : SchleifenGrenze}
    (atTest : (pc, limit) ∈ b.schleifen) :
    (pc + a.code.length, limit) ∈ (a.anhaengen b).schleifen :=
  List.mem_append_right _ (List.mem_map.mpr ⟨(pc, limit), atTest, rfl⟩)

private theorem loop_relocated {pre body post : Fragment} {pc : Nat} {limit : SchleifenGrenze}
    {u : Ast.Unit}
    (table : (programm u).schleifen = ((pre.anhaengen body).anhaengen post).schleifen)
    (atTest : (pc, limit) ∈ body.schleifen) :
    (pc + pre.code.length, limit) ∈ (programm u).schleifen := by
  rw [table]
  exact loop_left (loop_right atTest)

/-- The while setup and its table row remain paired when the source statement
    is placed in the unit. The setup counts from its own PC past the condition. -/
theorem whileBounded_kostenEinrichtung {u : Ast.Unit} {lo hi : Int}
    (condition : Expr scope .bool) (bound : Expr scope (.int lo hi))
    (static : bound.static) (nonnegative : 0 ≤ lo) (handler : Identifier)
    (body : BracedBlock result scope) (pre post : Fragment) (r : Rahmen)
    (table : (programm u).schleifen =
      ((pre.anhaengen (stmt (.whileBounded condition bound static nonnegative handler body))).anhaengen
        post).schleifen)
    (position : r.pc = pre.code.length + (expr 0 bound).code.length)
    (value : Zahl lo hi) (operand : r.temp 0 = some ⟨.int lo hi, value⟩) :
    KostenEinrichtung u (.setzePasszahl 0 ((expr 0 condition).code.length + 1)) r := by
  let limit := SchleifenGrenze.whileBounded bound
  have localRow :
      ((expr 0 bound).code.length + ((expr 0 condition).code.length + 1), limit) ∈
        (stmt (.whileBounded condition bound static nonnegative handler body)).schleifen := by
    rw [stmt]
    apply loop_left
    apply loop_left
    have row := loop_right (a := (((expr 0 bound).anhaengen
      (.einzel (.setzePasszahl 0 ((expr 0 condition).code.length + 1)))).anhaengen (expr 0 condition)))
      (b := { Fragment.einzel (whileInstruction condition (bracedBlock body) handler) with
        schleifen := [(0, limit)] }) List.mem_cons_self
    simpa only [Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using row
  have row := loop_relocated table localRow
  intro a read
  have same : some (⟨lo, hi, value⟩ : Ganzzahl) = some a := by
    simpa only [Rahmen.zahl, operand, Option.bind, alsGanzzahl] using read
  cases same
  refine ⟨limit, ?_, Nat.le_refl _⟩
  rw [position]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using row

/-- The range setup installs both fields at its following instruction, using
    the same typed endpoints as the relocated range-test row. -/
theorem forRange_kostenEinrichtung {u : Ast.Unit} {low lowHi highLo high : Int}
    (name : Identifier) (ordinary : ordinaryLocal name)
    (lower : Expr scope (.int low lowHi)) (upper : Expr scope (.int highLo high))
    (static : lower.static ∧ upper.static) (handler : Option Identifier)
    (body : BracedBlock result (rangeBinding name low high :: scope))
    (pre post : Fragment) (r : Rahmen)
    (table : (programm u).schleifen =
      ((pre.anhaengen (stmt (.forRange name ordinary lower upper static handler body))).anhaengen
        post).schleifen)
    (position : r.pc = pre.code.length + ((expr 0 lower).code.length + (expr 1 upper).code.length))
    (start : Zahl low lowHi) (stop : Zahl highLo high)
    (lowerOperand : r.temp 0 = some ⟨.int low lowHi, start⟩)
    (upperOperand : r.temp 1 = some ⟨.int highLo high, stop⟩) :
    KostenEinrichtung u
      (.forAnfang 0 1 (rangeBinding name low high).type ((bracedBlock body).code.length + 4)
        (BracedBlock.rangeUses name body).1 ((BracedBlock.rangeUses name body).2 && handler.isNone)) r := by
  let limit := SchleifenGrenze.forRange lower upper
  have localRow :
      ((expr 0 lower).code.length + (expr 1 upper).code.length + 1, limit) ∈
        (stmt (.forRange name ordinary lower upper static handler body)).schleifen := by
    cases uses : BracedBlock.rangeUses name body with
    | mk shadows writes =>
      simp only [stmt, uses]
      apply loop_left
      apply loop_left
      apply loop_left
      have row := loop_right (a := (((expr 0 lower).anhaengen (expr 1 upper)).anhaengen
        (.einzel (.forAnfang 0 1 (rangeBinding name low high).type ((bracedBlock body).code.length + 4)
          shadows (writes && handler.isNone)))))
        (b := { Fragment.einzel (forInstruction (bracedBlock body) handler) with
          schleifen := [(0, limit)] }) List.mem_cons_self
      simpa only [Fragment.anhaengen, Fragment.einzel, List.length_append, List.length_cons,
        List.length_nil, Nat.zero_add] using row
  have row := loop_relocated table localRow
  intro a b readA readB _
  have sameA : some (⟨low, lowHi, start⟩ : Ganzzahl) = some a := by
    simpa only [Rahmen.zahl, lowerOperand, Option.bind, alsGanzzahl] using readA
  have sameB : some (⟨highLo, high, stop⟩ : Ganzzahl) = some b := by
    simpa only [Rahmen.zahl, upperOperand, Option.bind, alsGanzzahl] using readB
  cases sameA
  cases sameB
  refine ⟨limit, high, ?_, Nat.le_refl _, rfl, le_rfl⟩
  rw [position]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using row

end Gabbro.Core.Beobachtung
