module

public import Core.Ast.Semantik.Runtime.Walk

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- A successfully evaluated segment leaves only the counter and its own temporary slots changed. -/
structure Ausdrucksabschnitt (code : List Befehl) (endPC firstSlot : Nat) (before after : Rahmen) : Prop where
  walk : Rahmen.Lauf code before after
  position : after.pc = endPC
  frame : after = { before with pc := after.pc, temp := after.temp }
  lower : ∀ i, i < firstSlot → after.temp i = before.temp i

theorem Ausdrucksabschnitt.start (position : frame.pc = endPC) :
    Ausdrucksabschnitt code endPC firstSlot frame frame :=
  ⟨.start, position, by cases frame; rfl, fun _ _ => rfl⟩

theorem Ausdrucksabschnitt.aktiv (trace : Ausdrucksabschnitt code endPC firstSlot before after)
    (active : before.Aktiv) : after.Aktiv :=
  ⟨(congrArg Rahmen.stopp trace.frame).trans active.1,
    (congrArg Rahmen.rueckgabe trace.frame).trans active.2⟩

theorem Ausdrucksabschnitt.traegt (trace : Ausdrucksabschnitt code endPC firstSlot before after)
    (typed : before.traegt env) : after.traegt env := by
  intro type ref
  rw [congrArg Rahmen.lokale trace.frame]
  exact typed ref

theorem Ausdrucksabschnitt.trans (left : Ausdrucksabschnitt code midPC firstSlot before middle)
    (right : Ausdrucksabschnitt code endPC otherSlot middle after) (preserve : firstSlot ≤ otherSlot) :
    Ausdrucksabschnitt code endPC firstSlot before after := by
  refine ⟨left.walk.trans right.walk, right.position, ?_, ?_⟩
  · exact right.frame.trans
      (congrArg (fun frame : Rahmen => { frame with pc := after.pc, temp := after.temp }) left.frame)
  · intro i hi
    exact (right.lower i (Nat.lt_of_lt_of_le hi preserve)).trans (left.lower i hi)

theorem Ausdrucksabschnitt.schreibe (active : before.Aktiv)
    (lookup : code[before.pc]? = some instruction)
    (step : instruction.auswerten before = before.schreibe slot value) :
    Ausdrucksabschnitt code (before.pc + 1) slot before (before.schreibe slot value) := by
  refine ⟨.schritt .start ⟨instruction, active.1, active.2, lookup, step.symm⟩, rfl, ?_, ?_⟩
  · cases before
    rfl
  · intro i lower
    exact Function.update_of_ne (Nat.ne_of_lt lower) _ _

/-- A code fragment runs at its assigned address within the actual containing code.
    The premises describe the state at entry and the conclusion describes its computed data. -/
def BewachterAusdruck (env : Umgebung scope) (slot : Nat) (fragment : List Befehl)
    (ready result : Rahmen → Prop) : Prop :=
  ∀ (pre post : List Befehl) (before : Rahmen),
    before.pc = pre.length → before.Aktiv → before.traegt env →
    before.WaechterHalten (pre ++ fragment ++ post) → ready before →
    ∃ after, Ausdrucksabschnitt (pre ++ fragment ++ post) (pre.length + fragment.length) slot before after ∧
      result after

theorem BewachterAusdruck.leer (preserve : ∀ frame, ready frame → result frame) :
    BewachterAusdruck env slot [] ready result := by
  intro pre post before position _ _ _ h
  exact ⟨before, .start (by simpa only [List.length_nil, Nat.add_zero] using position), preserve before h⟩

theorem BewachterAusdruck.anhaengen
    (left : BewachterAusdruck env leftSlot leftCode ready between)
    (right : BewachterAusdruck env rightSlot rightCode between rightResult)
    (slotted : leftSlot ≤ rightSlot)
    (combine : ∀ middle after, between middle → rightResult after →
      (∀ i, i < rightSlot → after.temp i = middle.temp i) → result after) :
    BewachterAusdruck env leftSlot (leftCode ++ rightCode) ready result := by
  intro pre post before position running typed checked entry
  have checkedLeft : before.WaechterHalten (pre ++ leftCode ++ (rightCode ++ post)) := by
    simpa only [List.append_assoc] using checked
  obtain ⟨middle, leftTrace, intermediate⟩ :=
    left pre (rightCode ++ post) before position running typed checkedLeft entry
  have checkedRight : middle.WaechterHalten ((pre ++ leftCode) ++ rightCode ++ post) := by
    simpa only [List.append_assoc] using checkedLeft.after leftTrace.walk
  obtain ⟨after, rightTrace, final⟩ := right (pre ++ leftCode) post middle
    (by simpa only [List.length_append] using leftTrace.position)
    (leftTrace.aktiv running) (leftTrace.traegt typed) checkedRight intermediate
  have traceLeft :
      Ausdrucksabschnitt (pre ++ (leftCode ++ rightCode) ++ post) (pre.length + leftCode.length)
        leftSlot before middle := by
    simpa only [List.append_assoc] using leftTrace
  have traceRight :
      Ausdrucksabschnitt (pre ++ (leftCode ++ rightCode) ++ post)
        (pre.length + (leftCode ++ rightCode).length) rightSlot middle after := by
    simpa only [List.append_assoc, List.length_append, Nat.add_assoc] using rightTrace
  exact ⟨after, traceLeft.trans traceRight slotted, combine middle after intermediate final rightTrace.lower⟩

theorem BewachterAusdruck.schreibe (value : Rahmen → Dynamisch)
    (eval : ∀ pre post (before : Rahmen), before.pc = pre.length → before.Aktiv → before.traegt env →
      before.WaechterHalten (pre ++ [instruction] ++ post) → ready before →
      instruction.auswerten before = before.schreibe slot (some (value before)))
    (result : ∀ before, ready before → resultAt (before.schreibe slot (some (value before)))) :
    BewachterAusdruck env slot [instruction] ready resultAt := by
  intro pre post before position active typed checked h
  have lookup : (pre ++ [instruction] ++ post)[before.pc]? = some instruction := by
    rw [position, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have step := Ausdrucksabschnitt.schreibe active lookup (eval pre post before position active typed checked h)
  exact ⟨_, by simpa only [position, List.length_cons, List.length_nil] using step, result before h⟩

end Gabbro.Core.Ast.Semantik
