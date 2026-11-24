module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Sicher
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.RechteLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen

/-! # The table model is not vacuous

The table invariant (`tabellenGedeckt_erreichbar`) and the full-view safety (`uebersetze_sicher_voll`)
are statements over every reachable state. If no run could ever fill a table and a cache cell jointly,
all three invariants would hold vacuously. This module exhibits one concrete reachable run of a real
memory unit: a mapping is created and hardware fills a cell for it. At the end the table holds the
entry, the cache holds a copy, all three invariants hold jointly, and a translation over the full
view (`MemFrame.mmuSicht`) succeeds. All states below are the actual successors of `memProgram` from
a real start, not hand-built witnesses. -/

private def tabName : Identifier :=
  keywordName 't' [] (by decide) (by intro c h; cases h)

private def tabEnv : Katalog.Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)

private theorem tabHardware : Hardware Plattform.x86_64.katalog tabEnv :=
  Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)

private def tabStart : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none),
    [⟨0, 4096⟩, ⟨4096, 8192⟩], (fun _ => none), tabEnv.politik.sicht 0 []⟩

private def tabCode : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 [.read], .tlbFuellen 0 0 0]

private def tabE : MemUnit := memProgram Plattform.x86_64.katalog tabCode

private def tabS0 : MemState := (I.start tabE tabStart).2

private theorem tabS0status : tabS0.status entryContext = .laeuft := by
  rfl

private theorem tabS0pc : (tabS0.lokal entryContext).pc = 0 := by
  rfl

private theorem tabHead0 : tabE.system.kopf tabS0 entryContext = some (.newSpace 0) := by
  simp only [tabE, memProgram, memHead, tabS0status, tabS0pc, tabCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tabEval0 :
    ((.newSpace 0 : MemInstruction).evaluate Plattform.x86_64.katalog.plattform.ziel
      tabS0 entryContext).isSome = true := by rfl

private def tabF1 := ((.newSpace 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tabS0 entryContext).get tabEval0

private theorem tabF1eq : (.newSpace 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tabS0 entryContext = some tabF1 :=
  Option.eq_some_iff_get_eq.mpr ⟨tabEval0, rfl⟩

private def tabS1 : MemState := tabF1.advance entryContext tabS0

private theorem tabS1status : tabS1.status entryContext = .laeuft := by
  simpa only [tabS1, MemFrame.advance] using tabS0status

private theorem tabS1pc : (tabS1.lokal entryContext).pc = 1 := by
  simp only [tabS1, MemFrame.advance, Function.update_self, tabS0pc]

private theorem tabHead1 : tabE.system.kopf tabS1 entryContext =
    some (.mapSpace 0 0 1 [.read]) := by
  simp only [tabE, memProgram, memHead, tabS1status, tabS1pc, tabCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tabEval1 :
    ((.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel tabS1 entryContext).isSome = true := by rfl

private def tabF2 := ((.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tabS1 entryContext).get tabEval1

private theorem tabF2eq : (.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tabS1 entryContext = some tabF2 :=
  Option.eq_some_iff_get_eq.mpr ⟨tabEval1, rfl⟩

private def tabS2 : MemState := tabF2.advance entryContext tabS1

private theorem tabS2status : tabS2.status entryContext = .laeuft := by
  simpa only [tabS2, MemFrame.advance] using tabS1status

private theorem tabS2pc : (tabS2.lokal entryContext).pc = 2 := by
  simp only [tabS2, MemFrame.advance, Function.update_self, tabS1pc]

private theorem tabHead2 : tabE.system.kopf tabS2 entryContext = some (.tlbFuellen 0 0 0) := by
  simp only [tabE, memProgram, memHead, tabS2status, tabS2pc, tabCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tabEval2 :
    ((.tlbFuellen 0 0 0 : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel tabS2 entryContext).isSome = true := by rfl

private def tabF3 := ((.tlbFuellen 0 0 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tabS2 entryContext).get tabEval2

private theorem tabF3eq : (.tlbFuellen 0 0 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tabS2 entryContext = some tabF3 :=
  Option.eq_some_iff_get_eq.mpr ⟨tabEval2, rfl⟩

private def tabS3 : MemState := tabF3.advance entryContext tabS2

private theorem tabReach : tabE.system.IErreichbar tabS0 tabS3 := by
  exact System.IErreichbar.schritt entryContext () [plan]
    (System.IErreichbar.schritt entryContext () [plan]
      (System.IErreichbar.schritt entryContext () [plan] .start
        ⟨.newSpace 0, tabHead0, ⟨tabF1, tabF1eq, rfl, rfl⟩⟩)
      ⟨.mapSpace 0 0 1 [.read], tabHead1, ⟨tabF2, tabF2eq, rfl, rfl⟩⟩)
    ⟨.tlbFuellen 0 0 0, tabHead2, ⟨tabF3, tabF3eq, rfl, rfl⟩⟩

private theorem tabS3gedeckt : tabS3.TlbGedeckt := by
  simpa only [tabE] using tlbGedeckt_erreichbar Plattform.x86_64.katalog tabCode tabStart tabReach

private theorem tabS3rechte : tabS3.TlbRechteGedeckt := by
  simpa only [tabE] using tlbRechteGedeckt_erreichbar Plattform.x86_64.katalog tabCode tabStart tabReach

private theorem tabS3tabellen : tabS3.TabellenGedeckt := by
  simpa only [tabE] using tabellenGedeckt_erreichbar Plattform.x86_64.katalog tabCode tabStart tabReach

private theorem tabS3zellen : (tabS3.lokal entryContext).tlb.zellen =
    [⟨0, 0, 0, ⟨1, [.read], 0⟩⟩] := by
  rfl

private theorem tabS3tabelle : (tabS3.lokal entryContext).tabellenSicht 0 0 =
    some ⟨1, [.read], 0⟩ := by
  rfl

private theorem tabS3uebersetzt :
    uebersetze Plattform.x86_64.katalog.plattform.ziel
      (tabS3.lokal entryContext).mmuSicht 0 0 0 .read = .ok (4096, 0) := by
  rfl

/-- **The table model is not vacuous.** A real reachable run first maps a page, then lets hardware
    cache it. Its final state holds the table entry and a cached copy, satisfies all three invariants
    jointly (`TlbGedeckt`, `TlbRechteGedeckt`, `TabellenGedeckt`), and translates over the full view.
    Neither the table cover nor the cache cover is true only of an empty view. -/
theorem tabelle_nichtvakant :
    ∃ (E : MemUnit) (start : AussenStart) (code : List MemInstruction) (s : MemState),
      code = [.newSpace 0, .mapSpace 0 0 1 [.read], .tlbFuellen 0 0 0] ∧
      E = memProgram Plattform.x86_64.katalog code ∧
      E.system.IErreichbar (I.start E start).2 s ∧
      s.TlbGedeckt ∧ s.TlbRechteGedeckt ∧ s.TabellenGedeckt ∧
      (s.lokal entryContext).tlb.zellen ≠ [] ∧
      (s.lokal entryContext).tabellenSicht 0 0 ≠ none ∧
      uebersetze Plattform.x86_64.katalog.plattform.ziel
        (s.lokal entryContext).mmuSicht 0 0 0 .read = .ok (4096, 0) := by
  refine ⟨tabE, tabStart, tabCode, tabS3, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tabReach
  · exact tabS3gedeckt
  · exact tabS3rechte
  · exact tabS3tabellen
  · rw [tabS3zellen]
    exact List.cons_ne_nil _ _
  · rw [tabS3tabelle]
    exact Option.some_ne_none _
  · exact tabS3uebersetzt

end Gabbro.Core.Ast.LowLevel
