module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Reserviert

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen

/-! # The translation-cache model is not vacuous

The coverage invariant (`tlbGedeckt_erreichbar`) and the release guard (`flush_verweigert_gecachte_uebersetzung`)
are statements over every reachable state and every caching core. If no run could ever fill a cell, both
would hold for the empty cache alone and would say nothing. This module exhibits one concrete reachable
run of a real memory unit: a mapping is created, hardware fills a cell for it, the mapping is revoked and
the token is bound. At the end a stale cell is present, the release is refused while it caches the revoked
page, and the release is enabled once the cell is dropped by hardware. All states below are the actual
successors of `memProgram` from a real start, not hand-built witnesses. -/

private def tlbName : Identifier :=
  keywordName 't' [] (by decide) (by intro c h; cases h)

private def tlbEnv : Katalog.Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)

private theorem tlbHardware : Hardware Plattform.x86_64.katalog tlbEnv :=
  Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)

private def tlbStart : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none),
    [⟨0, 4096⟩, ⟨4096, 8192⟩], (fun _ => none), tlbEnv.politik.sicht 0 []⟩

private def tlbCode : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 [.read], .tlbFuellen 0 0 0,
    .unmapSpace 0 0 1, .bindToken tlbName]

private def tlbE : MemUnit := memProgram Plattform.x86_64.katalog tlbCode

private def tlbS0 : MemState := (I.start tlbE tlbStart).2

private theorem tlbS0status : tlbS0.status entryContext = .laeuft := by
  rfl

private theorem tlbS0pc : (tlbS0.lokal entryContext).pc = 0 := by
  rfl

private theorem tlbHead0 : tlbE.system.kopf tlbS0 entryContext = some (.newSpace 0) := by
  simp only [tlbE, memProgram, memHead, tlbS0status, tlbS0pc, tlbCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tlbEval0 :
    ((.newSpace 0 : MemInstruction).evaluate Plattform.x86_64.katalog.plattform.ziel
      tlbS0 entryContext).isSome = true := by rfl

private def tlbF1 := ((.newSpace 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tlbS0 entryContext).get tlbEval0

private theorem tlbF1eq : (.newSpace 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tlbS0 entryContext = some tlbF1 :=
  Option.eq_some_iff_get_eq.mpr ⟨tlbEval0, rfl⟩

private def tlbS1 : MemState := tlbF1.advance entryContext tlbS0

private theorem tlbS1status : tlbS1.status entryContext = .laeuft := by
  simpa only [tlbS1, MemFrame.advance] using tlbS0status

private theorem tlbS1pc : (tlbS1.lokal entryContext).pc = 1 := by
  simp only [tlbS1, MemFrame.advance, Function.update_self, tlbS0pc]

private theorem tlbHead1 : tlbE.system.kopf tlbS1 entryContext =
    some (.mapSpace 0 0 1 [.read]) := by
  simp only [tlbE, memProgram, memHead, tlbS1status, tlbS1pc, tlbCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tlbEval1 :
    ((.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel tlbS1 entryContext).isSome = true := by rfl

private def tlbF2 := ((.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tlbS1 entryContext).get tlbEval1

private theorem tlbF2eq : (.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tlbS1 entryContext = some tlbF2 :=
  Option.eq_some_iff_get_eq.mpr ⟨tlbEval1, rfl⟩

private def tlbS2 : MemState := tlbF2.advance entryContext tlbS1

private theorem tlbS2status : tlbS2.status entryContext = .laeuft := by
  simpa only [tlbS2, MemFrame.advance] using tlbS1status

private theorem tlbS2pc : (tlbS2.lokal entryContext).pc = 2 := by
  simp only [tlbS2, MemFrame.advance, Function.update_self, tlbS1pc]

private theorem tlbHead2 : tlbE.system.kopf tlbS2 entryContext = some (.tlbFuellen 0 0 0) := by
  simp only [tlbE, memProgram, memHead, tlbS2status, tlbS2pc, tlbCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tlbEval2 :
    ((.tlbFuellen 0 0 0 : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel tlbS2 entryContext).isSome = true := by rfl

private def tlbF3 := ((.tlbFuellen 0 0 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tlbS2 entryContext).get tlbEval2

private theorem tlbF3eq : (.tlbFuellen 0 0 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tlbS2 entryContext = some tlbF3 :=
  Option.eq_some_iff_get_eq.mpr ⟨tlbEval2, rfl⟩

private def tlbS3 : MemState := tlbF3.advance entryContext tlbS2

private theorem tlbS3status : tlbS3.status entryContext = .laeuft := by
  simpa only [tlbS3, MemFrame.advance] using tlbS2status

private theorem tlbS3pc : (tlbS3.lokal entryContext).pc = 3 := by
  simp only [tlbS3, MemFrame.advance, Function.update_self, tlbS2pc]

private theorem tlbHead3 : tlbE.system.kopf tlbS3 entryContext = some (.unmapSpace 0 0 1) := by
  simp only [tlbE, memProgram, memHead, tlbS3status, tlbS3pc, tlbCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tlbEval3 :
    ((.unmapSpace 0 0 1 : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel tlbS3 entryContext).isSome = true := by rfl

private def tlbF4 := ((.unmapSpace 0 0 1 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tlbS3 entryContext).get tlbEval3

private theorem tlbF4eq : (.unmapSpace 0 0 1 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tlbS3 entryContext = some tlbF4 :=
  Option.eq_some_iff_get_eq.mpr ⟨tlbEval3, rfl⟩

private def tlbS4 : MemState := tlbF4.advance entryContext tlbS3

private theorem tlbS4status : tlbS4.status entryContext = .laeuft := by
  simpa only [tlbS4, MemFrame.advance] using tlbS3status

private theorem tlbS4pc : (tlbS4.lokal entryContext).pc = 4 := by
  simp only [tlbS4, MemFrame.advance, Function.update_self, tlbS3pc]

private theorem tlbHead4 : tlbE.system.kopf tlbS4 entryContext = some (.bindToken tlbName) := by
  simp only [tlbE, memProgram, memHead, tlbS4status, tlbS4pc, tlbCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem tlbEval4 :
    ((.bindToken tlbName : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel tlbS4 entryContext).isSome = true := by rfl

private def tlbF5 := ((.bindToken tlbName : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel tlbS4 entryContext).get tlbEval4

private theorem tlbF5eq : (.bindToken tlbName : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel tlbS4 entryContext = some tlbF5 :=
  Option.eq_some_iff_get_eq.mpr ⟨tlbEval4, rfl⟩

private def tlbS5 : MemState := tlbF5.advance entryContext tlbS4

private theorem tlbS5status : tlbS5.status entryContext = .laeuft := by
  simpa only [tlbS5, MemFrame.advance] using tlbS4status

private theorem tlbS5pc : (tlbS5.lokal entryContext).pc = 5 := by
  simp only [tlbS5, MemFrame.advance, Function.update_self, tlbS4pc]

private theorem tlbReach : tlbE.system.IErreichbar tlbS0 tlbS5 := by
  exact System.IErreichbar.schritt entryContext () [plan]
    (System.IErreichbar.schritt entryContext () [plan]
      (System.IErreichbar.schritt entryContext () [plan]
        (System.IErreichbar.schritt entryContext () [plan]
          (System.IErreichbar.schritt entryContext () [plan] .start
            ⟨.newSpace 0, tlbHead0, ⟨tlbF1, tlbF1eq, rfl, rfl⟩⟩)
          ⟨.mapSpace 0 0 1 [.read], tlbHead1, ⟨tlbF2, tlbF2eq, rfl, rfl⟩⟩)
        ⟨.tlbFuellen 0 0 0, tlbHead2, ⟨tlbF3, tlbF3eq, rfl, rfl⟩⟩)
      ⟨.unmapSpace 0 0 1, tlbHead3, ⟨tlbF4, tlbF4eq, rfl, rfl⟩⟩)
    ⟨.bindToken tlbName, tlbHead4, ⟨tlbF5, tlbF5eq, rfl, rfl⟩⟩

private def tlbCell : TlbZelle := ⟨0, 0, 0, ⟨1, [.read], 0⟩⟩

private theorem tlbS5zellen : (tlbS5.lokal entryContext).tlb.zellen = [tlbCell] := by
  rfl

private theorem tlbS5gedeckt : tlbS5.TlbGedeckt := by
  simpa only [tlbE] using tlbGedeckt_erreichbar Plattform.x86_64.katalog tlbCode tlbStart tlbReach

private theorem tlbFlushNone :
    (MemInstruction.flushSpace tlbName).evaluate Plattform.x86_64.katalog.plattform.ziel
      tlbS5 entryContext = none := by
  rfl

private def tlbS5frameLeer : MemFrame := { (tlbS5.lokal entryContext) with tlb := ⟨[]⟩ }

private def tlbS5verdraengt : MemState :=
  { tlbS5 with lokal := Function.update tlbS5.lokal entryContext tlbS5frameLeer }

private theorem tlbS5verdraengtzellen :
    (tlbS5verdraengt.lokal entryContext).tlb.zellen = [] := by
  simp only [tlbS5verdraengt, tlbS5frameLeer, Function.update_self]

private theorem tlbS5verdraengtgedeckt : tlbS5verdraengt.TlbGedeckt := by
  intro c
  by_cases same : c = entryContext
  · rw [same]
    exact MemFrame.TlbGedeckt.verdraengt (tlbS5gedeckt entryContext) (by
      intro zelle mem
      rw [tlbS5verdraengtzellen] at mem
      cases mem) (by
      simp only [tlbS5verdraengt, tlbS5frameLeer, Function.update_self])
  · have eq : (tlbS5verdraengt.lokal c) = (tlbS5.lokal c) := by
      simp only [tlbS5verdraengt, Function.update_of_ne same]
    rw [eq]
    exact tlbS5gedeckt c

private theorem tlbFlushSome :
    (MemInstruction.flushSpace tlbName).evaluate Plattform.x86_64.katalog.plattform.ziel
      tlbS5verdraengt entryContext ≠ none := by
  have hs : ((MemInstruction.flushSpace tlbName).evaluate
      Plattform.x86_64.katalog.plattform.ziel tlbS5verdraengt entryContext).isSome = true := by rfl
  intro h
  rw [h] at hs
  cases hs

/-- **The translation-cache model is not vacuous.** A real reachable run first maps a page, then lets
    hardware cache it (`tlbFuellen`), then revokes the mapping and binds the pending token. Its final
    state holds a cell for the revoked page, the release step refuses to hand the frames back while
    that cell is cached, and the release step succeeds once hardware drops the cell. The premises of
    `tlbGedeckt_erreichbar` and of `flush_verweigert_gecachte_uebersetzung` therefore hold jointly in a
    state with a nonempty cache: neither statement is true only of an empty translation cache. -/
theorem tlb_nichtvakant :
    ∃ (name : Identifier) (E : MemUnit) (start : AussenStart) (code : List MemInstruction)
      (s : MemState),
      code = [.newSpace 0, .mapSpace 0 0 1 [.read], .tlbFuellen 0 0 0,
        .unmapSpace 0 0 1, .bindToken name] ∧
      E = memProgram Plattform.x86_64.katalog code ∧
      E.system.IErreichbar (I.start E start).2 s ∧
      s.TlbGedeckt ∧
      (s.lokal entryContext).tlb.zellen ≠ [] ∧
      (MemInstruction.flushSpace name).evaluate Plattform.x86_64.katalog.plattform.ziel
        s entryContext = none ∧
      ∃ (s' : MemState),
        (s'.lokal entryContext).tlb.zellen = [] ∧
        s'.TlbGedeckt ∧
        (MemInstruction.flushSpace name).evaluate Plattform.x86_64.katalog.plattform.ziel
          s' entryContext ≠ none := by
  refine ⟨tlbName, tlbE, tlbStart, tlbCode, tlbS5, rfl, rfl, ?_, ?_, ?_, ?_,
    tlbS5verdraengt, ?_, ?_, ?_⟩
  · exact tlbReach
  · exact tlbS5gedeckt
  · rw [tlbS5zellen]
    exact List.cons_ne_nil _ _
  · exact tlbFlushNone
  · exact tlbS5verdraengtzellen
  · exact tlbS5verdraengtgedeckt
  · exact tlbFlushSome

end Gabbro.Core.Ast.LowLevel
