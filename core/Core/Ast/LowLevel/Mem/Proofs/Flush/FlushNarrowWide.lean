module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.NewSpace
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Stufung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen
private theorem memDerivesSymbolsW {form : MemForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .terminal ih
private theorem memParseOfPiecesW {form : MemForm} {text : RawText} {tree : MemTree form}
    {pieces : List Piece} (lex : Lexed text pieces)
    (prod : tree.production (canonicalTokens pieces)) : MemParse text tree := by
  refine ⟨True.intro, pieces, lex, ?_⟩
  refine .production ⟨semanticTokens pieces, rfl, ?_⟩ (memDerivesSymbolsW (semanticTokens pieces))
  simpa [canonicalTokens] using prod
private theorem memFlushPrintsW (name : Identifier) :
    (MemTree.flushSpace name).production
      ((MemTree.flushSpace name).printPieces.map PrintedToken.value) := by
  simp only [MemTree.production, MemTree.printPieces, word, keyword,
    Identifier.print, PrintedToken.unquoted, printPunctuation, printOpen, printClose,
    openParen, closeParen, String.reduceToList]
  rfl
private theorem memParseOfPrintW {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) : MemParse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply memParseOfPiecesW (text := tree.print) (tree := tree) lex
  rw [aligned]
  exact prints
private theorem memGenauInternalW {t : Nat} {c : Kontext} {s u : MemState}
    {trace : SchrittSpur Nat UInt8} {next : MemState}
    (execute : FuehrtSchrittAus memSetup t c s u plan trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨rahmen, _, _, _, action, memory, nextEq⟩ := execute
  cases trace with
  | mk events outside =>
      cases action
      simp only [plan, List.nil_append, schreibEreignisse, List.map_nil] at memory
      have unchanged : ∀ {recorded graph},
          Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
            recorded = [] ∧ graph = s.graph := by
        intro _ _ run
        cases run
        exact ⟨rfl, rfl⟩
      obtain ⟨rfl, graph⟩ := unchanged memory
      rw [graph] at nextEq
      rw [← rahmen.graph] at nextEq
      exact ⟨rfl, nextEq⟩
private theorem memProgramAkzeptiertW (code : List MemInstruction) :
    Annahme.Akzeptiert (memProgram Plattform.x86_64.katalog code) := by
  let E := memProgram Plattform.x86_64.katalog code
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_,
    ⟨Aussen.zulassung_m2 _, ?_⟩, memProgramFlussLokal _ code, ?_⟩, ?_, ?_⟩
  · intro i c s u w P hstep
    simp only [memProgram, MemInstruction.rule, MemInstruction.step] at hstep
    rcases hstep with ⟨frame, heval, hP, hu⟩
    have hPlan : P = plan := (List.cons.inj hP).1
    subst P
    rw [Annahme.Befugt]
    constructor
    · intro x hx
      cases hx
    · intro l hl
      cases hl
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur s' step
    cases step with
    | kontext _ _ regel execute =>
        obtain ⟨i, hi, frame, heval, planEq, hu⟩ := regel
        cases (List.cons.inj planEq).1
        obtain ⟨traceEq, nextEq⟩ := memGenauInternalW execute
        subst spur
        rw [nextEq, hu]
        simp only [MemFrame.advance]
        refine ⟨?_, ?_⟩
        · refine ⟨fun _ mem => (List.not_mem_nil mem).elim, [], ?_,
            fun _ mem => (List.not_mem_nil mem).elim⟩
          rw [List.append_nil]
        · intro h q hq hcut hans
          exact h q hq hcut hans
  · exact schrankenLokal_leer rfl rfl rfl
  · intro ρ lauf
    change (∀ p ∈ ([] : List (MemState → Prop)), p (I.start E ρ.start).2) ∧
      (∀ t : I.Schnitt E ρ, ∀ p ∈ ([] : List (MemState → Prop)), p (ρ.zeit.zustand t.val)) ∧
      (∀ t : I.Schnitt E ρ, (∀ c, E.system.fertig (ρ.zeit.zustand t.val) c) →
        ∀ p ∈ ([] : List (MemState → Prop)), p (ρ.zeit.zustand t.val))
    exact ⟨fun _ h => (List.not_mem_nil h).elim,
      fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro ρ lauf t op args need
      exact False.elim need
    · intro ρ lauf t waiting
      obtain ⟨C, nonEmpty, blocked⟩ := waiting
      obtain ⟨c, hc⟩ := nonEmpty
      obtain ⟨b, hb, _⟩ := blocked c hc
      simpa only [memProgram] using hb
    · intro ρ lauf t l h _ hne
      exact (hne rfl).elim

private def wideName : Identifier :=
  keywordName 'w' [] (by decide) (by intro c h; cases h)
private theorem wideElaborate :
    elaborateMem { regionen := [], raeume := [], marken := [wideName] }
      (MemTree.flushSpace wideName) = some (.flushSpace wideName) := by
  change Option.map (fun _ => MemInstruction.flushSpace wideName)
    (List.idxOf? wideName.val [wideName.val]) = some (MemInstruction.flushSpace wideName)
  have h : List.idxOf? wideName.val [wideName.val] = some 0 := by rfl
  rw [h]
  rfl

private def wideEnv : Katalog.Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)
private theorem wideHardware : Hardware Plattform.x86_64.katalog wideEnv :=
  Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)

private def wideStart : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none),
    [⟨0, 4096⟩, ⟨4096, 8192⟩], (fun _ => none), wideEnv.politik.sicht 0 []⟩

private def mapRightsW : List Speicherdienst := [.read, .write]
private def narrowRightsW : List Speicherdienst := [.read]

private def widePref : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 mapRightsW, .tlbFuellen 0 0 0,
    .protectSpace 0 0 1 narrowRightsW, .bindToken wideName]

private def wideEvict : MemInstruction := .tlbVerdraengen 0 0 0
private def wideOp : MemInstruction := .flushSpace wideName

private def wideCode : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 mapRightsW, .tlbFuellen 0 0 0,
    .protectSpace 0 0 1 narrowRightsW, .bindToken wideName, wideEvict, wideOp]
private theorem widePrefEq : widePref ++ [wideEvict, wideOp] = wideCode := by rfl

private def wideE : MemUnit := memProgram Plattform.x86_64.katalog wideCode
private def wideS0 : MemState := (I.start wideE wideStart).2
private theorem wideImage : image.gueltig Plattform.x86_64.katalog.plattform.ziel := by
  refine ⟨List.Mem.head _, ?_, ?_⟩
  · intro a v h
    change (if a = 0 then some 0 else none) = some v at h
    split at h
    · rename_i h0
      subst a
      exact Nat.pow_pos (Nat.zero_lt_succ _)
    · cases h
  · intro a hm
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨0, rfl⟩
private theorem wideZul : wideE.ZulStart wideEnv wideStart := by
  refine ⟨wideImage, wideHardware.kerne, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro i hi
    change i < 1 at hi
    have hi0 : i = 0 := by omega
    subst i
    exact ⟨0, rfl⟩
  · intro i c hi
    change (if i = 0 then some 0 else none) = some c at hi
    split at hi
    · rename_i hi0
      subst i
      cases hi
      exact ⟨by simp only [wideE, memProgram, image, List.length_cons,
        List.length_nil, Nat.zero_lt_succ], wideHardware.kerne⟩
    · cases hi
  · change List.Pairwise Strecke.getrennt [⟨0, 4096⟩, ⟨4096, 8192⟩]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
    · intro a ha
      have ha' : a = (⟨4096, 8192⟩ : Strecke) := by
        simpa only [List.mem_singleton] using ha
      subst a
      change Strecke.getrennt (⟨0, 4096⟩ : Strecke) ⟨4096, 8192⟩
      simp only [Strecke.getrennt]
      omega
    · intro a ha
      cases ha
  · intro r hr
    simp only [wideStart, List.mem_cons] at hr
    rcases hr with hEq | hr
    · subst r
      refine ⟨by change 0 < 4096; omega, by change 4096 ≤ 2 ^ (52 : Nat); omega, ?_⟩
      intro e d hdev hmmio
      cases e with
      | uart =>
          change some Plattform.x86_64.uart = some d at hdev
          cases hdev
          change GeratBus.ioPorts = GeratBus.mmio at hmmio
          cases hmmio
      | virtio =>
          change some Plattform.x86_64.virtio = some d at hdev
          cases hdev
          simp only [Plattform.virtio, GeraeteDaten.window, Strecke.getrennt]
          omega
      | bios | uefi | psci | sbi | hosted | cProcess =>
          change none = some d at hdev
          cases hdev
    · rcases hr with hEq | hr
      · subst r
        refine ⟨by change 4096 < 8192; omega, by change 8192 ≤ 2 ^ (52 : Nat); omega, ?_⟩
        intro e d hdev hmmio
        cases e with
        | uart =>
            change some Plattform.x86_64.uart = some d at hdev
            cases hdev
            change GeratBus.ioPorts = GeratBus.mmio at hmmio
            cases hmmio
        | virtio =>
            change some Plattform.x86_64.virtio = some d at hdev
            cases hdev
            simp only [Plattform.virtio, GeraeteDaten.window, Strecke.getrennt]
            omega
        | bios | uefi | psci | sbi | hosted | cProcess =>
            change none = some d at hdev
            cases hdev
      · cases hr
  · intro a byte hb
    cases hb
private theorem wideS0status : wideS0.status entryContext = .laeuft := by rfl

private theorem wideS0pc : (wideS0.lokal entryContext).pc = 0 := by rfl
private theorem wideHead0 : wideE.system.kopf wideS0 entryContext = some (.newSpace 0) := by
  simp only [wideE, memProgram, memHead, wideS0status, wideS0pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval0 : ((.newSpace 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS0 entryContext).isSome = true := by rfl
private def wideF1 := ((.newSpace 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS0 entryContext).get wideEval0
private def wideS1 : MemState := wideF1.advance entryContext wideS0

private theorem wideS1status : wideS1.status entryContext = .laeuft := by
  simpa only [wideS1, MemFrame.advance] using wideS0status

private theorem wideS1pc : (wideS1.lokal entryContext).pc = 1 := by
  simp only [wideS1, MemFrame.advance, Function.update_self, wideS0pc]

private theorem wideHead1 : wideE.system.kopf wideS1 entryContext =
    some (.mapSpace 0 0 1 mapRightsW) := by
  simp only [wideE, memProgram, memHead, wideS1status, wideS1pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval1 : ((.mapSpace 0 0 1 mapRightsW : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS1 entryContext).isSome = true := by rfl
private def wideF2 := ((.mapSpace 0 0 1 mapRightsW : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS1 entryContext).get wideEval1
private def wideS2 : MemState := wideF2.advance entryContext wideS1

private theorem wideS2status : wideS2.status entryContext = .laeuft := by
  simpa only [wideS2, MemFrame.advance] using wideS1status

private theorem wideS2pc : (wideS2.lokal entryContext).pc = 2 := by
  simp only [wideS2, MemFrame.advance, Function.update_self, wideS1pc]

private theorem wideHead2 : wideE.system.kopf wideS2 entryContext =
    some (.tlbFuellen 0 0 0) := by
  simp only [wideE, memProgram, memHead, wideS2status, wideS2pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval2 : ((.tlbFuellen 0 0 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS2 entryContext).isSome = true := by rfl
private def wideF3 := ((.tlbFuellen 0 0 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS2 entryContext).get wideEval2
private def wideS3 : MemState := wideF3.advance entryContext wideS2

private theorem wideS3status : wideS3.status entryContext = .laeuft := by
  simpa only [wideS3, MemFrame.advance] using wideS2status

private theorem wideS3pc : (wideS3.lokal entryContext).pc = 3 := by
  simp only [wideS3, MemFrame.advance, Function.update_self, wideS2pc]

private theorem wideHead3 : wideE.system.kopf wideS3 entryContext =
    some (.protectSpace 0 0 1 narrowRightsW) := by
  simp only [wideE, memProgram, memHead, wideS3status, wideS3pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval3 : ((.protectSpace 0 0 1 narrowRightsW : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS3 entryContext).isSome = true := by rfl
private def wideF4 := ((.protectSpace 0 0 1 narrowRightsW : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS3 entryContext).get wideEval3
private def wideS4 : MemState := wideF4.advance entryContext wideS3

private theorem wideS4status : wideS4.status entryContext = .laeuft := by
  simpa only [wideS4, MemFrame.advance] using wideS3status

private theorem wideS4pc : (wideS4.lokal entryContext).pc = 4 := by
  simp only [wideS4, MemFrame.advance, Function.update_self, wideS3pc]

private theorem wideHead4 : wideE.system.kopf wideS4 entryContext =
    some (.bindToken wideName) := by
  simp only [wideE, memProgram, memHead, wideS4status, wideS4pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval4 : ((.bindToken wideName : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS4 entryContext).isSome = true := by rfl
private def wideF5 := ((.bindToken wideName : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS4 entryContext).get wideEval4
private def wideS5 : MemState := wideF5.advance entryContext wideS4

private theorem wideS5status : wideS5.status entryContext = .laeuft := by
  simpa only [wideS5, MemFrame.advance] using wideS4status

private theorem wideS5pc : (wideS5.lokal entryContext).pc = 5 := by
  simp only [wideS5, MemFrame.advance, Function.update_self, wideS4pc]

private theorem wideHead5 : wideE.system.kopf wideS5 entryContext = some wideEvict := by
  simp only [wideE, memProgram, memHead, wideS5status, wideS5pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval5 : (wideEvict.evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS5 entryContext).isSome = true := by rfl
private def wideF6 := (wideEvict.evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS5 entryContext).get wideEval5
private def wideS6 : MemState := wideF6.advance entryContext wideS5

private theorem wideS6status : wideS6.status entryContext = .laeuft := by
  simpa only [wideS6, MemFrame.advance] using wideS5status

private theorem wideS6pc : (wideS6.lokal entryContext).pc = 6 := by
  simp only [wideS6, MemFrame.advance, Function.update_self, wideS5pc]

private theorem wideHead6 : wideE.system.kopf wideS6 entryContext = some wideOp := by
  simp only [wideE, memProgram, memHead, wideS6status, wideS6pc, wideCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]
private theorem wideEval6 : (wideOp.evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS6 entryContext).isSome = true := by rfl
private def wideF7 := (wideOp.evaluate
  Plattform.x86_64.katalog.plattform.ziel wideS6 entryContext).get wideEval6

private theorem wideF7eq : wideOp.evaluate
    Plattform.x86_64.katalog.plattform.ziel wideS6 entryContext = some wideF7 :=
  Option.eq_some_iff_get_eq.mpr ⟨wideEval6, rfl⟩
private theorem wideReach5 : wideE.system.IErreichbar wideS0 wideS5 := by
  exact System.IErreichbar.schritt entryContext () [plan]
    (System.IErreichbar.schritt entryContext () [plan]
      (System.IErreichbar.schritt entryContext () [plan]
        (System.IErreichbar.schritt entryContext () [plan]
          (System.IErreichbar.schritt entryContext () [plan] .start
            ⟨.newSpace 0, wideHead0,
              ⟨wideF1, Option.eq_some_iff_get_eq.mpr ⟨wideEval0, rfl⟩, rfl, rfl⟩⟩)
          ⟨.mapSpace 0 0 1 mapRightsW, wideHead1,
            ⟨wideF2, Option.eq_some_iff_get_eq.mpr ⟨wideEval1, rfl⟩, rfl, rfl⟩⟩)
        ⟨.tlbFuellen 0 0 0, wideHead2,
          ⟨wideF3, Option.eq_some_iff_get_eq.mpr ⟨wideEval2, rfl⟩, rfl, rfl⟩⟩)
      ⟨.protectSpace 0 0 1 narrowRightsW, wideHead3,
        ⟨wideF4, Option.eq_some_iff_get_eq.mpr ⟨wideEval3, rfl⟩, rfl, rfl⟩⟩)
    ⟨.bindToken wideName, wideHead4,
      ⟨wideF5, Option.eq_some_iff_get_eq.mpr ⟨wideEval4, rfl⟩, rfl, rfl⟩⟩
private theorem wideReach6 : wideE.system.IErreichbar wideS0 wideS6 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact wideReach5
  · exact ⟨wideEvict, wideHead5,
      ⟨wideF6, Option.eq_some_iff_get_eq.mpr ⟨wideEval5, rfl⟩, rfl, rfl⟩⟩

private def wideToken : Zuruecknahme := Zuruecknahme.verengung 0 0 1 0
private theorem wideHfind :
    ((wideS5.lokal entryContext).marken.find? (fun p => p.1.val == wideName.val)).map Prod.snd =
      some wideToken := by rfl

private def mappedSpaceW : Adressraum := ⟨⟨0, 4096⟩, [(0, ⟨1, mapRightsW, 0⟩)], 0, []⟩
private def narrowedSpaceW : Adressraum := narrowRights mappedSpaceW 0 1 narrowRightsW
private theorem wideHspace : (wideS5.lokal entryContext).spaces[wideToken.raum]? =
    some narrowedSpaceW := by rfl

private def wideCell : TlbZelle := ⟨0, 0, 0, ⟨1, mapRightsW, 0⟩⟩
private theorem wideCellMem : wideCell ∈ (wideS5.lokal entryContext).tlb.zellen := by
  change wideCell ∈ [wideCell]
  exact List.mem_cons_self
private theorem wideCellWider : ∃ right ∈ wideCell.eintrag.rights, right ∉ narrowRightsW := by
  refine ⟨Speicherdienst.write, ?_, ?_⟩
  · change Speicherdienst.write ∈ [Speicherdienst.read, Speicherdienst.write]
    exact List.mem_cons_of_mem Speicherdienst.read List.mem_cons_self
  · change ¬ Speicherdienst.write ∈ [Speicherdienst.read]
    simp only [List.mem_singleton]
    intro h
    cases h
private theorem wideNotNichtBreiter :
    ¬ (wideS5.lokal entryContext).tlb.NichtBreiter narrowedSpaceW
      wideToken.raum wideToken.seite wideToken.seiten := by
  intro nb
  obtain ⟨right, hright, hnot⟩ := wideCellWider
  have ged := nb wideCell wideCellMem (by rfl)
  exact hnot (ged ⟨1, narrowRightsW, 0⟩ (by rfl) (by rfl) right hright)
private theorem wideFlushNone :
    wideOp.evaluate Plattform.x86_64.katalog.plattform.ziel wideS5 entryContext = none := by
  have hmeaning := (flush_aussage.2.1 Plattform.x86_64.katalog.plattform.ziel wideS5 entryContext
    wideName wideToken narrowedSpaceW wideHfind wideHspace).2 (by rfl : wideToken.nurRechte = true)
  exact hmeaning.2 (Or.inr wideNotNichtBreiter)
private theorem wideS5verengt : (wideS5.lokal entryContext).verengt = [wideToken] := by rfl
private theorem wideS6Hfind :
    ((wideS6.lokal entryContext).marken.find? (fun p => p.1.val == wideName.val)).map Prod.snd =
      some wideToken := by rfl
private theorem wideS6Hspace : (wideS6.lokal entryContext).spaces[wideToken.raum]? =
    some narrowedSpaceW := by rfl
private theorem wideF7protected : wideF7.result = some .«protected» :=
  (flush_abschluss_nicht_breiter Plattform.x86_64.katalog.plattform.ziel wideName wideS6
    entryContext wideToken narrowedSpaceW wideS6Hfind wideS6Hspace (by rfl) wideF7eq).2.2.2.2.2
private theorem wideF7verengt : wideF7.verengt = [] := by rfl
private theorem wideF7keinToken :
    ∀ t ∈ wideF7.verengt, ∀ pg, wideToken.contains pg → ¬ t.contains pg := by
  rw [wideF7verengt]
  intro t h
  cases h
private theorem wideBezeichnet : BezeichnetMem Plattform.x86_64.katalog
    { regionen := [], raeume := [], marken := [wideName] }
    (MemTree.flushSpace wideName).print
    (memUnit Plattform.x86_64.katalog wideOp) .flushSpace := by
  refine ⟨MemTree.flushSpace wideName, memParseOfPrintW _ (memFlushPrintsW wideName), ?_⟩
  refine ⟨wideOp, wideElaborate, ?_⟩
  rfl

theorem flushNarrowWideJoint : FlushNarrowWideJointAussage := by
  have hnodupRegion : ([] : List (List Char)).Nodup := by
    exact List.nodup_nil
  refine ⟨Plattform.x86_64.katalog,
    { regionen := [], raeume := [], marken := [wideName] },
    MemTree.flushSpace wideName, wideOp, wideEvict, wideEnv, wideStart,
    (MemTree.flushSpace wideName).print,
    0, 0, 1, 1, 0, 0, 0, mapRightsW, narrowRightsW, wideName,
    widePref, wideS5, wideS6, wideF7, wideToken,
    ?_, ?_, ?_, ?_, ?_, wideHardware, wideZul, memProgramAkzeptiertW wideCode,
    hnodupRegion, hnodupRegion, ?_, wideBezeichnet,
    memParseOfPrintW _ (memFlushPrintsW wideName), wideElaborate,
    ?_, wideHead5, ?_, ?_, ?_, ?_, ?_, ?_, wideHead6, wideF7eq,
    wideF7protected, ?_, wideF7keinToken, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change [wideName.val].Nodup
    exact List.nodup_singleton _
  · simpa only [widePrefEq, wideE, wideS0] using wideReach5
  · exact ⟨wideCell, wideCellMem, rfl, by decide, wideCellWider⟩
  · exact ⟨narrowedSpaceW, wideHspace, wideHfind, wideNotNichtBreiter⟩
  · rfl
  · simpa only [wideS5verengt, List.mem_singleton]
  · exact wideFlushNone
  · simpa only [widePrefEq, wideE, wideS0] using wideReach6
  · exact (flush_abschluss_nicht_breiter Plattform.x86_64.katalog.plattform.ziel wideName wideS6
      entryContext wideToken narrowedSpaceW wideS6Hfind wideS6Hspace (by rfl) wideF7eq).2.1
  · exact ⟨wideOp, wideHead6, ⟨wideF7, wideF7eq, rfl, rfl⟩⟩
  · exact ⟨wideOp, wideHead6, ⟨wideF7, wideF7eq, rfl, rfl⟩⟩

end Gabbro.Core.Ast.LowLevel
