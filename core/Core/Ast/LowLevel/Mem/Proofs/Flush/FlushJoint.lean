module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.NewSpace

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen

private theorem memDerivesSymbolsJ {form : MemForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .terminal ih

private theorem memParseOfPiecesJ {form : MemForm} {text : RawText} {tree : MemTree form}
    {pieces : List Piece} (lex : Lexed text pieces)
    (prod : tree.production (canonicalTokens pieces)) : MemParse text tree := by
  refine ⟨True.intro, pieces, lex, ?_⟩
  refine .production ⟨semanticTokens pieces, rfl, ?_⟩ (memDerivesSymbolsJ (semanticTokens pieces))
  simpa [canonicalTokens] using prod

private theorem memFlushPrintsJ (name : Identifier) :
    (MemTree.flushSpace name).production
      ((MemTree.flushSpace name).printPieces.map PrintedToken.value) := by
  simp only [MemTree.production, MemTree.printPieces, word, keyword,
    Identifier.print, PrintedToken.unquoted, printPunctuation, printOpen, printClose,
    openParen, closeParen, String.reduceToList]
  rfl

private theorem memParseOfPrintJ {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) : MemParse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply memParseOfPiecesJ (text := tree.print) (tree := tree) lex
  rw [aligned]
  exact prints

private theorem memGenauInternalJ {t : Nat} {c : Kontext} {s u : MemState}
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

private theorem memProgramAkzeptiert (code : List MemInstruction) :
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
        obtain ⟨traceEq, nextEq⟩ := memGenauInternalJ execute
        subst spur
        rw [nextEq, hu]
        simp only [MemFrame.advance]
        refine ⟨?_, ?_⟩
        · refine ⟨fun _ mem => (List.not_mem_nil mem).elim, [], ?_,
            fun _ mem => (List.not_mem_nil mem).elim⟩
          rw [List.append_nil]
        · intro h q hq hcut hans
          exact h q hq hcut hans
  · exact schrankenLokal_leer rfl rfl rfl  · intro ρ lauf
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

private def flushName : Identifier :=
  keywordName 't' [] (by decide) (by intro c h; cases h)

private theorem flushElaborate :
    elaborateMem { regionen := [], raeume := [], marken := [flushName] }
      (MemTree.flushSpace flushName) = some (.flushSpace flushName) := by
  change Option.map (fun _ => MemInstruction.flushSpace flushName)
    (List.idxOf? flushName.val [flushName.val]) = some (MemInstruction.flushSpace flushName)
  have h : List.idxOf? flushName.val [flushName.val] = some 0 := by rfl
  rw [h]
  rfl

private def flushEnv : Katalog.Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)

private theorem flushHardware : Hardware Plattform.x86_64.katalog flushEnv :=
  Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)

private def flushStart : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none),
    [⟨0, 4096⟩, ⟨4096, 8192⟩], (fun _ => none), flushEnv.politik.sicht 0 []⟩

private def flushPref : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 [.read], .unmapSpace 0 0 1, .bindToken flushName]

private def flushOp : MemInstruction := .flushSpace flushName

private def flushCode : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 [.read], .unmapSpace 0 0 1, .bindToken flushName, flushOp]

private theorem flushPrefEq : flushPref ++ [flushOp] = flushCode := by rfl

private def flushE : MemUnit := memProgram Plattform.x86_64.katalog flushCode

private def flushS0 : MemState := (I.start flushE flushStart).2

private theorem flushImage : image.gueltig Plattform.x86_64.katalog.plattform.ziel := by
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

private theorem flushZul : flushE.ZulStart flushEnv flushStart := by
  refine ⟨flushImage, flushHardware.kerne, ?_, ?_, ?_, ?_, ?_, rfl⟩
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
      exact ⟨by simp only [flushE, memProgram, image, List.length_cons,
        List.length_nil, Nat.zero_lt_succ], flushHardware.kerne⟩
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
    simp only [flushStart, List.mem_cons] at hr
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

private theorem flushS0status : flushS0.status entryContext = .laeuft := by
  rfl

private theorem flushS0pc : (flushS0.lokal entryContext).pc = 0 := by
  rfl

private theorem flushHead0 : flushE.system.kopf flushS0 entryContext = some (.newSpace 0) := by
  simp only [flushE, memProgram, memHead, flushS0status, flushS0pc, flushCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem flushEval0 :
    ((.newSpace 0 : MemInstruction).evaluate Plattform.x86_64.katalog.plattform.ziel
      flushS0 entryContext).isSome = true  := by rfl

private def flushF1 := ((.newSpace 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel flushS0 entryContext).get flushEval0

private theorem flushF1eq : (.newSpace 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel flushS0 entryContext = some flushF1 :=
  Option.eq_some_iff_get_eq.mpr ⟨flushEval0, rfl⟩

private def flushS1 : MemState := flushF1.advance entryContext flushS0

private theorem flushS1status : flushS1.status entryContext = .laeuft := by
  simpa only [flushS1, MemFrame.advance] using flushS0status

private theorem flushS1pc : (flushS1.lokal entryContext).pc = 1 := by
  simp only [flushS1, MemFrame.advance, Function.update_self, flushS0pc]

private theorem flushHead1 : flushE.system.kopf flushS1 entryContext =
    some (.mapSpace 0 0 1 [.read]) := by
  simp only [flushE, memProgram, memHead, flushS1status, flushS1pc, flushCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem flushEval1 :
    ((.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel flushS1 entryContext).isSome = true  := by rfl

private def flushF2 := ((.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel flushS1 entryContext).get flushEval1

private theorem flushF2eq : (.mapSpace 0 0 1 [.read] : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel flushS1 entryContext = some flushF2 :=
  Option.eq_some_iff_get_eq.mpr ⟨flushEval1, rfl⟩

private def flushS2 : MemState := flushF2.advance entryContext flushS1

private theorem flushS2status : flushS2.status entryContext = .laeuft := by
  simpa only [flushS2, MemFrame.advance] using flushS1status

private theorem flushS2pc : (flushS2.lokal entryContext).pc = 2 := by
  simp only [flushS2, MemFrame.advance, Function.update_self, flushS1pc]

private theorem flushHead2 : flushE.system.kopf flushS2 entryContext = some (.unmapSpace 0 0 1) := by
  simp only [flushE, memProgram, memHead, flushS2status, flushS2pc, flushCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem flushEval2 :
    ((.unmapSpace 0 0 1 : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel flushS2 entryContext).isSome = true  := by rfl

private def flushF3 := ((.unmapSpace 0 0 1 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel flushS2 entryContext).get flushEval2

private theorem flushF3eq : (.unmapSpace 0 0 1 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel flushS2 entryContext = some flushF3 :=
  Option.eq_some_iff_get_eq.mpr ⟨flushEval2, rfl⟩

private def flushS3 : MemState := flushF3.advance entryContext flushS2

private theorem flushS3status : flushS3.status entryContext = .laeuft := by
  simpa only [flushS3, MemFrame.advance] using flushS2status

private theorem flushS3pc : (flushS3.lokal entryContext).pc = 3 := by
  simp only [flushS3, MemFrame.advance, Function.update_self, flushS2pc]

private theorem flushHead3 : flushE.system.kopf flushS3 entryContext = some (.bindToken flushName) := by
  simp only [flushE, memProgram, memHead, flushS3status, flushS3pc, flushCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem flushEval3 :
    ((.bindToken flushName : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel flushS3 entryContext).isSome = true  := by rfl

private def flushF4 := ((.bindToken flushName : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel flushS3 entryContext).get flushEval3

private theorem flushF4eq : (.bindToken flushName : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel flushS3 entryContext = some flushF4 :=
  Option.eq_some_iff_get_eq.mpr ⟨flushEval3, rfl⟩

private def flushS4 : MemState := flushF4.advance entryContext flushS3

private theorem flushS4status : flushS4.status entryContext = .laeuft := by
  simpa only [flushS4, MemFrame.advance] using flushS3status

private theorem flushS4pc : (flushS4.lokal entryContext).pc = 4 := by
  simp only [flushS4, MemFrame.advance, Function.update_self, flushS3pc]

private theorem flushHead4 : flushE.system.kopf flushS4 entryContext = some flushOp := by
  simp only [flushE, memProgram, memHead, flushS4status, flushS4pc, flushCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem flushEval4 :
    (flushOp.evaluate Plattform.x86_64.katalog.plattform.ziel flushS4 entryContext).isSome = true  := by rfl

private def flushF5 := (flushOp.evaluate
  Plattform.x86_64.katalog.plattform.ziel flushS4 entryContext).get flushEval4

private theorem flushF5eq : flushOp.evaluate
    Plattform.x86_64.katalog.plattform.ziel flushS4 entryContext = some flushF5 :=
  Option.eq_some_iff_get_eq.mpr ⟨flushEval4, rfl⟩

private theorem flushReach : flushE.system.IErreichbar flushS0 flushS4 := by
  exact System.IErreichbar.schritt entryContext () [plan]
    (System.IErreichbar.schritt entryContext () [plan]
      (System.IErreichbar.schritt entryContext () [plan]
        (System.IErreichbar.schritt entryContext () [plan] .start
          ⟨.newSpace 0, flushHead0, ⟨flushF1, flushF1eq, rfl, rfl⟩⟩)
        ⟨.mapSpace 0 0 1 [.read], flushHead1, ⟨flushF2, flushF2eq, rfl, rfl⟩⟩)
      ⟨.unmapSpace 0 0 1, flushHead2, ⟨flushF3, flushF3eq, rfl, rfl⟩⟩)
    ⟨.bindToken flushName, flushHead3, ⟨flushF4, flushF4eq, rfl, rfl⟩⟩

theorem flushJointAussage : FlushJointAussage := by
  refine ⟨Plattform.x86_64.katalog,
    { regionen := [], raeume := [], marken := [flushName] },
    MemTree.flushSpace flushName, flushOp, flushEnv, flushStart,
    (MemTree.flushSpace flushName).print, flushPref, flushS4, flushF5, ?_,
    flushHardware, flushZul, ?_, ?_, ?_, ?_, ?_,
    memParseOfPrintJ _ (memFlushPrintsJ flushName), flushElaborate, ?_, flushHead4,
    flushF5eq, ?_, ?_⟩
  · refine ⟨0, 0, 1, [.read], 1, flushName, ?_, ?_⟩ <;> rfl
  · simpa only [flushPrefEq] using memProgramAkzeptiert flushCode
  · change ([] : List RawText).Nodup
    exact List.nodup_nil
  · change ([] : List RawText).Nodup
    exact List.nodup_nil
  · change [flushName.val].Nodup
    exact List.nodup_singleton _
  · refine ⟨MemTree.flushSpace flushName, memParseOfPrintJ _ (memFlushPrintsJ flushName), ?_⟩
    refine ⟨flushOp, flushElaborate, ?_⟩
    rfl
  · simpa only [flushPrefEq, flushE, flushS0] using flushReach
  · exact ⟨flushOp, flushHead4, ⟨flushF5, flushF5eq, rfl, rfl⟩⟩
  · exact ⟨flushOp, flushHead4, ⟨flushF5, flushF5eq, rfl, rfl⟩⟩

end Gabbro.Core.Ast.LowLevel
