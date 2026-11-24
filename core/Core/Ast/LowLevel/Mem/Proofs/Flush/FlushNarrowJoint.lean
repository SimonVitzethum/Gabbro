module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.NewSpace
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Stufung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen

private theorem memDerivesSymbolsN {form : MemForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .terminal ih

private theorem memParseOfPiecesN {form : MemForm} {text : RawText} {tree : MemTree form}
    {pieces : List Piece} (lex : Lexed text pieces)
    (prod : tree.production (canonicalTokens pieces)) : MemParse text tree := by
  refine ⟨True.intro, pieces, lex, ?_⟩
  refine .production ⟨semanticTokens pieces, rfl, ?_⟩ (memDerivesSymbolsN (semanticTokens pieces))
  simpa [canonicalTokens] using prod

private theorem memFlushPrintsN (name : Identifier) :
    (MemTree.flushSpace name).production
      ((MemTree.flushSpace name).printPieces.map PrintedToken.value) := by
  simp only [MemTree.production, MemTree.printPieces, word, keyword,
    Identifier.print, PrintedToken.unquoted, printPunctuation, printOpen, printClose,
    openParen, closeParen, String.reduceToList]
  rfl

private theorem memParseOfPrintN {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) : MemParse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply memParseOfPiecesN (text := tree.print) (tree := tree) lex
  rw [aligned]
  exact prints

private theorem memGenauInternalN {t : Nat} {c : Kontext} {s u : MemState}
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

private theorem memProgramAkzeptiertN (code : List MemInstruction) :
    Annahme.Akzeptiert (memProgram Plattform.x86_64.katalog code) := by
  let E := memProgram Plattform.x86_64.katalog code
  refine ⟨⟨Plattform.katalog_wohlgeformt .x86_64, ?_,
    ⟨Aussen.zulassung_m2 _, ?_⟩, memProgramFlussLokal _ code⟩, ?_, ?_⟩
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
        obtain ⟨traceEq, nextEq⟩ := memGenauInternalN execute
        subst spur
        rw [nextEq, hu]
        simp only [MemFrame.advance]
        refine ⟨?_, ?_⟩
        · refine ⟨fun _ mem => (List.not_mem_nil mem).elim, [], ?_,
            fun _ mem => (List.not_mem_nil mem).elim⟩
          rw [List.append_nil]
        · intro h q hq hcut hans
          exact h q hq hcut hans
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

private def narrowName : Identifier :=
  keywordName 'n' [] (by decide) (by intro c h; cases h)

private theorem narrowElaborate :
    elaborateMem { regionen := [], raeume := [], marken := [narrowName] }
      (MemTree.flushSpace narrowName) = some (.flushSpace narrowName) := by
  change Option.map (fun _ => MemInstruction.flushSpace narrowName)
    (List.idxOf? narrowName.val [narrowName.val]) = some (MemInstruction.flushSpace narrowName)
  have h : List.idxOf? narrowName.val [narrowName.val] = some 0 := by rfl
  rw [h]
  rfl

private def narrowEnv : Katalog.Umgebung :=
  Umgebung.referenz Plattform.x86_64.katalog 2 (fun _ _ => AussenSicht.leer)

private theorem narrowHardware : Hardware Plattform.x86_64.katalog narrowEnv :=
  Umgebung.referenz_hardware _ 2 _ (Plattform.katalog_wohlgeformt .x86_64) (by decide)

private def narrowStart : AussenStart :=
  ⟨0, (fun i => if i = 0 then some 0 else none),
    [⟨0, 4096⟩, ⟨4096, 8192⟩], (fun _ => none), narrowEnv.politik.sicht 0 []⟩

private def mapRightsN : List Speicherdienst := [.read, .write]
private def narrowRightsN : List Speicherdienst := [.read]

private def narrowPref : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 mapRightsN, .protectSpace 0 0 1 narrowRightsN, .bindToken narrowName]

private def narrowOp : MemInstruction := .flushSpace narrowName

private def narrowCode : List MemInstruction :=
  [.newSpace 0, .mapSpace 0 0 1 mapRightsN, .protectSpace 0 0 1 narrowRightsN, .bindToken narrowName, narrowOp]

private theorem narrowPrefEq : narrowPref ++ [narrowOp] = narrowCode := by rfl

private def narrowE : MemUnit := memProgram Plattform.x86_64.katalog narrowCode

private def narrowS0 : MemState := (I.start narrowE narrowStart).2

private theorem narrowImage : image.gueltig Plattform.x86_64.katalog.plattform.ziel := by
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

private theorem narrowZul : narrowE.ZulStart narrowEnv narrowStart := by
  refine ⟨narrowImage, narrowHardware.kerne, ?_, ?_, ?_, ?_, ?_, rfl⟩
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
      exact ⟨by simp only [narrowE, memProgram, image, List.length_cons,
        List.length_nil, Nat.zero_lt_succ], narrowHardware.kerne⟩
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
    simp only [narrowStart, List.mem_cons] at hr
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

private theorem narrowS0status : narrowS0.status entryContext = .laeuft := by rfl

private theorem narrowS0pc : (narrowS0.lokal entryContext).pc = 0 := by rfl

private theorem narrowHead0 : narrowE.system.kopf narrowS0 entryContext = some (.newSpace 0) := by
  simp only [narrowE, memProgram, memHead, narrowS0status, narrowS0pc, narrowCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem narrowEval0 :
    ((.newSpace 0 : MemInstruction).evaluate Plattform.x86_64.katalog.plattform.ziel
      narrowS0 entryContext).isSome = true := by rfl

private def narrowF1 := ((.newSpace 0 : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel narrowS0 entryContext).get narrowEval0

private theorem narrowF1eq : (.newSpace 0 : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel narrowS0 entryContext = some narrowF1 :=
  Option.eq_some_iff_get_eq.mpr ⟨narrowEval0, rfl⟩

private def narrowS1 : MemState := narrowF1.advance entryContext narrowS0

private theorem narrowS1status : narrowS1.status entryContext = .laeuft := by
  simpa only [narrowS1, MemFrame.advance] using narrowS0status

private theorem narrowS1pc : (narrowS1.lokal entryContext).pc = 1 := by
  simp only [narrowS1, MemFrame.advance, Function.update_self, narrowS0pc]

private theorem narrowHead1 : narrowE.system.kopf narrowS1 entryContext =
    some (.mapSpace 0 0 1 mapRightsN) := by
  simp only [narrowE, memProgram, memHead, narrowS1status, narrowS1pc, narrowCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem narrowEval1 :
    ((.mapSpace 0 0 1 mapRightsN : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel narrowS1 entryContext).isSome = true := by rfl

private def narrowF2 := ((.mapSpace 0 0 1 mapRightsN : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel narrowS1 entryContext).get narrowEval1

private theorem narrowF2eq : (.mapSpace 0 0 1 mapRightsN : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel narrowS1 entryContext = some narrowF2 :=
  Option.eq_some_iff_get_eq.mpr ⟨narrowEval1, rfl⟩

private def narrowS2 : MemState := narrowF2.advance entryContext narrowS1

private theorem narrowS2status : narrowS2.status entryContext = .laeuft := by
  simpa only [narrowS2, MemFrame.advance] using narrowS1status

private theorem narrowS2pc : (narrowS2.lokal entryContext).pc = 2 := by
  simp only [narrowS2, MemFrame.advance, Function.update_self, narrowS1pc]

private theorem narrowHead2 : narrowE.system.kopf narrowS2 entryContext =
    some (.protectSpace 0 0 1 narrowRightsN) := by
  simp only [narrowE, memProgram, memHead, narrowS2status, narrowS2pc, narrowCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem narrowEval2 :
    ((.protectSpace 0 0 1 narrowRightsN : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel narrowS2 entryContext).isSome = true := by rfl

private def narrowF3 := ((.protectSpace 0 0 1 narrowRightsN : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel narrowS2 entryContext).get narrowEval2

private theorem narrowF3eq : (.protectSpace 0 0 1 narrowRightsN : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel narrowS2 entryContext = some narrowF3 :=
  Option.eq_some_iff_get_eq.mpr ⟨narrowEval2, rfl⟩

private def narrowS3 : MemState := narrowF3.advance entryContext narrowS2

private theorem narrowS3status : narrowS3.status entryContext = .laeuft := by
  simpa only [narrowS3, MemFrame.advance] using narrowS2status

private theorem narrowS3pc : (narrowS3.lokal entryContext).pc = 3 := by
  simp only [narrowS3, MemFrame.advance, Function.update_self, narrowS2pc]

private theorem narrowHead3 : narrowE.system.kopf narrowS3 entryContext =
    some (.bindToken narrowName) := by
  simp only [narrowE, memProgram, memHead, narrowS3status, narrowS3pc, narrowCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem narrowEval3 :
    ((.bindToken narrowName : MemInstruction).evaluate
      Plattform.x86_64.katalog.plattform.ziel narrowS3 entryContext).isSome = true := by rfl

private def narrowF4 := ((.bindToken narrowName : MemInstruction).evaluate
  Plattform.x86_64.katalog.plattform.ziel narrowS3 entryContext).get narrowEval3

private theorem narrowF4eq : (.bindToken narrowName : MemInstruction).evaluate
    Plattform.x86_64.katalog.plattform.ziel narrowS3 entryContext = some narrowF4 :=
  Option.eq_some_iff_get_eq.mpr ⟨narrowEval3, rfl⟩

private def narrowS4 : MemState := narrowF4.advance entryContext narrowS3

private theorem narrowS4status : narrowS4.status entryContext = .laeuft := by
  simpa only [narrowS4, MemFrame.advance] using narrowS3status

private theorem narrowS4pc : (narrowS4.lokal entryContext).pc = 4 := by
  simp only [narrowS4, MemFrame.advance, Function.update_self, narrowS3pc]

private theorem narrowHead4 : narrowE.system.kopf narrowS4 entryContext = some narrowOp := by
  simp only [narrowE, memProgram, memHead, narrowS4status, narrowS4pc, narrowCode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (by rfl)]

private theorem narrowEval4 :
    (narrowOp.evaluate Plattform.x86_64.katalog.plattform.ziel narrowS4 entryContext).isSome = true := by rfl

private def narrowF5 := (narrowOp.evaluate
  Plattform.x86_64.katalog.plattform.ziel narrowS4 entryContext).get narrowEval4

private theorem narrowF5eq : narrowOp.evaluate
    Plattform.x86_64.katalog.plattform.ziel narrowS4 entryContext = some narrowF5 :=
  Option.eq_some_iff_get_eq.mpr ⟨narrowEval4, rfl⟩

private theorem narrowReach1 : narrowE.system.IErreichbar narrowS0 narrowS1 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact .start
  · exact ⟨.newSpace 0, narrowHead0, ⟨narrowF1, narrowF1eq, rfl, rfl⟩⟩

private theorem narrowReach2 : narrowE.system.IErreichbar narrowS0 narrowS2 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact narrowReach1
  · exact ⟨.mapSpace 0 0 1 mapRightsN, narrowHead1, ⟨narrowF2, narrowF2eq, rfl, rfl⟩⟩

private theorem narrowReach3 : narrowE.system.IErreichbar narrowS0 narrowS3 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact narrowReach2
  · exact ⟨.protectSpace 0 0 1 narrowRightsN, narrowHead2, ⟨narrowF3, narrowF3eq, rfl, rfl⟩⟩

private theorem narrowReach : narrowE.system.IErreichbar narrowS0 narrowS4 := by
  apply System.IErreichbar.schritt entryContext () [plan]
  · exact narrowReach3
  · exact ⟨.bindToken narrowName, narrowHead3, ⟨narrowF4, narrowF4eq, rfl, rfl⟩⟩

private def narrowToken : Zuruecknahme := Zuruecknahme.verengung 0 0 1 0

private theorem narrowHfind :
    ((narrowS4.lokal entryContext).marken.find? (fun p => p.1.val == narrowName.val)).map Prod.snd =
      some narrowToken := by rfl

private def mappedSpaceN : Adressraum := ⟨⟨0, 4096⟩, [(0, ⟨1, mapRightsN, 0⟩)], 0, []⟩

private def narrowedSpaceN : Adressraum := narrowRights mappedSpaceN 0 1 narrowRightsN

private theorem narrowHspace : (narrowS4.lokal entryContext).spaces[narrowToken.raum]? =
    some narrowedSpaceN := by rfl

private theorem narrowF5protected : narrowF5.result = some .«protected» :=
  (flush_abschluss_nicht_breiter Plattform.x86_64.katalog.plattform.ziel narrowName narrowS4
    entryContext narrowToken narrowedSpaceN narrowHfind narrowHspace (by rfl) narrowF5eq).2.2.2.2.2

private theorem narrowS4verengt : (narrowS4.lokal entryContext).verengt = [narrowToken] := by rfl

private theorem narrowF5verengt : narrowF5.verengt = [] := by rfl

private theorem narrowF5keinToken :
    ∀ t ∈ narrowF5.verengt, ∀ pg, narrowToken.contains pg → ¬ t.contains pg := by
  rw [narrowF5verengt]
  intro t h
  cases h

private theorem narrowBezeichnet : BezeichnetMem Plattform.x86_64.katalog
    { regionen := [], raeume := [], marken := [narrowName] }
    (MemTree.flushSpace narrowName).print
    (memUnit Plattform.x86_64.katalog narrowOp) .flushSpace := by
  refine ⟨MemTree.flushSpace narrowName, memParseOfPrintN _ (memFlushPrintsN narrowName), ?_⟩
  refine ⟨narrowOp, narrowElaborate, ?_⟩
  rfl

/-- **Joint satisfiability of the completion of a narrowing.** Unlike the release of an unmapped range,
    the prefix here creates a space, maps a frame with rights, performs the staged `protect` that narrows
    the table and records a pending token (`nurRechte = true`), then binds that token. In the reached state
    `flushSpace` of the bound token completes the narrowing with `.protected`, and no pending token covers
    any page of the range any more. The run is a real, reachable run of `memProgram`: no state is built by
    hand. The translation cache of this run is empty throughout (`map` invalidates its range, `protect`
    touches no cache and no `tlbFuellen` occurs), so the completion is enabled without an eviction step;
    a run with a wider cached cell would need a `tlbVerdraengen` step before `flushSpace` (THEOREM-MAP §219). -/
def FlushNarrowJointAussage : Prop :=
  ∃ (k : Katalog) (scope : MemScope) (tree : MemTree .flushSpace) (op : MemInstruction)
    (env : Katalog.Umgebung) (start : AussenStart) (text : RawText) («prefix» : List MemInstruction)
    (s : MemState) (next : MemFrame) (token : Zuruecknahme),
    let E := memProgram k («prefix» ++ [op])
    (∃ tables virt frames rights pages narrowed name,
      «prefix» = [.newSpace tables, .mapSpace 0 virt frames rights,
        .protectSpace 0 virt pages narrowed, .bindToken name] ∧ op = .flushSpace name) ∧
    Hardware k env ∧ E.ZulStart env start ∧ Annahme.Akzeptiert E ∧
    (scope.regionen.map Subtype.val).Nodup ∧ (scope.raeume.map Subtype.val).Nodup ∧
    (scope.marken.map Subtype.val).Nodup ∧
    BezeichnetMem k scope text (memUnit k op) .flushSpace ∧ MemParse text tree ∧
    elaborateMem scope tree = some op ∧
    E.system.IErreichbar (I.start E start).2 s ∧ E.system.kopf s entryContext = some op ∧
    op.evaluate k.plattform.ziel s entryContext = some next ∧
    token.nurRechte = true ∧ token ∈ (s.lokal entryContext).verengt ∧
    next.result = some .«protected» ∧ token ∉ next.verengt ∧
    (∀ t ∈ next.verengt, ∀ pg, token.contains pg → ¬ t.contains pg) ∧
    E.system.ISchritt entryContext s () [plan] (next.advance entryContext s) ∧
    E.system.ImplSchritt entryContext s () [plan] (next.advance entryContext s)

theorem flushNarrowJoint : FlushNarrowJointAussage := by
  have hprefix : ∃ tables virt frames rights pages narrowed name,
      narrowPref = [.newSpace tables, .mapSpace 0 virt frames rights,
        .protectSpace 0 virt pages narrowed, .bindToken name] ∧ narrowOp = .flushSpace name := by
    refine ⟨0, 0, 1, mapRightsN, 1, narrowRightsN, narrowName, ?_, ?_⟩ <;> rfl
  have hnodupRegion : ([] : List (List Char)).Nodup := by
    exact List.nodup_nil
  refine ⟨Plattform.x86_64.katalog,
    { regionen := [], raeume := [], marken := [narrowName] },
    MemTree.flushSpace narrowName, narrowOp, narrowEnv, narrowStart,
    (MemTree.flushSpace narrowName).print, narrowPref, narrowS4, narrowF5, narrowToken,
    hprefix, narrowHardware, narrowZul, memProgramAkzeptiertN narrowCode,
    hnodupRegion, hnodupRegion, ?_, narrowBezeichnet,
    memParseOfPrintN _ (memFlushPrintsN narrowName), narrowElaborate,
    ?_, narrowHead4, narrowF5eq, ?_, ?_, narrowF5protected, ?_, narrowF5keinToken, ?_, ?_⟩
  · change [narrowName.val].Nodup
    exact List.nodup_singleton _
  · simpa only [narrowPrefEq, narrowE, narrowS0] using narrowReach
  · rfl
  · rfl
  · exact (flush_abschluss_nicht_breiter Plattform.x86_64.katalog.plattform.ziel narrowName narrowS4
      entryContext narrowToken narrowedSpaceN narrowHfind narrowHspace (by rfl) narrowF5eq).2.1
  · exact ⟨narrowOp, narrowHead4, ⟨narrowF5, narrowF5eq, rfl, rfl⟩⟩
  · exact ⟨narrowOp, narrowHead4, ⟨narrowF5, narrowF5eq, rfl, rfl⟩⟩
  · exact ⟨narrowOp, narrowHead4, ⟨narrowF5, narrowF5eq, rfl, rfl⟩⟩

end Gabbro.Core.Ast.LowLevel
