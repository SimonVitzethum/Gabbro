module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Waechter Katalog Maschine Text
open Gabbro.Core.Annahme
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

/-! Joint satisfiability and meaning of `unmap`. The generic part of the
memory obligations is proved for the form at hand; the two unmap-specific
parts use a concrete admissible prefix `newSpace; mapSpace`. -/

theorem unmapMemParse (form : MemForm) : MemParseAussage form := by
  intro text tree
  constructor
  · intro parsed
    rcases parsed with ⟨_, pieces, lex, derives⟩
    refine ⟨pieces, lex, ?_⟩
    cases derives with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa [canonicalTokens, children.terminalTokens] using reads
  · rintro ⟨pieces, lex, prod⟩
    refine ⟨True.intro, pieces, lex, ?_⟩
    have symbols : ∀ ts : List LocatedToken,
        DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
          (ts.map Symbol.terminal) ts := by
      intro ts
      induction ts with
      | nil => exact .nil
      | cons t ts ih => exact .terminal ih
    exact .production ⟨semanticTokens pieces, rfl, by simpa [canonicalTokens] using prod⟩
      (symbols (semanticTokens pieces))

theorem memUnmapPrints (tree : MemTree .unmapSpace) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree with
  | unmapSpace space virt pages =>
      simp only [MemTree.production, MemTree.printPieces, keyword, word, Identifier.print,
        PrintedToken.unquoted, printPunctuation, printOpen, printClose, printComma,
        printInteger, openParen, comma, closeParen, String.reduceToList,
        List.map_cons, List.map_nil]

theorem unmapMemParseOfPrint {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) :
    MemParse tree.print tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨True.intro, pieces, lexical, ?_⟩
  have symbols : ∀ ts : List LocatedToken,
      DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
        (ts.map Symbol.terminal) ts := by
    intro ts
    induction ts with
    | nil => exact .nil
    | cons t ts ih => exact .terminal ih
  exact .production ⟨semanticTokens pieces, rfl, by
    have hp : tree.production (canonicalTokens pieces) := by
      rw [align]
      exact prints
    simpa [canonicalTokens] using hp⟩ (symbols (semanticTokens pieces))

theorem memInversionUnmap : MemInversionAussage .unmapSpace := by
  intro tree tokens prod
  cases tree with
  | unmapSpace space virt pages =>
      let t : MemTree .unmapSpace := .unmapSpace space virt pages
      obtain ⟨pieces, lex, align⟩ := PrintedToken.renderLexed 0 t.printPieces
      refine ⟨pieces, lex, ?_⟩
      rw [align]
      exact (memUnmapPrints t).trans prod.symm

private theorem memUnmapUnique {tokens : List Token} {a b : MemTree .unmapSpace}
    (ha : a.production tokens) (hb : b.production tokens) : a = b := by
  cases a with
  | unmapSpace space virt pages =>
      cases b with
      | unmapSpace space' virt' pages' =>
          simp only [MemTree.production] at ha hb
          rw [ha] at hb
          simp only [List.cons.injEq, Token.word.injEq, Token.natural.injEq,
            eq_self, true_and] at hb
          rcases hb with ⟨hspace, hvirt, hpages⟩
          have hs : space = space' := Subtype.ext hspace
          subst space'
          subst virt'
          have hp : pages = pages' := hpages.1
          subst pages'
          rfl

theorem memEindeutigUnmap : MemEindeutigAussage .unmapSpace := by
  intro a b tokens ha hb
  exact memUnmapUnique ha hb

theorem memDruckUnmap : MemDruckAussage .unmapSpace := by
  intro tree
  exact ⟨memUnmapPrints tree, unmapMemParseOfPrint tree (memUnmapPrints tree)⟩

theorem unmapMemRealisiert (form : MemForm) : MemRealisiertAussage form := by
  intro k scope tree op hElab s c
  constructor
  · intro hhead
    change (if c = entryContext then
        match s.status c with
        | .laeuft => do
          let i ← [op][(s.lokal c).pc]?
          if (i.evaluate k.plattform.ziel s c).isSome then some i else none
        | .ruht | .beendet _ => none
      else none) = some op at hhead
    by_cases hc : c = entryContext
    · rw [hc] at hhead ⊢
      cases hs : s.status entryContext with
      | laeuft =>
          cases hpc : (s.lokal entryContext).pc with
          | zero =>
              simp only [hs, hpc, List.getElem?_cons_zero, Bind.bind, Option.bind,
                Option.bind_some, if_true, ↓reduceIte] at hhead
              have heval : (op.evaluate k.plattform.ziel s entryContext).isSome = true := by
                by_contra hnot
                rw [if_neg hnot] at hhead
                cases hhead
              exact ⟨rfl, rfl, rfl, heval⟩
          | succ n =>
              simp only [hs, hpc, List.getElem?_cons_succ, List.getElem?_nil,
                Option.bind_none] at hhead
              cases hhead
      | ruht => simp only [hs] at hhead; cases hhead
      | beendet e => simp only [hs] at hhead; cases hhead
    · simp only [hc] at hhead
      cases hhead
  · rintro ⟨hs, hc, hpc, heval⟩
    subst c
    change (if entryContext = entryContext then
        match s.status entryContext with
        | .laeuft => do
          let i ← [op][(s.lokal entryContext).pc]?
          if (i.evaluate k.plattform.ziel s entryContext).isSome then some i else none
        | .ruht | .beendet _ => none
      else none) = some op
    rw [hs, hpc]
    simp only [List.getElem?_cons_zero, Bind.bind, Option.bind, Option.bind_some,
      if_pos heval, if_true, ↓reduceIte]

theorem unmapMemAnnahme (form : MemForm) : MemAnnahmeAussage form := by
  intro k scope tree op hElab
  unfold Annahme.RegelLokal
  intro c s u w P hideal
  simp only [memUnit, memProgram, MemInstruction.rule, MemInstruction.step] at hideal
  have hP' : P = plan := by
    rcases hideal with ⟨frame, heval, hP, hu⟩
    simpa using hP
  subst P
  rw [Annahme.Befugt]
  have hfuss : plan.fuss = [] := rfl
  have hlesen : plan.lesen = [] := rfl
  rw [hfuss, hlesen]
  constructor
  · intro x hx; cases hx
  · intro l hl; cases hl

theorem unmapMemIdeal (form : MemForm) : MemIdealAussage form := by
  intro k scope tree op hElab
  change Gabbro.Core.Ideal.RegelBestimmt (MemInstruction.rule k.plattform.ziel op)
  intro c s w es es' s1 s2 h1 h2
  rcases h1 with ⟨f1, he1, hes1, hs1⟩
  rcases h2 with ⟨f2, he2, hes2, hs2⟩
  constructor
  · rw [hes1, hes2]
  · have hf : f1 = f2 := by rw [he1] at he2; cases he2; rfl
    rw [hs1, hs2, hf]

theorem unmapMemFortschritt (form : MemForm) : MemFortschrittAussage form := by
  intro k scope tree op hElab s c hhead
  change memHead k.plattform.ziel [op] s c = some op at hhead
  cases hEval : op.evaluate k.plattform.ziel s c with
  | none =>
      exfalso
      by_cases hc : c = entryContext
      · subst c
        cases hs : s.status entryContext with
        | laeuft =>
            cases hpc : (s.lokal entryContext).pc with
            | zero =>
                simp only [memHead, hs, hpc, List.getElem?_cons_zero, Bind.bind,
                  Option.bind, Option.bind_some, if_true, ↓reduceIte] at hhead
                by_cases his : (op.evaluate k.plattform.ziel s entryContext).isSome = true
                · rw [if_pos his] at hhead
                  rw [hEval] at his
                  cases his
                · rw [if_neg his] at hhead
                  cases hhead
            | succ n =>
                simp only [memHead, hs, hpc, List.getElem?_cons_succ, List.getElem?_nil,
                  Option.bind_none] at hhead
                cases hhead
        | ruht => simp only [memHead, hs] at hhead; cases hhead
        | beendet e => simp only [memHead, hs] at hhead; cases hhead
      · simp only [memHead, hc] at hhead
        cases hhead
  | some frame =>
      left
      exact ⟨(), [plan], frame.advance c s, ⟨frame, hEval, rfl, rfl⟩⟩

private theorem filter_range_find_none (base pages pg : Nat) (hpg : pageRange base pages pg)
    (entries : List (Nat × Seiteneintrag)) :
    (entries.filter (fun (page, _) => !decide (pageRange base pages page))).find?
        (fun entry => entry.1 == pg) = none := by
  apply List.find?_eq_none.mpr
  rintro ⟨page, entry⟩ hmem
  have hnot := (List.mem_filter.mp hmem).2
  by_cases heq : page = pg
  · subst page
    change (!decide (pageRange base pages pg)) = true at hnot
    have hd : decide (pageRange base pages pg) = true := decide_eq_true hpg
    rw [hd] at hnot
    cases hnot
  · intro h
    exact heq (beq_iff_eq.mp h)

private theorem filter_range_find_keep (base pages pg : Nat) (hpg : ¬ pageRange base pages pg) :
    ∀ entries : List (Nat × Seiteneintrag),
    (entries.filter (fun (page, _) => !decide (pageRange base pages page))).find?
        (fun entry => entry.1 == pg) = entries.find? (fun entry => entry.1 == pg) := by
  intro entries
  induction entries with
  | nil => rfl
  | cons e es ih =>
      rcases e with ⟨page, entry⟩
      by_cases hin : pageRange base pages page
      · have hne : page ≠ pg := by intro heq; subst page; exact hpg hin
        simp only [List.filter_cons, hin, decide_true, Bool.not_true, if_false,
          Bool.false_eq_true, List.find?_cons, beq_eq_false_iff_ne.mpr hne, ih]
      · simp only [List.filter_cons, hin, decide_false, Bool.not_false, if_true,
          List.find?_cons, ih]

theorem unmap_meaning : UnmapMeaningAussage := by
  intro target s c sp virt pages space first hspace
  dsimp only
  intro hfirst hvalid hframes
  let granule := target.seitengranule
  let base := virt / granule
  have hcond : (List.range pages).all (fun i =>
      ((space.abbildung (base + i)).map Seiteneintrag.frame) == some (first.frame + i)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    have hip : i < pages := List.mem_range.mp hi
    rw [hframes i hip]
    exact beq_self_eq_true _
  let token : Zuruecknahme := ⟨sp, base, pages, space.generation + 1, first.frame⟩
  let entries := space.entries.filter (fun (page, _) => !decide (pageRange base pages page))
  let cleared : Adressraum := ⟨space.tabellen, entries, token.generation,
    token :: space.ausstehend⟩
  let next : MemFrame := { s.lokal c with result := some (.pending token), spaces := (s.lokal c).spaces.set sp cleared }
  have hcond' : (List.range pages).all (fun i =>
      ((space.abbildung (virt / target.seitengranule + i)).map Seiteneintrag.frame) ==
        some (first.frame + i)) = true := by
    simpa only [base, granule] using hcond
  have heval : (MemInstruction.unmapSpace sp virt pages).evaluate target s c = some next := by
    simp only [MemInstruction.evaluate, hspace, hfirst, hvalid, hcond', Bind.bind,
      Option.bind, Option.bind_some, Option.pure_def, and_true, if_true, ↓reduceIte]
    dsimp [next, token, cleared, entries, base, granule]
  refine ⟨next, cleared, token, heval, rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, ?_⟩
  · have hlt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hspace).1
    dsimp [next]
    rw [List.getElem?_set_self hlt]
  · intro pg hpg
    change ((space.entries.filter (fun (page, _) => !decide (pageRange base pages page))).find?
      (fun entry => entry.1 == pg)).map Prod.snd = none
    rw [filter_range_find_none base pages pg hpg space.entries]
    rfl
  · intro pg hpg
    change ((space.entries.filter (fun (page, _) => !decide (pageRange base pages page))).find?
      (fun entry => entry.1 == pg)).map Prod.snd =
      (space.entries.find? (fun entry => entry.1 == pg)).map Prod.snd
    rw [filter_range_find_keep base pages pg hpg space.entries]
  · intro extent hsep
    have hlt : sp < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp hspace).1
    dsimp [next]
    unfold MemFrame.unreserved
    rw [List.all_eq_false]
    refine ⟨cleared, List.mem_set hlt cleared, ?_⟩
    have hd : decide (extent.getrennt (token.frames target.seitengranule)) = false := by
      simpa only [granule] using decide_eq_false hsep
    dsimp [cleared]
    rw [hd]
    simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, not_false_eq_true]

theorem unmapMemImplTransfer {k : Katalog} {op : MemInstruction} {c : Kontext} {s : MemState}
    (w : PUnit) {plans : List Plan} {u : MemState} (h : op.step k.plattform.ziel c s w plans u) :
    ∃ frame, op.evaluate k.plattform.ziel s c = some frame ∧ plans = [plan] ∧
      u = frame.advance c s := by
  cases he : op.evaluate k.plattform.ziel s c with
  | none =>
      unfold MemInstruction.step at h
      rw [he] at h
      rcases h with ⟨frame, hframe, _, _⟩
      cases hframe
  | some frame =>
      unfold MemInstruction.step at h
      rw [he] at h
      rcases h with ⟨frame', hframe, hp, hu⟩
      cases hframe
      exact ⟨frame, rfl, hp, hu⟩

theorem unmapMemGenauInternal {t : Nat} {c : Kontext} {s u : MemState}
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

theorem unmapMemVollzug (k : Katalog) (op : MemInstruction) (frame : MemFrame)
    (t : Nat) (c : Kontext) (s : MemState) :
    FuehrtSchrittAus memSetup t c s (frame.advance c s) plan ⟨[], []⟩ (frame.advance c s) := by
  refine ⟨?_, ?_, [], frame.advance c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [plan] at hl
    cases hl
  · change FuehrtAus memSetup t c s (frame.advance c s) .intern [] [] (frame.advance c s)
    exact FuehrtAus.intern
  · change Speicherfolge s.initial (.kontext c) s.graph [] [] (frame.advance c s).graph
    exact Speicherfolge.nil _

theorem unmapMemAbgleich {k : Katalog} (op : MemInstruction) :
    I.RegelAbgleich (memUnit k op) op := by
  intro hw t c w s u s' i stepPlan trace related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨frame, evaluate, planEq, hu⟩ := unmapMemImplTransfer (k := k) (op := op) w impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

theorem unmapMemKomponierbar {k : Katalog} (op : MemInstruction) :
    I.RegelKomponierbar memSetup (memUnit k op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨frame, evaluate, planEq, hu⟩ := unmapMemImplTransfer (k := k) (op := op) w ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq, unmapMemVollzug k op frame t c s⟩

theorem unmapMemRegelSicher {k : Katalog} (op : MemInstruction) :
    Gabbro.Core.Sicherheit.RegelSicher (memSafetyUnit k op) op := by
  intro H ρ t c w vor zwischen nach stepPlan trace head impl execute
  obtain ⟨frame, _, planEq, _⟩ := unmapMemImplTransfer (k := k) (op := op) w impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := unmapMemGenauInternal execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (frame.advance c vor) (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
    Or.inr ⟨ohneAbsturz, (List.append_nil _).symm⟩
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => ordered, ?_, ?_⟩
  · intro i actor access recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    exact nomatch alive.symm.trans lost
  · intro _
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared _
    change [][i]? = some d at declared
    cases declared
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

theorem unmapMemAussenLokal {k : Katalog} (op : MemInstruction) :
    Gabbro.Core.Annahme.AussenLokal (memUnit k op) := by
  refine ⟨Aussen.zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
      obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
      cases (List.cons.inj planEq).1
      obtain ⟨rfl, rfl⟩ := unmapMemGenauInternal execute
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

theorem unmapMemKosten {k : Katalog} (op : MemInstruction) :
    ∀ t c s w middle next p trace, op.step k.plattform.ziel c s w [p] middle →
      FuehrtSchrittAus memSetup t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (memUnit k op).stotterLaenge op = 0 := by
  intro t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := unmapMemImplTransfer (k := k) (op := op) w impl
  cases (List.cons.inj hp).1
  exact ⟨(unmapMemGenauInternal execute).1, rfl⟩

end Gabbro.Core.Ast.LowLevel
