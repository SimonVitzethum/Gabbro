module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Flush.FlushJoint

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter Annahme Sicherheit Aussen

private theorem memDerivesSymbols {form : MemForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .terminal ih

private theorem memParseOfPieces {form : MemForm} {text : RawText} {tree : MemTree form}
    {pieces : List Piece} (lex : Lexed text pieces)
    (prod : tree.production (canonicalTokens pieces)) : MemParse text tree := by
  refine ⟨True.intro, pieces, lex, ?_⟩
  refine .production ⟨semanticTokens pieces, rfl, ?_⟩ (memDerivesSymbols (semanticTokens pieces))
  simpa [canonicalTokens] using prod

private theorem memParseAussage_all (form : MemForm) : MemParseAussage form := by
  intro text tree
  constructor
  · intro parsed
    change Text.Parse (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens)) text tree at parsed
    rcases parsed with ⟨root, pieces, lex, derives⟩
    refine ⟨pieces, lex, ?_⟩
    cases derives with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa [canonicalTokens, children.terminalTokens] using reads
  · rintro ⟨pieces, lex, prod⟩
    exact memParseOfPieces lex prod

private theorem memFlushPrints (name : Identifier) :
    (MemTree.flushSpace name).production
      ((MemTree.flushSpace name).printPieces.map PrintedToken.value) := by
  simp only [MemTree.production, MemTree.printPieces, word, keyword,
    Identifier.print, PrintedToken.unquoted, printPunctuation, printOpen, printClose,
    openParen, closeParen, String.reduceToList]
  rfl

private theorem memParseOfPrint {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) : MemParse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply memParseOfPieces (text := tree.print) (tree := tree) lex
  rw [aligned]
  exact prints

private theorem memInversionFlush : MemInversionAussage .flushSpace := by
  intro tree tokens prod
  cases tree with
  | flushSpace name =>
      obtain ⟨pieces, lex, aligned⟩ :=
        PrintedToken.renderLexed 0 (MemTree.flushSpace name).printPieces
      refine ⟨pieces, lex, ?_⟩
      rw [aligned]
      have hp := memFlushPrints name
      simp only [MemTree.production] at hp prod
      rw [prod, hp]

private theorem memEindeutigFlush : MemEindeutigAussage .flushSpace := by
  intro a b tokens ha hb
  cases a with
  | flushSpace na =>
      cases b with
      | flushSpace nb =>
          simp only [MemTree.production] at ha hb
          rw [ha] at hb
          have hname := congrArg (fun l : List Token => l[2]?) hb
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hname
          have hval : na.val = nb.val := by simpa using hname
          exact congrArg MemTree.flushSpace (Subtype.ext hval)

private theorem memDruckFlush : MemDruckAussage .flushSpace := by
  intro tree
  cases tree with
  | flushSpace name =>
      exact ⟨memFlushPrints name, memParseOfPrint _ (memFlushPrints name)⟩

private theorem memHeadSingleEval {target : ZielDaten} {op : MemInstruction}
    {s : MemState} {c : Kontext} (h : memHead target [op] s c = some op) :
    s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
      (op.evaluate target s c).isSome = true := by
  by_cases hc : c = entryContext
  · subst c
    cases hs : s.status entryContext with
    | laeuft =>
        cases hpc : (s.lokal entryContext).pc with
        | zero =>
            unfold memHead at h
            simp only [hs, hpc, List.getElem?_cons_zero, Option.bind_eq_bind,
              Option.bind_some, Option.pure_def, ↓reduceIte] at h
            split at h
            · rename_i heval
              exact ⟨rfl, rfl, rfl, heval⟩
            · cases h
        | succ n =>
            unfold memHead at h
            simp only [hs, hpc, List.getElem?_cons_succ, List.getElem?_nil,
              Option.bind_eq_bind, ↓reduceIte] at h
            cases h
    | ruht =>
        unfold memHead at h
        simp only [hs, ↓reduceIte] at h
        cases h
    | beendet _ =>
        unfold memHead at h
        simp only [hs, ↓reduceIte] at h
        cases h
  · unfold memHead at h
    simp only [hc] at h
    cases h

private theorem memRealisiertFlush : MemRealisiertAussage .flushSpace := by
  intro k scope tree op _ s c
  constructor
  · intro hhead
    simp only [memUnit, memProgram] at hhead
    exact memHeadSingleEval hhead
  · rintro ⟨hs, rfl, hpc, heval⟩
    simp only [memUnit, memProgram, memHead, hs, hpc, List.getElem?_cons_zero,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, ↓reduceIte]
    rw [if_pos heval]

private theorem memAnnahmeFlush : MemAnnahmeAussage .flushSpace := by
  intro k scope tree op _
  intro c s u w P hstep
  simp only [memUnit, MemInstruction.rule, MemInstruction.step] at hstep
  rcases hstep with ⟨frame, heval, hP, hu⟩
  have hPlan : P = plan := (List.cons.inj hP).1
  subst P
  rw [Annahme.Befugt]
  constructor
  · intro x hx
    cases hx
  · intro l hl
    cases hl

private theorem memIdealFlush : MemIdealAussage .flushSpace := by
  intro k scope tree op _
  intro c s w es es' s1 s2 h1 h2
  simp only [MemInstruction.rule, MemInstruction.step] at h1 h2
  rcases h1 with ⟨t1, he1, hes1, hs1⟩
  rcases h2 with ⟨t2, he2, hes2, hs2⟩
  constructor
  · rw [hes1, hes2]
  · have ht : t1 = t2 := by
      rw [he1] at he2
      cases he2
      rfl
    rw [hs1, hs2, ht]

private theorem memFortschrittFlush : MemFortschrittAussage .flushSpace := by
  intro k scope tree op _ s c hhead
  simp only [memUnit, memProgram] at hhead
  cases hEval : op.evaluate k.plattform.ziel s c with
  | none =>
      exfalso
      have h := memHeadSingleEval hhead
      rw [hEval] at h
      cases h.2.2.2
  | some frame =>
      left
      refine ⟨(), [plan], frame.advance c s, ?_⟩
      change ∃ f, op.evaluate k.plattform.ziel s c = some f ∧ [plan] = [plan] ∧
        frame.advance c s = f.advance c s
      exact ⟨frame, hEval, rfl, rfl⟩

private theorem memVollzug (frame : MemFrame) (t : Nat) (c : Kontext) (s : MemState) :
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

private theorem memGenauInternal {t : Nat} {c : Kontext} {s u : MemState}
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

private theorem memAbgleich {k : Katalog} (op : MemInstruction) :
    I.RegelAbgleich (memUnit k op) op := by
  intro hw t c w s u s' i P spur related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨frame, evaluate, planEq, hu⟩ := impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

private theorem memKomponierbar {k : Katalog} (op : MemInstruction) :
    I.RegelKomponierbar (memUnit k op).einrichtung (memUnit k op).system op := by
  intro t s c w P u head gut ideal
  obtain ⟨frame, evaluate, planEq, hu⟩ := ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq, memVollzug frame t c s⟩

private theorem memErhaltungFlush : MemErhaltungAussage .flushSpace := by
  intro k scope tree op _
  exact ⟨memAbgleich op, memKomponierbar op⟩

private theorem memRegelSicherOp {k : Katalog} (op : MemInstruction) :
    Sicherheit.RegelSicher (memSafetyUnit k op) op := by
  intro H ρ t c w vor zwischen nach P spur head impl execute
  obtain ⟨frame, _, planEq, _⟩ := impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := memGenauInternal execute
  subst spur
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (frame.advance c vor)
      (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
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

private theorem memRegelSicherFlush : MemRegelSicherAussage .flushSpace := by
  intro k scope tree op _
  exact memRegelSicherOp op

private theorem memAussenLokalOp {k : Katalog} (op : MemInstruction) :
    Annahme.AussenLokal (memUnit k op) := by
  refine ⟨Aussen.zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
      obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
      cases (List.cons.inj planEq).1
      obtain ⟨rfl, rfl⟩ := memGenauInternal execute
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

private theorem memAussenLokalFlush : MemAussenLokalAussage .flushSpace := by
  intro k scope tree op _
  exact memAussenLokalOp op

private theorem memKostenFlush : MemKostenAussage .flushSpace := by
  intro k scope tree op _ t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := impl
  cases (List.cons.inj hp).1
  exact ⟨(memGenauInternal execute).1, rfl⟩

private theorem flushMeaning : FlushMeaningAussage := by
  intro target s c name token space hfind hspace
  let frame := s.lokal c
  let granule := target.seitengranule
  obtain ⟨pair, hf, hp⟩ := Option.map_eq_some_iff.mp hfind
  rcases pair with ⟨nm, tok⟩
  change tok = token at hp
  subst tok
  have hfind' : frame.marken.find? (fun p => p.1.val == name.val) = some (nm, token) := by
    simpa only [frame] using hf
  let flushed : Adressraum :=
    { space with ausstehend := space.ausstehend.filter (fun t => t != token) }
  let next : MemFrame :=
    { frame with
      result := some (.frames (token.frames granule))
      spaces := frame.spaces.set token.raum flushed
      marken := frame.marken.filter (fun p => p.1.val != name.val && p.2 != token) }
  refine ⟨?_, ?_⟩
  · intro hcond
    have hall : (List.range token.seiten).all
        (fun i => (space.abbildung (token.seite + i)).isNone) = true := by
      rw [List.all_eq_true]
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [hcond.2.1 i hi']
      rfl
    have hmem : decide (token ∈ space.ausstehend) = true := by
      rw [decide_eq_true]
      exact hcond.1
    have hfrei : (s.lokal c).tlb.frei token.raum token.seite token.seiten = true :=
      TranslationCache.frei_eq_true.mpr hcond.2.2
    have hif : ((decide (token ∈ space.ausstehend) &&
        (List.range token.seiten).all
          (fun i => (space.abbildung (token.seite + i)).isNone)) &&
        (s.lokal c).tlb.frei token.raum token.seite token.seiten) = true := by
      simp only [hmem, hall, hfrei, Bool.and_true]
    refine ⟨next, flushed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [MemInstruction.evaluate, frame, granule, hfind', hspace,
        Option.bind_eq_bind, Option.bind_some, hif, if_true, next, flushed]
      rfl
    · simp only [next, granule]
    · have hlt : token.raum < frame.spaces.length :=
        (List.getElem?_eq_some_iff.mp hspace).1
      simp only [next, List.getElem?_set_self hlt]
    · rfl
    · intro hm
      have hm' := List.mem_filter.mp (by simpa only [flushed] using hm)
      have hne : (token != token) = false := bne_self_eq_false token
      rw [hne] at hm'
      cases hm'.2
    · intro bound hb
      have hb' := List.mem_filter.mp (by simpa only [next] using hb)
      have hne : (bound.2 != token) = true := by
        cases hfirst : (bound.1.val != name.val) <;>
          cases hsecond : (bound.2 != token) <;> simp_all
      intro heq
      rw [heq] at hne
      have hneFalse : (token != token) = false := bne_self_eq_false token
      rw [hneFalse] at hne
      cases hne
    · rfl
  · intro hbad
    have hifFalse : ((decide (token ∈ space.ausstehend) &&
        (List.range token.seiten).all
          (fun i => (space.abbildung (token.seite + i)).isNone)) &&
        (s.lokal c).tlb.frei token.raum token.seite token.seiten) = false := by
      rcases hbad with hnotmem | ⟨pg, hcpg, hisSome⟩ | hnotfrei
      · simp only [decide_eq_false hnotmem, Bool.false_and]
      · let i := pg - token.seite
        have hc1 := hcpg.1
        have hc2 := hcpg.2
        have hi_lt : i < token.seiten := by
          dsimp only [i]
          omega
        have hpgeq : token.seite + i = pg := by
          dsimp only [i]
          omega
        have hnone : (space.abbildung (token.seite + i)).isNone = false := by
          rw [hpgeq]
          cases hs : space.abbildung pg with
          | none =>
              rw [hs] at hisSome
              cases hisSome
          | some e => rfl
        cases hall' : (List.range token.seiten).all
            (fun i => (space.abbildung (token.seite + i)).isNone) with
        | false =>
            cases hmem' : decide (token ∈ space.ausstehend) <;>
              simp only [hmem', hall', Bool.false_and, Bool.and_false]
        | true =>
            exfalso
            have hit := List.all_eq_true.mp hall' i (List.mem_range.mpr hi_lt)
            rw [hnone] at hit
            cases hit
      · have hfreiFalse : (s.lokal c).tlb.frei token.raum token.seite token.seiten = false := by
          cases hf : (s.lokal c).tlb.frei token.raum token.seite token.seiten with
          | false => rfl
          | true => exact (hnotfrei (TranslationCache.frei_eq_true.mp hf)).elim
        simp only [hfreiFalse, Bool.and_false]
    simp only [MemInstruction.evaluate, frame, hfind', hspace,
      Option.bind_eq_bind, Option.bind_some, hifFalse]
    rw [if_neg Bool.false_ne_true]

theorem flush_aussage : FlushAussage := by
  exact ⟨⟨memParseAussage_all .flushSpace, memInversionFlush, memEindeutigFlush,
    memDruckFlush, memElaboriert .flushSpace, memRealisiertFlush, memAnnahmeFlush,
    memIdealFlush, memEinheit .flushSpace, memImpl .flushSpace, memFortschrittFlush,
    memErhaltungFlush, memRegelSicherFlush, memRegelAntwortSicher .flushSpace,
    memAussenLokalFlush, memKostenFlush, memSchranken, memEtiketten, memFluss⟩,
    flushMeaning, flushJointAussage⟩

end Gabbro.Core.Ast.LowLevel
