module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Annahme.AussenLauf

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter Aussen
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

private theorem memDerivesSymbols {form : MemForm} (ts : List LocatedToken) :
    DerivesSymbols (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens))
      (ts.map Symbol.terminal) ts := by
  induction ts with
  | nil => exact DerivesSymbols.nil
  | cons t ts ih => exact DerivesSymbols.terminal ih

private theorem memDerivesTerminals {form : MemForm} {tree : MemTree form} (ts : List LocatedToken)
    (prod : tree.production (ts.map LocatedToken.value)) :
    Derives (tokenGrammar (fun tokens (t : MemTree form) => t.production tokens)) tree ts := by
  refine Derives.production (symbols := ts.map Symbol.terminal) ?_ ?_
  · exact ⟨ts, rfl, prod⟩
  · exact memDerivesSymbols ts

private theorem memParse_of {form : MemForm} {text : RawText} {tree : MemTree form}
    {pieces : List Piece} (lex : Lexed text pieces)
    (prod : tree.production (canonicalTokens pieces)) : MemParse text tree := by
  refine ⟨True.intro, pieces, lex, ?_⟩
  exact memDerivesTerminals (semanticTokens pieces) prod

private theorem rightsToken_inj : Function.Injective rightsToken := by
  intro a b h
  cases a <;> cases b <;>
    simp only [rightsToken, keyword, String.reduceToList, Token.word.injEq, List.cons.injEq,
      Char.reduceEq, reduceCtorEq] at h ⊢
  all_goals first | rfl | exact False.elim h.1

private theorem rightsToken_ne_comma (r : Speicherdienst) : rightsToken r ≠ comma := by
  intro h
  cases r <;> cases h

private theorem comma_ne_rightsToken (r : Speicherdienst) : comma ≠ rightsToken r :=
  fun h => rightsToken_ne_comma r h.symm

private theorem rightsPrint_value (r : Speicherdienst) : (rightsPrint r).value = rightsToken r := by
  cases r <;>
    simp only [rightsPrint, rightsToken, word, keyword, Identifier.print, PrintedToken.unquoted,
      String.reduceToList]

private theorem printComma_value : printComma.value = comma := by
  simp only [printComma, printPunctuation, PrintedToken.unquoted, comma, String.reduceToList]

private theorem rightsPrints_value : ∀ rs, (rightsPrints rs).map PrintedToken.value = rightsTokens rs
  | [] => rfl
  | [r] => by
      simp only [rightsPrints, rightsTokens, List.map_cons, List.map_nil,
        List.intersperse_singleton, List.intersperse_nil, rightsPrint_value]
  | r :: q :: qs => by
      simpa only [rightsPrints, rightsTokens, List.map_cons, List.intersperse_cons_cons,
        rightsPrint_value, printComma_value] using congrArg (fun l => rightsToken r :: comma :: l)
          (rightsPrints_value (q :: qs))

private def rightsKey : List Speicherdienst → List Token
  | [] => []
  | [r] => [rightsToken r]
  | r :: q :: qs => rightsToken r :: comma :: rightsKey (q :: qs)

private theorem rightsTokens_eq_key : ∀ rs, rightsTokens rs = rightsKey rs
  | [] => rfl
  | [r] => by
      simp only [rightsTokens, rightsKey, List.map_cons, List.map_nil,
        List.intersperse_singleton, List.intersperse_nil]
  | r :: q :: qs => by
      rw [show rightsTokens (r :: q :: qs) =
          rightsToken r :: comma :: rightsTokens (q :: qs) by
        simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons]]
      rw [show rightsKey (r :: q :: qs) =
          rightsToken r :: comma :: rightsKey (q :: qs) by rfl]
      rw [rightsTokens_eq_key (q :: qs)]

private theorem rightsKey_inj : Function.Injective rightsKey := by
  intro a b h
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons r rs =>
          cases rs <;> cases h
  | cons r rs ih =>
      cases rs with
      | nil =>
          cases b with
          | nil => cases h
          | cons r' rs' =>
              cases rs' with
              | nil =>
                  change [rightsToken r] = [rightsToken r'] at h
                  simp only [List.cons.injEq] at h
                  have : r = r' := rightsToken_inj h.1
                  subst r'
                  rfl
              | cons q qs =>
                  change [rightsToken r] = rightsToken r' :: comma :: rightsKey (q :: qs) at h
                  simp only [List.cons.injEq] at h
                  cases h.2
      | cons q qs =>
          cases b with
          | nil => cases h
          | cons r' rs' =>
              cases rs' with
              | nil =>
                  change rightsToken r :: comma :: rightsKey (q :: qs) = [rightsToken r'] at h
                  simp only [List.cons.injEq] at h
                  cases h.2
              | cons q' qs' =>
                  change rightsToken r :: comma :: rightsKey (q :: qs) =
                    rightsToken r' :: comma :: rightsKey (q' :: qs') at h
                  simp only [List.cons.injEq] at h
                  rcases h with ⟨hhead, htail⟩
                  rcases htail with ⟨_, htail'⟩
                  have : r = r' := rightsToken_inj hhead
                  subst r'
                  cases ih htail'
                  rfl

private theorem rightsTokens_inj {a b : List Speicherdienst}
    (h : rightsTokens a = rightsTokens b) : a = b := by
  apply rightsKey_inj
  rwa [rightsTokens_eq_key a, rightsTokens_eq_key b] at h

private theorem memProductionPrint {form : MemForm} (tree : MemTree form) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree <;>
    simp only [MemTree.production, MemTree.printPieces, rightsPrints_value, word, keyword,
      Identifier.print, PrintedToken.unquoted, printPunctuation, printDot, printOpen, printClose,
      printComma, printOpenBrace, printCloseBrace, printInteger, dot, comma, openParen, closeParen,
      openBrace, closeBrace, String.reduceToList, List.map_cons, List.map_nil, List.map_append]

private theorem memParsePrint {form : MemForm} (tree : MemTree form) : MemParse tree.print tree := by
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  apply memParse_of (text := tree.print) (tree := tree) lex
  rw [aligned]
  exact memProductionPrint tree

theorem memParse (form : MemForm) : MemParseAussage form := by
  intro text tree
  constructor
  · rintro ⟨_, pieces, lex, derives⟩
    refine ⟨pieces, lex, ?_⟩
    cases derives with
    | production prod children =>
        obtain ⟨expected, rfl, reads⟩ := prod
        change tree.production ((semanticTokens pieces).map LocatedToken.value)
        rw [children.terminalTokens]
        exact reads
  · rintro ⟨pieces, lex, prod⟩
    exact memParse_of lex prod

theorem memInversion (form : MemForm) : MemInversionAussage form := by
  intro tree tokens prod
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨pieces, lex, ?_⟩
  rw [aligned]
  have pp := memProductionPrint tree
  cases tree <;> simp only [MemTree.production] at prod pp ⊢
  all_goals exact pp.trans prod.symm

theorem memEindeutig (form : MemForm) : MemEindeutigAussage form := by
  intro a b tokens ha hb
  cases a with
  | splitAt reg point =>
      cases b with
      | splitAt reg' point' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨hn, _, _, _, hp, _⟩
          injection hn with hn
          injection hp with hp
          have heq : reg = reg' := Subtype.ext hn
          subst reg'
          subst point'
          rfl
  | splitPages reg pages =>
      cases b with
      | splitPages reg' pages' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨hn, _, _, _, hp, _⟩
          injection hn with hn
          injection hp with hp
          have heq : reg = reg' := Subtype.ext hn
          subst reg'
          subst pages'
          rfl
  | merge first second =>
      cases b with
      | merge first' second' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨_, _, hf, _, hs, _⟩
          injection hf with hf
          injection hs with hs
          have hf' : first = first' := Subtype.ext hf
          have hs' : second = second' := Subtype.ext hs
          subst first'
          subst second'
          rfl
  | newSpace tables =>
      cases b with
      | newSpace tables' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨_, _, _, _, ht, _⟩
          injection ht with ht
          have heq : tables = tables' := Subtype.ext ht
          subst tables'
          rfl
  | mapSpace space virt frames rights =>
      cases b with
      | mapSpace space' virt' frames' rights' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          have h' := h
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h'
          rcases h' with ⟨_, _, hs, _, hv, _, hf, _, _, _, hrt⟩
          injection hs with hs
          injection hv with hv
          injection hf with hf
          have hsE : space = space' := Subtype.ext hs
          have hfE : frames = frames' := Subtype.ext hf
          have hrE : rights = rights' := rightsTokens_inj (List.append_cancel_right hrt)
          subst space'
          subst virt'
          subst frames'
          subst rights'
          rfl
  | protectSpace space virt pages rights =>
      cases b with
      | protectSpace space' virt' pages' rights' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          have h' := h
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h'
          rcases h' with ⟨_, _, hs, _, hv, _, hp, _, _, _, hrt⟩
          injection hs with hs
          injection hv with hv
          injection hp with hp
          have hsE : space = space' := Subtype.ext hs
          have hrE : rights = rights' := rightsTokens_inj (List.append_cancel_right hrt)
          subst space'
          subst virt'
          subst pages'
          subst rights'
          rfl
  | unmapSpace space virt pages =>
      cases b with
      | unmapSpace space' virt' pages' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨_, _, hs, _, hv, _, hp, _⟩
          injection hs with hs
          injection hv with hv
          injection hp with hp
          have heq : space = space' := Subtype.ext hs
          subst space'
          subst virt'
          subst pages'
          rfl
  | flushSpace name =>
      cases b with
      | flushSpace name' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨_, _, hn, _⟩
          injection hn with hn
          have heq : name = name' := Subtype.ext hn
          subst name'
          rfl
  | activateSpace space =>
      cases b with
      | activateSpace space' =>
          simp only [MemTree.production] at ha hb
          have h := ha.symm.trans hb
          simp only [List.cons.injEq] at h
          rcases h with ⟨_, _, hs, _⟩
          injection hs with hs
          have heq : space = space' := Subtype.ext hs
          subst space'
          rfl

theorem memDruck (form : MemForm) : MemDruckAussage form := by
  intro tree
  exact ⟨memProductionPrint tree, memParsePrint tree⟩

theorem memRealisiert (form : MemForm) : MemRealisiertAussage form := by
  intro k scope tree op _ s c
  let target := k.plattform.ziel
  change (memHead target [op] s c = some op) ↔
    (s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
      (op.evaluate target s c).isSome = true)
  constructor
  · intro hhead
    unfold memHead at hhead
    by_cases hc : c = entryContext
    · subst c
      rw [if_pos rfl] at hhead
      cases hs : s.status entryContext with
      | laeuft =>
          rw [hs] at hhead
          cases hpc : (s.lokal entryContext).pc with
          | zero =>
              rw [hpc] at hhead
              simp only [List.getElem?_cons_zero] at hhead
              change (if (op.evaluate target s entryContext).isSome then some op else none) = some op at hhead
              by_cases he : (op.evaluate target s entryContext).isSome
              · rw [if_pos he] at hhead
                exact ⟨rfl, rfl, rfl, he⟩
              · rw [if_neg he] at hhead
                cases hhead
          | succ n =>
              rw [hpc] at hhead
              simp only [List.getElem?_cons_succ, List.getElem?_nil] at hhead
              cases hhead
      | ruht | beendet =>
          rw [hs] at hhead
          cases hhead
    · rw [if_neg hc] at hhead
      cases hhead
  · rintro ⟨hs, hc, hpc, he⟩
    subst c
    unfold memHead
    rw [if_pos rfl, hs, hpc]
    simp only [List.getElem?_cons_zero]
    exact if_pos he

theorem memRegelLokalUnit (k : Katalog) (op : MemInstruction) :
    Annahme.RegelLokal (memUnit k op) op := by
  intro c s u w p hideal
  rcases hideal with ⟨frame, heval, hp, hu⟩
  have hp' : p = plan := by simpa using hp
  subst p
  unfold Annahme.Befugt
  constructor
  · intro x hx
    cases hx
  · intro l hl
    cases hl

theorem memAnnahme (form : MemForm) : MemAnnahmeAussage form := by
  intro k scope tree op _
  exact memRegelLokalUnit k op

theorem memIdeal (form : MemForm) : MemIdealAussage form := by
  intro k scope tree op _
  unfold MemInstruction.rule Ideal.RegelBestimmt
  intro c s w es es' s1 s2 h1 h2
  rcases h1 with ⟨frame1, heval1, heq1, hs1⟩
  rcases h2 with ⟨frame2, heval2, heq2, hs2⟩
  have hframe : frame1 = frame2 := Option.some.inj (heval1.symm.trans heval2)
  subst frame2
  exact ⟨heq1.trans heq2.symm, hs1.trans hs2.symm⟩

theorem memFortschritt (form : MemForm) : MemFortschrittAussage form := by
  intro k scope tree op hop s c hhead
  left
  have hcond := (memRealisiert form k scope tree op hop s c).mp hhead
  have heval : (op.evaluate k.plattform.ziel s c).isSome := hcond.2.2.2
  obtain ⟨frame, hframe⟩ := Option.isSome_iff_exists.mp heval
  exact ⟨(), [plan], frame.advance c s, frame, hframe, rfl, rfl⟩

namespace MemInstruction

theorem stepTransfer {target} {op : MemInstruction} {c : Kontext} {s : MemState}
    {w : PUnit} {plans : List Plan} {u : MemState} (h : op.step target c s w plans u) :
    ∃ frame, op.evaluate target s c = some frame ∧ plans = [plan] ∧ u = frame.advance c s := h

theorem vollzug (target : ZielDaten) (op : MemInstruction) (frame : MemFrame)
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

theorem genauInternal {t : Nat} {c : Kontext} {s u : MemState}
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

theorem vollzugGenau {target : ZielDaten} {op : MemInstruction} {t : Nat} {c : Kontext}
    {s u : MemState} {w : PUnit} {p : Plan} {trace : SchrittSpur Nat UInt8} {next : MemState}
    (rule : op.step target c s w [p] u) (execute : FuehrtSchrittAus memSetup t c s u p trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨_, _, hp, _⟩ := stepTransfer rule
  cases (List.cons.inj hp).1
  exact genauInternal execute

end MemInstruction

end Gabbro.Core.Ast.LowLevel
