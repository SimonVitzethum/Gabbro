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

private theorem memProductionPrint {form : MemForm} (tree : MemTree form) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree <;>
    simp only [MemTree.production, MemTree.printPieces, rightsPrints, rightsPrint, rightsTokens,
      rightsToken, word, keyword, Identifier.print, PrintedToken.unquoted, printPunctuation,
      printDot, printOpen, printClose, printComma, printOpenBrace, printCloseBrace, printInteger,
      dot, comma, openParen, closeParen, openBrace, closeBrace, String.reduceToList,
      List.map_cons, List.map_nil, List.intersperse_nil, List.intersperse_cons_cons]

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
        rw [children.terminalTokens]
        exact reads
  · rintro ⟨pieces, lex, prod⟩
    exact memParse_of lex prod

theorem memInversion (form : MemForm) : MemInversionAussage form := by
  intro tree tokens prod
  obtain ⟨pieces, lex, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨pieces, lex, ?_⟩
  rw [aligned]
  have printEq := memProductionPrint tree
  exact (prod.trans printEq.symm).symm

private theorem rightsToken_inj : Function.Injective rightsToken := by
  intro a b h
  cases a <;> cases b <;>
    simp only [rightsToken, keyword, String.reduceToList, Token.word.injEq, reduceCtorEq] at h ⊢

private theorem rightsToken_ne_comma (r : Speicherdienst) : rightsToken r ≠ comma := by
  cases r <;>
    simp only [rightsToken, keyword, comma, String.reduceToList, Token.noConfusion]

private theorem comma_ne_rightsToken (r : Speicherdienst) : comma ≠ rightsToken r :=
  fun h => rightsToken_ne_comma r h.symm

private theorem rightsTokens_inj {a b : List Speicherdienst}
    (h : rightsTokens a = rightsTokens b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons r rs =>
          simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
            List.intersperse_cons_cons] at h
          cases h
  | cons r rs ih =>
      cases b with
      | nil =>
          simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
            List.intersperse_cons_cons] at h
          cases h
      | cons r' rs' =>
          cases rs with
          | nil =>
              cases rs' with
              | nil =>
                  simp only [rightsTokens, List.map_cons, List.map_nil, List.intersperse_nil] at h
                  have hrr : r = r' := rightsToken_inj h
                  subst r'
                  rfl
              | cons q qs =>
                  simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons] at h
                  simp only [List.cons.injEq] at h
                  exact (rightsToken_ne_comma q h.2.1).elim
          | cons q qs =>
              cases rs' with
              | nil =>
                  simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons] at h
                  simp only [List.cons.injEq] at h
                  exact (comma_ne_rightsToken q h.2.1).elim
              | cons q' qs' =>
                  simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons] at h
                  simp only [List.cons.injEq] at h
                  rcases h with ⟨hr, _, hrest⟩
                  have hrr : r = r' := rightsToken_inj hr
                  subst r'
                  have tailEq : q :: qs = q' :: qs' := ih hrest
                  subst tailEq
                  rfl

theorem memEindeutig (form : MemForm) : MemEindeutigAussage form := by
  intro a b tokens ha hb
  cases a with
  | splitAt reg point =>
      cases b with
      | splitAt reg' point' =>
          simp only [MemTree.production] at ha hb
          have h := ha.trans hb.symm
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
          have h := ha.trans hb.symm
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
          have h := ha.trans hb.symm
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
          have h := ha.trans hb.symm
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
          have h := ha.trans hb.symm
          have hs : space = space' := by
            have hs' := congrArg (fun l : List Token => l[2]?) h
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
              Token.word.injEq] at hs'
            exact Subtype.ext hs'
          have hv : virt = virt' := by
            have hv' := congrArg (fun l : List Token => l[4]?) h
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
              Token.natural.injEq] at hv'
            exact hv'
          have hf : frames = frames' := by
            have hf' := congrArg (fun l : List Token => l[6]?) h
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
              Token.word.injEq] at hf'
            exact Subtype.ext hf'
          have hr : rights = rights' := by
            have h' := h
            simp only [List.cons_append, List.nil_append, List.cons.injEq,
              eq_self_iff_true, true_and] at h'
            exact rightsTokens_inj (List.append_cancel_right h')
          subst space'
          subst virt'
          subst frames'
          subst rights'
          rfl
  | protectSpace space virt pages rights =>
      cases b with
      | protectSpace space' virt' pages' rights' =>
          simp only [MemTree.production] at ha hb
          have h := ha.trans hb.symm
          have hs : space = space' := by
            have hs' := congrArg (fun l : List Token => l[2]?) h
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
              Token.word.injEq] at hs'
            exact Subtype.ext hs'
          have hv : virt = virt' := by
            have hv' := congrArg (fun l : List Token => l[4]?) h
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
              Token.natural.injEq] at hv'
            exact hv'
          have hp : pages = pages' := by
            have hp' := congrArg (fun l : List Token => l[6]?) h
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
              Token.natural.injEq] at hp'
            exact hp'
          have hr : rights = rights' := by
            have h' := h
            simp only [List.cons_append, List.nil_append, List.cons.injEq,
              eq_self_iff_true, true_and] at h'
            exact rightsTokens_inj (List.append_cancel_right h')
          subst space'
          subst virt'
          subst pages'
          subst rights'
          rfl
  | unmapSpace space virt pages =>
      cases b with
      | unmapSpace space' virt' pages' =>
          simp only [MemTree.production] at ha hb
          have h := ha.trans hb.symm
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
          have h := ha.trans hb.symm
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
          have h := ha.trans hb.symm
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
  constructor
  · intro hhead
    unfold memHead at hhead
    by_cases hc : c = entryContext
    · simp only [hc, ↓reduceIte] at hhead
      cases hs : s.status c with
      | laeuft =>
          simp only [hs] at hhead
          cases hpc : (s.lokal c).pc with
          | zero =>
              simp only [List.getElem?_cons_zero] at hhead
              by_cases he : (op.evaluate target s c).isSome
              · simp only [if_pos he] at hhead
                exact ⟨hs, hc, hpc, he⟩
              · simp only [if_neg he] at hhead
                cases hhead
          | succ n =>
              simp only [List.getElem?_cons_succ, List.getElem?_nil] at hhead
              cases hhead
      | ruht | beendet => cases hhead
    · simp only [hc, ↓reduceIte] at hhead
      cases hhead
  · rintro ⟨hs, hc, hpc, he⟩
    unfold memHead
    simp only [hc, ↓reduceIte, hs, hpc, List.getElem?_cons_zero]
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
  have hframe : frame1 = frame2 := by rw [← heval1, heval2]
  subst frame2
  exact ⟨heq1.trans heq2.symm, hs1.trans hs2.symm⟩

theorem memHead_eval_some {target} {code : List MemInstruction} {s : MemState} {c : Kontext}
    {op : MemInstruction} (h : memHead target code s c = some op) :
    ∃ frame, op.evaluate target s c = some frame := by
  unfold memHead at h
  by_cases hc : c = entryContext
  · simp only [hc, ↓reduceIte] at h
    cases hs : s.status c with
    | laeuft =>
        simp only [hs] at h
        cases hget : code[(s.lokal c).pc]? with
        | none => cases h
        | some op' =>
            simp only [hget] at h
            by_cases he : (op'.evaluate target s c).isSome
            · simp only [if_pos he] at h
              injection h with hop
              subst op
              obtain ⟨frame, hframe⟩ := Option.isSome_iff_exists.mp he
              exact ⟨frame, hframe⟩
            · simp only [if_neg he] at h
              cases h
    | ruht | beendet => cases h
  · simp only [hc, ↓reduceIte] at h
    cases h

theorem memFortschritt (form : MemForm) : MemFortschrittAussage form := by
  intro k scope tree op _ s c hhead
  left
  obtain ⟨frame, heval⟩ := memHead_eval_some hhead
  exact ⟨(), [plan], frame.advance c s, frame, heval, rfl, rfl⟩

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
