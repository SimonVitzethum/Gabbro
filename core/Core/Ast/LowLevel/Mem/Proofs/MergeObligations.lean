module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine Text

private theorem memParseOfPrint {form : MemForm} (tree : MemTree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) : MemParse tree.print tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 (tree.printPieces)
  refine ⟨True.intro, pieces, lexical, ?_⟩
  have symbols : ∀ ts : List LocatedToken,
      DerivesSymbols (tokenGrammar (fun tokens (tree : MemTree form) => tree.production tokens))
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

theorem memParseAussage_merge : MemParseAussage .merge := by
  intro text tree
  constructor
  · intro parsed
    rcases parsed with ⟨root, pieces, lex, derives⟩
    refine ⟨pieces, lex, ?_⟩
    cases derives with
    | production production children =>
      obtain ⟨expected, rfl, reads⟩ := production
      simpa [canonicalTokens, children.terminalTokens] using reads
  · intro found
    rcases found with ⟨pieces, lex, prod⟩
    refine ⟨True.intro, pieces, lex, ?_⟩
    have symbols : ∀ ts : List LocatedToken,
        DerivesSymbols (tokenGrammar (fun tokens (tree : MemTree .merge) => tree.production tokens))
          (ts.map Symbol.terminal) ts := by
      intro ts
      induction ts with
      | nil => exact .nil
      | cons t ts ih => exact .terminal ih
    exact .production ⟨semanticTokens pieces, rfl, by
      have hp : tree.production (canonicalTokens pieces) := prod
      simpa [canonicalTokens] using hp⟩ (symbols (semanticTokens pieces))

theorem memInversionAussage_merge : MemInversionAussage .merge := by
  intro tree tokens prod
  obtain ⟨pieces, lex, align⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨pieces, lex, ?_⟩
  rw [align]
  cases tree with
  | merge first second =>
      dsimp [MemTree.printPieces, MemTree.production] at prod ⊢
      rw [prod]
      simp only [word, Identifier.print, keyword, PrintedToken.unquoted, printPunctuation,
        printComma, printOpen, printClose, comma, openParen, closeParen, String.reduceToList,
        List.map_cons, List.map_nil, Token.word.injEq, and_true, List.cons.injEq]

theorem memEindeutigAussage_merge : MemEindeutigAussage .merge := by
  intro a b tokens hpa hpb
  cases a with
  | merge first second =>
    cases b with
    | merge first' second' =>
      dsimp [MemTree.production] at hpa hpb
      rw [hpa] at hpb
      have hf : first.val = first'.val := by
        have h := congrArg (fun l : List Token => l[2]?) hpb
        simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
          Token.word.injEq] using h
      have hs : second.val = second'.val := by
        have h := congrArg (fun l : List Token => l[4]?) hpb
        simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
          Token.word.injEq] using h
      have hfeq : first = first' := Subtype.ext hf
      have hseq : second = second' := Subtype.ext hs
      subst first'
      subst second'
      rfl

theorem memDruckAussage_merge : MemDruckAussage .merge := by
  intro tree
  cases tree with
  | merge first second =>
      constructor
      · dsimp [MemTree.production, MemTree.printPieces]
        simp only [word, Identifier.print, keyword, PrintedToken.unquoted, printPunctuation,
          printComma, printOpen, printClose, comma, openParen, closeParen, String.reduceToList,
          List.map_cons, List.map_nil, Token.word.injEq, and_true, List.cons.injEq]
      · apply memParseOfPrint
        dsimp [MemTree.production, MemTree.printPieces]
        simp only [word, Identifier.print, keyword, PrintedToken.unquoted, printPunctuation,
          printComma, printOpen, printClose, comma, openParen, closeParen, String.reduceToList,
          List.map_cons, List.map_nil, Token.word.injEq, and_true, List.cons.injEq]

theorem memRealisiertAussage_merge : MemRealisiertAussage .merge := by
  intro k scope tree op hElab s c
  constructor
  · intro hhead
    dsimp [memUnit, memProgram, memHead] at hhead ⊢
    by_cases hc : c = entryContext
    · subst c
      cases hs : s.status entryContext with
      | laeuft =>
          rw [if_pos rfl] at hhead
          rw [hs] at hhead
          by_cases hpc : (s.lokal entryContext).pc = 0
          · have hget : [op][(s.lokal entryContext).pc]? = some op := by
              rw [hpc]
              rfl
            rw [hget, Option.bind_some] at hhead
            by_cases he : (op.evaluate k.plattform.ziel s entryContext).isSome
            · rw [if_pos he] at hhead
              exact ⟨hs, rfl, hpc, he⟩
            · rw [if_neg he] at hhead
              cases hhead
          · have hlen : [op].length ≤ (s.lokal entryContext).pc := by
              simp only [List.length_cons, List.length_nil]
              omega
            have hget : [op][(s.lokal entryContext).pc]? = none :=
              List.getElem?_eq_none_iff.mpr hlen
            rw [hget, Option.bind_none] at hhead
            cases hhead
      | ruht =>
          rw [hs] at hhead
          cases hhead
      | beendet e =>
          rw [hs] at hhead
          cases hhead
    · simp only [hc] at hhead
      cases hhead
  · intro h
    obtain ⟨hc, hs, hpc, he⟩ := h
    subst c
    dsimp [memUnit, memProgram, memHead]
    rw [hs]
    have hget : [op][(s.lokal entryContext).pc]? = some op := by
      rw [hpc]
      rfl
    rw [hget, Option.bind_some]
    rw [if_pos he]

theorem memAnnahmeAussage_merge : MemAnnahmeAussage .merge := by
  intro k scope tree op hElab c s u w pl
  intro hstep
  dsimp [memUnit, memProgram, MemInstruction.rule, MemInstruction.step] at hstep
  rcases hstep with ⟨frame, heval, hplans, hu⟩
  have hpl : pl = plan := (List.cons.inj hplans).1
  subst pl
  rw [Annahme.Befugt]
  constructor
  · intro x hx
    simp only [plan] at hx
    cases hx
  · intro l hl
    simp only [plan] at hl
    cases hl

theorem memIdealAussage_merge : MemIdealAussage .merge := by
  intro k scope tree op hElab c s w es es' s1 s2 h1 h2
  dsimp [MemInstruction.rule, MemInstruction.step] at h1 h2
  rcases h1 with ⟨t1, he1, hes1, hs1⟩
  rcases h2 with ⟨t2, he2, hes2, hs2⟩
  constructor
  · rw [hes1, hes2]
  · have ht : t1 = t2 := by
      rw [he1] at he2
      cases he2
      rfl
    rw [hs1, hs2, ht]

theorem memFortschrittAussage_merge : MemFortschrittAussage .merge := by
  intro k scope tree op hElab s c hhead
  cases hEval : op.evaluate k.plattform.ziel s c with
  | none =>
      exfalso
      dsimp [memUnit, memProgram, memHead] at hhead
      by_cases hc : c = entryContext
      · subst c
        cases hs : s.status entryContext with
        | laeuft =>
            rw [if_pos rfl] at hhead
            rw [hs] at hhead
            by_cases hpc : (s.lokal entryContext).pc = 0
            · have hget : [op][(s.lokal entryContext).pc]? = some op := by
                rw [hpc]
                rfl
              rw [hget, Option.bind_some] at hhead
              by_cases he : (op.evaluate k.plattform.ziel s entryContext).isSome
              · rw [if_pos he] at hhead
                rw [hEval] at he
                cases he
              · rw [if_neg he] at hhead
                cases hhead
            · have hlen : [op].length ≤ (s.lokal entryContext).pc := by
                simp only [List.length_cons, List.length_nil]
                omega
              have hget : [op][(s.lokal entryContext).pc]? = none :=
                List.getElem?_eq_none_iff.mpr hlen
              rw [hget, Option.bind_none] at hhead
              cases hhead
        | ruht =>
            rw [hs] at hhead
            cases hhead
        | beendet e =>
            rw [hs] at hhead
            cases hhead
      · simp only [hc] at hhead
        cases hhead
  | some transfer =>
      left
      refine ⟨(), [plan], transfer.advance c s, ?_⟩
      exact ⟨transfer, hEval, rfl, rfl⟩

end Gabbro.Core.Ast.LowLevel
