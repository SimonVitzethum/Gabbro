module

public import Core.Ast.LowLevel.Mem.Registry
public import Core.Ast.LowLevel.Mem.Proofs.Flush.FlushJoint
public import Core.Ast.LowLevel.Mem.Proofs.Kern

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
      tlb := frame.tlb.invalidate token.raum token.seite token.seiten
      spaces := frame.spaces.set token.raum flushed
      marken := frame.marken.filter (fun p => p.1.val != name.val && p.2 != token) }
  refine ⟨?_, ?_⟩
  · intro hcond
    have hall : (List.range token.seiten).all
        (fun i => (space.abbildung (token.seite + i)).isNone) = true := by
      rw [List.all_eq_true]
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [hcond.2 i hi']
      rfl
    have hmem : decide (token ∈ space.ausstehend) = true := by
      rw [decide_eq_true]
      exact hcond.1
    have hif : (decide (token ∈ space.ausstehend) &&
        (List.range token.seiten).all
          (fun i => (space.abbildung (token.seite + i)).isNone)) = true := by
      simp only [hmem, hall, Bool.true_and]
    refine ⟨next, flushed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · intro core pg hpg
      simpa only [next] using
        (TranslationCache.invalidate_hit frame.tlb token.raum token.seite token.seiten core pg hpg)
    · intro core sp pg hsp
      simpa only [next] using
        (TranslationCache.invalidate_miss frame.tlb token.raum token.seite token.seiten core sp pg hsp)
  · intro hbad
    have hifFalse : (decide (token ∈ space.ausstehend) &&
        (List.range token.seiten).all
          (fun i => (space.abbildung (token.seite + i)).isNone)) = false := by
      rcases hbad with hnotmem | ⟨pg, hcpg, hisSome⟩
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
    simp only [MemInstruction.evaluate, frame, hfind', hspace,
      Option.bind_eq_bind, Option.bind_some, hifFalse]
    rw [if_neg Bool.false_ne_true]

theorem flush_aussage : FlushAussage :=
  ⟨memObligationsKern_alle .flushSpace, flushMeaning, flushJointAussage⟩

end Gabbro.Core.Ast.LowLevel
