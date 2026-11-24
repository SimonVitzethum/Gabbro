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

end Gabbro.Core.Ast.LowLevel
