module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine

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

private theorem printCommaVal : printComma.value = comma := rfl

private theorem map_intersperse {α β : Type} (f : α → β) (sep : α) : ∀ xs : List α,
    (xs.intersperse sep).map f = (xs.map f).intersperse (f sep)
  | [] => rfl
  | [_] => rfl
  | x :: y :: ys => by
      simp only [List.intersperse_cons_cons, List.map_cons, map_intersperse f sep (y :: ys)]

private theorem rightsPrint_val_fun : (fun r : Speicherdienst => (rightsPrint r).value) = rightsToken := by
  funext r
  cases r <;> rfl

private theorem rightsPrints_value_aux (rights : List Speicherdienst) :
    (rights.map (fun r => (rightsPrint r).value)).intersperse comma = rightsTokens rights := by
  induction rights with
  | nil => rfl
  | cons right rights ih =>
      cases rights with
      | nil => cases right <;> rfl
      | cons r2 rs =>
          cases r2 <;>
            simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons, List.map_map,
              rightsPrint_val_fun, ih]

private theorem rightsPrints_value (rights : List Speicherdienst) :
    (rightsPrints rights).map PrintedToken.value = rightsTokens rights := by
  rw [rightsPrints]
  rw [map_intersperse]
  rw [printCommaVal]
  simp only [List.map_map]
  exact rightsPrints_value_aux rights

private theorem memPrintProduction {form : MemForm} (tree : MemTree form) :
    tree.production (tree.printPieces.map PrintedToken.value) := by
  cases tree <;> simp only [MemTree.production, MemTree.printPieces]
  all_goals
    simp only [rightsPrints_value, rightsTokens, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, word, Identifier.print, PrintedToken.unquoted, keyword,
      printOpen, printPunctuation, printClose, printComma, printInteger,
      printOpenBrace, printCloseBrace, printDot, dot, openParen, closeParen, comma,
      openBrace, closeBrace] <;> rfl

private theorem memPrintValueEqTokens {form : MemForm} (tree : MemTree form) (tokens : List Token)
    (prod : tree.production tokens) : tree.printPieces.map PrintedToken.value = tokens := by
  cases tree <;> simp only [MemTree.production, MemTree.printPieces] at prod ⊢
  all_goals
    subst tokens
    simp only [rightsPrints_value, rightsTokens, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, word, Identifier.print, PrintedToken.unquoted, keyword,
      printOpen, printPunctuation, printClose, printComma, printInteger,
      printOpenBrace, printCloseBrace, printDot, dot, openParen, closeParen, comma,
      openBrace, closeBrace] <;> rfl

private theorem memParseOfPrint {form : MemForm} (tree : MemTree form) : MemParse tree.print tree := by
  obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨True.intro, pieces, lexed, ?_⟩
  apply memDerivesTerminals (semanticTokens pieces)
  change tree.production (canonicalTokens pieces)
  rw [aligned]
  exact memPrintProduction tree

theorem mapMemParse (form : MemForm) : MemParseAussage form := by
  intro text tree
  constructor
  · intro parsed
    rcases parsed with ⟨_, pieces, lexed, derives⟩
    refine ⟨pieces, lexed, ?_⟩
    cases derives with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        have h : semanticTokens pieces = expected := DerivesSymbols.terminalTokens children
        simpa [canonicalTokens, h] using reads
  · rintro ⟨pieces, lexed, prod⟩
    refine ⟨True.intro, pieces, lexed, ?_⟩
    exact memDerivesTerminals (semanticTokens pieces) (by simpa [canonicalTokens] using prod)

theorem mapMemInversion (form : MemForm) : MemInversionAussage form := by
  intro tree tokens prod
  obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 tree.printPieces
  refine ⟨pieces, lexed, ?_⟩
  rw [aligned]
  exact memPrintValueEqTokens tree tokens prod

theorem mapMemDruck (form : MemForm) : MemDruckAussage form := by
  intro tree
  exact ⟨memPrintProduction tree, memParseOfPrint tree⟩

private theorem rightsToken_injective : Function.Injective rightsToken := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

private theorem rightsTokens_inj : ∀ {a b : List Speicherdienst}, rightsTokens a = rightsTokens b → a = b
  | [], [] => fun _ => rfl
  | [], rb :: bs => fun h => by
      cases bs with
      | nil =>
          simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
            List.intersperse_singleton] at h
          cases h
      | cons b2 bs2 =>
          simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
            List.intersperse_cons_cons] at h
          exact (List.cons_ne_nil _ _ h.symm).elim
  | ra :: as, [] => fun h => by
      cases as with
      | nil =>
          simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
            List.intersperse_singleton] at h
          cases h
      | cons a2 as2 =>
          simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
            List.intersperse_cons_cons] at h
          exact (List.cons_ne_nil _ _ h).elim
  | ra :: as, rb :: bs => fun h => by
      cases as with
      | nil =>
          cases bs with
          | nil =>
              simp only [rightsTokens, List.map_nil, List.intersperse_nil, List.map_cons,
                List.intersperse_singleton] at h
              have hra : ra = rb := rightsToken_injective (by simpa using (List.cons.inj h).1)
              subst rb
              rfl
          | cons b2 bs2 =>
              simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons,
                List.intersperse_singleton] at h
              exact (List.cons_ne_nil _ _ (List.cons.inj h).2.symm).elim
      | cons a2 as2 =>
          cases bs with
          | nil =>
              simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons,
                List.intersperse_singleton] at h
              exact (List.cons_ne_nil _ _ (List.cons.inj h).2).elim
          | cons b2 bs2 =>
              simp only [rightsTokens, List.map_cons, List.intersperse_cons_cons] at h
              have hra : ra = rb := rightsToken_injective (List.cons.inj h).1
              have htail := (List.cons.inj h).2
              have hrest : rightsTokens (a2 :: as2) = rightsTokens (b2 :: bs2) := (List.cons.inj htail).2
              have heq : a2 :: as2 = b2 :: bs2 := rightsTokens_inj hrest
              subst rb
              cases heq
              rfl

theorem mapEindeutig : MemEindeutigAussage .mapSpace := by
  intro a b tokens ha hb
  cases a with
  | mapSpace space virt frames rights =>
      cases b with
      | mapSpace space' virt' frames' rights' =>
          simp only [MemTree.production] at ha hb
          rw [ha] at hb
          simp only [List.cons_append, List.nil_append] at hb
          have h1 := List.cons.inj hb
          have h2 := List.cons.inj h1.2
          have h3 := List.cons.inj h2.2
          have h4 := List.cons.inj h3.2
          have h5 := List.cons.inj h4.2
          have h6 := List.cons.inj h5.2
          have h7 := List.cons.inj h6.2
          have h8 := List.cons.inj h7.2
          have h9 := List.cons.inj h8.2
          have h10 := List.cons.inj h9.2
          have hsp : space = space' := Subtype.ext (by simpa using h3.1)
          have hvi : virt = virt' := by simpa using h5.1
          have hfr : frames = frames' := Subtype.ext (by simpa using h7.1)
          cases hsp
          cases hvi
          cases hfr
          have hmid : rightsTokens rights ++ [closeBrace, closeParen, keyword "else", keyword "full"] =
              rightsTokens rights' ++ [closeBrace, closeParen, keyword "else", keyword "full"] := h10.2
          have hr := rightsTokens_inj (List.append_cancel_right hmid)
          cases hr
          rfl

end Gabbro.Core.Ast.LowLevel
