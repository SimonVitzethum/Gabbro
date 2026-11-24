module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine

open Text Katalog Maschine

theorem rightsTokens_nil : rightsTokens [] = [] := rfl
theorem rightsTokens_single (r : Speicherdienst) : rightsTokens [r] = [rightsToken r] := rfl
theorem rightsTokens_cons_cons (r s : Speicherdienst) (rs : List Speicherdienst) :
    rightsTokens (r :: s :: rs) = rightsToken r :: comma :: rightsTokens (s :: rs) := rfl

theorem keyword_ne {a b : String} (h : a ≠ b) : keyword a ≠ keyword b := by
  intro eq
  exact h (String.toList_injective (Token.word.inj eq))

theorem rightsToken_injective : Function.Injective rightsToken := by
  intro a b h
  cases a <;> cases b <;> simp only [rightsToken] at h ⊢
  all_goals first
    | rfl
    | exact False.elim ((keyword_ne (by decide)) h)

theorem rightsTokens_inj (first second : List Speicherdienst)
    (h : rightsTokens first = rightsTokens second) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons r rs =>
          cases rs with
          | nil => rw [rightsTokens_nil, rightsTokens_single] at h; cases h
          | cons r2 rs2 => rw [rightsTokens_nil, rightsTokens_cons_cons] at h; cases h
  | cons r rs ih =>
      cases second with
      | nil =>
          cases rs with
          | nil => rw [rightsTokens_single, rightsTokens_nil] at h; cases h
          | cons r2 rs2 => rw [rightsTokens_cons_cons, rightsTokens_nil] at h; cases h
      | cons r' rs' =>
          cases rs with
          | nil =>
              cases rs' with
              | nil =>
                  rw [rightsTokens_single, rightsTokens_single] at h
                  have hr : r = r' := rightsToken_injective (List.cons.inj h).1
                  rw [← hr]
              | cons r2 rs2 =>
                  rw [rightsTokens_single, rightsTokens_cons_cons] at h
                  have hlen := congrArg List.length h
                  simp only [List.length_cons, List.length_nil] at hlen
                  omega
          | cons r2 rs2 =>
              cases rs' with
              | nil =>
                  rw [rightsTokens_cons_cons, rightsTokens_single] at h
                  have hlen := congrArg List.length h
                  simp only [List.length_cons, List.length_nil] at hlen
                  omega
              | cons r2' rs2' =>
                  rw [rightsTokens_cons_cons, rightsTokens_cons_cons] at h
                  have hr : r = r' := rightsToken_injective (List.cons.inj h).1
                  rw [← hr] at h ⊢
                  have htail : rightsTokens (r2 :: rs2) = rightsTokens (r2' :: rs2') :=
                    (List.cons.inj (List.cons.inj h).2).2
                  exact congrArg (fun l => r :: l) (ih (r2' :: rs2') htail)
theorem protect_production_unique {tokens : List Token} {a b : MemTree .protectSpace}
    (ha : a.production tokens) (hb : b.production tokens) : a = b := by
  cases a with
  | protectSpace space virt pages rights =>
      cases b with
      | protectSpace space' virt' pages' rights' =>
          simp only [MemTree.production] at ha hb
          rw [ha] at hb
          have h' :
              keyword "protect" :: openParen :: Token.word space.val :: comma :: .natural virt ::
                  comma :: .natural pages :: comma :: keyword "rights" :: openBrace ::
                  rightsTokens rights ++ [closeBrace, closeParen] =
              keyword "protect" :: openParen :: Token.word space'.val :: comma :: .natural virt' ::
                  comma :: .natural pages' :: comma :: keyword "rights" :: openBrace ::
                  rightsTokens rights' ++ [closeBrace, closeParen] := by
            simpa only [List.cons_append, List.nil_append] using hb
          have h1 := (List.cons.inj h').2
          have h2 := (List.cons.inj h1).2
          have hspace : space.val = space'.val := Token.word.inj (List.cons.inj h2).1
          have h3 := (List.cons.inj h2).2
          have h4 := (List.cons.inj h3).2
          have hvirt : virt = virt' := Token.natural.inj (List.cons.inj h4).1
          have h5 := (List.cons.inj h4).2
          have h6 := (List.cons.inj h5).2
          have hpages : pages = pages' := Token.natural.inj (List.cons.inj h6).1
          have h7 := (List.cons.inj h6).2
          have h8 := (List.cons.inj h7).2
          have h9 := (List.cons.inj h8).2
          have h10 := (List.cons.inj h9).2
          have hrt : rightsTokens rights = rightsTokens rights' :=
            List.append_cancel_right h10
          have hrights := rightsTokens_inj rights rights' hrt
          have hsp : space = space' := Subtype.ext hspace
          subst space'
          subst virt'
          subst pages'
          subst rights'
          rfl

theorem rightsPrint_value (right : Speicherdienst) : (rightsPrint right).value = rightsToken right := by
  cases right <;> rfl

theorem printComma_value : printComma.value = comma := rfl

theorem rightsPrints_value (rights : List Speicherdienst) :
    (rightsPrints rights).map PrintedToken.value = rightsTokens rights := by
  induction rights with
  | nil => rfl
  | cons r rs ih =>
      cases rs with
      | nil =>
          change [rightsPrint r].map PrintedToken.value = [rightsToken r]
          simp only [List.map_cons, List.map_nil, rightsPrint_value]
      | cons r2 rs2 =>
          change (rightsPrint r :: printComma :: rightsPrints (r2 :: rs2)).map PrintedToken.value =
            rightsToken r :: comma :: rightsTokens (r2 :: rs2)
          simp only [List.map_cons, rightsPrint_value, printComma_value, ih]
theorem printOpen_value : printOpen.value = openParen := rfl
theorem printClose_value : printClose.value = closeParen := rfl
theorem printOpenBrace_value : printOpenBrace.value = openBrace := rfl
theorem printCloseBrace_value : printCloseBrace.value = closeBrace := rfl

theorem protect_print_production (space : Identifier) (virt pages : Nat) (rights : List Speicherdienst) :
    (MemTree.protectSpace space virt pages rights).production
      ((MemTree.protectSpace space virt pages rights).printPieces.map PrintedToken.value) := by
  simp only [MemTree.production, MemTree.printPieces, rightsPrints_value,
    List.map_append, List.map_cons, List.map_nil, word, Identifier.print, PrintedToken.unquoted,
    printPunctuation, printInteger, keyword, openParen, closeParen, comma, openBrace, closeBrace,
    printOpen_value, printClose_value, printOpenBrace_value, printCloseBrace_value,
    printComma_value, rightsPrints_value, String.reduceToList]

def protectSyntax : Syntax (MemTree .protectSpace) where
  reads := fun tokens tree => tree.production tokens
  unique := by intro tokens a b ha hb; exact protect_production_unique ha hb
  printPieces := MemTree.printPieces
  reads_print := by intro tree; cases tree with | protectSpace s v p r => exact protect_print_production s v p r

theorem memParse_protect : MemParseAussage .protectSpace := by
  intro text tree
  change Text.Parse (tokenGrammar (fun tokens (t : MemTree .protectSpace) => t.production tokens)) text tree ↔
    ∃ pieces, Lexed text pieces ∧ tree.production (canonicalTokens pieces)
  exact (protectSyntax : Syntax (MemTree .protectSpace)).parse_iff

theorem memInversion_protect : MemInversionAussage .protectSpace := by
  intro tree tokens prod
  cases tree with
  | protectSpace space virt pages rights =>
      obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 (MemTree.printPieces (.protectSpace space virt pages rights))
      refine ⟨pieces, ?_, ?_⟩
      · simpa only [MemTree.print, Lexed] using lexed
      · have hp := protect_print_production space virt pages rights
        simp only [MemTree.production] at hp prod
        exact aligned.trans (hp.trans prod.symm)

theorem memEindeutig_protect : MemEindeutigAussage .protectSpace := by
  intro a b tokens ha hb
  exact protectSyntax.unique ha hb

theorem memDruck_protect : MemDruckAussage .protectSpace := by
  intro tree
  refine ⟨protectSyntax.reads_print tree, ?_⟩
  change Text.Parse (tokenGrammar (fun tokens (t : MemTree .protectSpace) => t.production tokens))
    (MemTree.print tree) tree
  simpa only [protectSyntax, Syntax.grammar, Syntax.print, MemTree.print] using protectSyntax.parse_print tree

end Gabbro.Core.Ast.LowLevel
