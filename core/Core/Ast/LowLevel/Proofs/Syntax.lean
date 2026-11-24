module

public import Core.Ast.LowLevel.Obligations

/-!
# Low-level lexical and grammatical proofs

Prove each statement for every `LowLevel.Form`. Use the shared lexical adapter
and canonical printer certificates. Invert `TypeReads` for the view's operand.

- `ParseAussage`
- `InversionAussage`
- `EindeutigAussage`
- `DruckAussage`
-/

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter

lemma productionUnique {form : Form} {tokens : List Token} {a b : Tree form}
    (ha : a.production tokens) (hb : b.production tokens) : a = b := by
  cases a with
  | addressType sa =>
      cases b with
      | addressType sb =>
          simp only [Tree.production] at ha hb
          rw [ha] at hb
          have hname := congrArg (fun l : List Token => l[2]?) hb
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hname
          have hnameList : sa.name.toList = sb.name.toList := by
            simpa only [keyword, Token.word.injEq] using hname
          have hnameEq : sa.name = sb.name := String.toList_injective hnameList
          cases sa <;> cases sb <;>
            simp only [AddressSpace.name, String.reduceEq] at hnameEq ⊢
  | regionAddress ra =>
      cases b with
      | regionAddress rb =>
          simp only [Tree.production] at ha hb
          rw [ha] at hb
          simp at hb
          exact congrArg Tree.regionAddress (Subtype.ext hb)
  | view ra ta =>
      cases b with
      | view rb tb =>
          simp only [Tree.production] at ha hb
          rcases ha with ⟨inputa, rfl, readsA⟩
          rcases hb with ⟨inputb, eqB, readsB⟩
          simp at eqB
          rcases eqB with ⟨hval, hinput⟩
          have hra : ra = rb := Subtype.ext hval
          have htype : ta = tb := (TypeReads.deterministic readsA (hinput.symm ▸ readsB)).1
          exact congrArg₂ Tree.view hra htype
  | environment na abi row =>
      cases b with
      | environment nb abi' row' =>
          simp only [Tree.production] at ha hb
          rw [ha] at hb
          have hname := congrArg (fun l : List Token => l[1]?) hb
          have habi := congrArg (fun l : List Token => l[3]?) hb
          have hrow := congrArg (fun l : List Token => l[6]?) hb
          simp only [environmentTokens, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hname habi hrow
          have hna : na.val = nb.val := by simpa using hname
          have habiName : abi.name.toList = abi'.name.toList := by
            simpa only [keyword, Token.word.injEq] using habi
          have hrowName : row.name.toList = row'.name.toList := by
            simpa only [keyword, Token.word.injEq] using hrow
          have habiEq := DienstAbi.name_injective (String.toList_injective habiName)
          have hrowEq := FirmwareZeile.name_injective (String.toList_injective hrowName)
          have hnaEq : na = nb := Subtype.ext hna
          subst nb
          cases habiEq
          cases hrowEq
          rfl

lemma addressTypePrints (space : AddressSpace) :
    (Tree.addressType space).production
      ((Tree.addressType space).printPieces.map PrintedToken.value) := by
  cases space <;>
    simpa [Tree.production, Tree.printPieces, keyword, word, Identifier.print,
      PrintedToken.unquoted, Compare.print, Compare.spelling, printPunctuation,
      AddressSpace.print, AddressSpace.name, String.reduceToList]

lemma regionAddressPrints (region : Identifier) :
    (Tree.regionAddress region).production
      ((Tree.regionAddress region).printPieces.map PrintedToken.value) := by
  simpa [Tree.production, Tree.printPieces, keyword, word, Identifier.print,
    PrintedToken.unquoted, printPunctuation, printDot, printOpen, printClose,
    dot, openParen, closeParen, String.reduceToList]

lemma environmentPrints (name : Identifier) (abi : DienstAbi) (row : FirmwareZeile) :
    (Tree.environment name abi row).production
      ((Tree.environment name abi row).printPieces.map PrintedToken.value) :=
  environment_printTokens name abi row

lemma parseOfPrint {form : Form} (tree : Tree form)
    (prints : tree.production (tree.printPieces.map PrintedToken.value)) :
    Parse tree.print tree := by
  obtain ⟨pieces, lexical, align⟩ := PrintedToken.renderLexed 0 (tree.printPieces)
  refine ⟨True.intro, pieces, lexical, ?_⟩
  have symbols : ∀ ts : List LocatedToken,
      DerivesSymbols (tokenGrammar (fun tokens (tree : Tree form) => tree.production tokens))
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

theorem parseAussage (form : Form) : ParseAussage form := by
  intro tree text pieces lex prod
  refine ⟨True.intro, pieces, lex, ?_⟩
  have symbols : ∀ ts : List LocatedToken,
      DerivesSymbols (tokenGrammar (fun tokens (tree : Tree form) => tree.production tokens))
        (ts.map Symbol.terminal) ts := by
    intro ts
    induction ts with
    | nil => exact .nil
    | cons t ts ih => exact .terminal ih
  exact .production ⟨semanticTokens pieces, rfl, by
    have hp : tree.production (canonicalTokens pieces) := prod
    simpa [canonicalTokens] using hp⟩ (symbols (semanticTokens pieces))

theorem inversionAussage (form : Form) : InversionAussage form := by
  intro tree text parsed
  rcases parsed with ⟨root, pieces, lex, derives⟩
  refine ⟨pieces, lex, ?_⟩
  cases derives with
  | production production children =>
      obtain ⟨expected, rfl, reads⟩ := production
      simpa [canonicalTokens, children.terminalTokens] using reads

theorem eindeutigAussage (form : Form) : EindeutigAussage form := by
  intro a b text pa pb
  rcases pa with ⟨root, pieces, lex, derivesA⟩
  rcases pb with ⟨root', pieces', lex', derivesB⟩
  have same : pieces = pieces' := LexedAt.deterministic lex lex'
  subst pieces'
  have readsA : a.production (canonicalTokens pieces) := by
    cases derivesA with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa [canonicalTokens, children.terminalTokens] using reads
  have readsB : b.production (canonicalTokens pieces) := by
    cases derivesB with
    | production production children =>
        obtain ⟨expected, rfl, reads⟩ := production
        simpa [canonicalTokens, children.terminalTokens] using reads
  exact productionUnique readsA readsB

theorem druckAussage_addressType : DruckAussage .addressType := by
  intro tree printable
  cases tree with
  | addressType space =>
      exact ⟨addressTypePrints space, parseOfPrint _ (addressTypePrints space)⟩

theorem druckAussage_regionAddress : DruckAussage .regionAddress := by
  intro tree
  cases tree with
  | regionAddress region =>
      exact ⟨regionAddressPrints region, parseOfPrint _ (regionAddressPrints region)⟩

theorem druckAussage_environment : DruckAussage .environment := by
  intro tree
  cases tree with
  | environment name abi row =>
      exact ⟨environmentPrints name abi row, parseOfPrint _ (environmentPrints name abi row)⟩

end Gabbro.Core.Ast.LowLevel
