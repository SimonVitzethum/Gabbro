module

public import Core.Ast.Aggregate.Records.Declarations
public import Core.Ast.Semantik.Formbeweise

/-!
# RecordDecl

- `Surface.RecordDeclInversionAussage`
- `Surface.RecordDeclSuffixAussage`
- `Surface.RecordDeclDerivationAussage`
- `RecordDeclParseAussage`
- `RecordDeclElaboriertAussage`
- `RecordDeclRealisiertAussage`
- `RecordDeclAnnahmeAussage`
- `RecordDeclIdealAussage`
- `RecordDeclEinheitAussage`
- `RecordDeclImplAussage`
- `RecordDeclErhaltungAussage`
- `RecordDeclRegelSicherAussage`
- `RecordDeclErfuellbarAmAussage`
- `RecordDeclBindingAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text

private theorem identPrintVal (i : Identifier) : i.print.value = Token.word i.val := by rfl
private theorem ppwVal (h : Char) (t : List Char) (p1 p2) :
    (printProgramWord h t p1 p2).value = Token.word (h :: t) := by rfl
private theorem ppValue (s : String) (p1 p2) :
    (printPunctuation s p1 p2).value = Token.punctuation s.toList := by rfl
private theorem printColonVal : printColon.value = colon := by rfl
private theorem printCommaVal : printComma.value = comma := by rfl
private theorem printAssignmentVal : printAssignment.value = assignment := by rfl
private theorem printOpenBraceVal : printOpenBrace.value = openBrace := by rfl
private theorem printCloseBraceVal : printCloseBrace.value = closeBrace := by rfl
private theorem printSemicolonVal : printSemicolon.value = semicolon := by rfl

theorem recordDecl_inversion : RecordDeclInversionAussage := by
  intro scope input tree rest ex name read
  generalize hh : recordDeclarationPrefix ex ++ [Token.word name.val, assignment, openBrace] ++ input = hs at read
  cases read with
  | record e n valid distinct memberRead =>
      rename_i fields input'
      have he : e = ex := by
        cases e <;> cases ex <;> simp_all [recordDeclarationPrefix, keyword]
      subst e
      have hh' : recordDeclarationPrefix ex ++ ([Token.word name.val, assignment, openBrace] ++ input) =
          recordDeclarationPrefix ex ++ ([Token.word n.val, assignment, openBrace] ++ input') := by
        simpa only [List.append_assoc] using hh
      have htail := List.append_cancel_left hh'
      have hnval0 : Token.word name.val = Token.word n.val := (List.cons.inj htail).1
      have hnval : n.val = name.val := by
        injection hnval0 with h
        exact h.symm
      have hin := (List.cons.inj (List.cons.inj (List.cons.inj htail).2).2).2
      refine ⟨⟨ex, n, _, valid, distinct⟩, rfl, Subtype.ext hnval, ?_, ?_⟩
      · cases hin
        exact memberRead
      · rfl
  | tagged ex' n valid distinct firstRead tailRead =>
      cases ex <;> cases ex' <;> simp_all [recordDeclarationPrefix, taggedDeclarationPrefix, keyword]
  | _ =>
      cases ex <;> simp_all [recordDeclarationPrefix, keyword, assignment, colon, openBrace,
        openParen, semicolon]

private theorem recordMembers_consumes {input : List Token} {fields : List RecordMember} {rest : List Token}
    (read : RecordMembersRead input fields rest) : rest <:+ input := by
  induction read with
  | close => exact List.suffix_cons _ _
  | next n typeRead memberRead ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨v, hv⟩ := TypeReads.consumes typeRead
      refine ⟨[.word n.val, colon] ++ v ++ [comma] ++ u, ?_⟩
      simpa [hv, hu, List.append_assoc]

theorem recordDecl_suffix : RecordDeclSuffixAussage := by
  intro input fields rest read
  exact (List.suffix_cons semicolon rest).trans (recordMembers_consumes read)

private def memberTokenList : List RecordMember → List Token
  | [] => []
  | m :: ms => m.name.print.value :: colon :: m.written.printPieces.map PrintedToken.value ++
      comma :: memberTokenList ms

private theorem recordMembers_print_reads (fields : List RecordMember)
    (valid : ∀ m ∈ fields, m.written.valid) :
    RecordMembersRead (memberTokenList fields ++ [closeBrace, semicolon]) fields [semicolon] := by
  induction fields with
  | nil =>
      simp_all [memberTokenList]
      exact .close
  | cons m ms ih =>
      simpa [memberTokenList, identPrintVal] using
        (RecordMembersRead.next m.name
          (WrittenType.printReads m.written (valid m (by simp_all)) (by intro more same; cases same))
          (ih (fun x hx => valid x (List.mem_cons_of_mem m hx))))

private theorem recordDecl_print (scope : Scope) (args : RecordDeclArgs) :
    (recordDecl scope).production args
      (((Category.declaration scope).printPieces ((recordDecl scope).tree args)).map PrintedToken.value) := by
  refine ⟨memberTokenList args.members ++ [closeBrace, semicolon], ?_, ?_⟩
  · have hmem : args.members.flatMap (fun m => (RecordMember.printPieces m).map PrintedToken.value) =
        memberTokenList args.members := by
      induction args.members with
      | nil => rfl
      | cons m ms ih => simpa [memberTokenList, RecordMember.printPieces,
          printColonVal, printCommaVal] using ih
    have hmem' : (args.members.map (fun x => (RecordMember.printPieces x).map PrintedToken.value)).flatten =
        memberTokenList args.members := by
      simpa [List.flatMap, Function.comp_def] using hmem
    by_cases h : args.exported <;>
      simp_all [h, hmem', List.flatMap, Function.comp_def, recordDecl, Category.printPieces, Decl.printPieces,
        recordDeclarationHead, recordDeclarationPrefix, keyword, printPub, printTypeDecl,
        identPrintVal, ppwVal, ppValue, printColonVal, printCommaVal, printAssignmentVal,
        printOpenBraceVal, printCloseBraceVal, printSemicolonVal,
        List.map_cons, List.map_append, List.map_nil]
  · exact recordMembers_print_reads args.members args.valid

theorem recordDecl_derivation : RecordDeclDerivationAussage := by
  intro scope
  refine ⟨
    (fun args tokens prod => by
      rcases prod with ⟨input, rfl, memberRead⟩
      exact DeclReads.record args.exported args.name args.valid args.distinct memberRead),
    recordDecl_print scope,
    ?_⟩
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let args : RecordDeclArgs :=
    ⟨false, name, [], (fun m h => (List.not_mem_nil h).elim), by decide⟩
  exact Rule.satisfiableOfPrint args (recordDecl_print scope args)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem rd_amOrt (scope : Scope) : (recordDeclForm scope).RegelAmOrt := by
  intro args
  rfl

theorem recordDecl_parse : RecordDeclParseAussage := by
  intro scope args text pieces lexed prod
  exact (Surface.recordDecl_derivation scope).parse lexed prod

theorem recordDecl_elaboriert : RecordDeclElaboriertAussage := by
  intro scope platform args
  rfl

theorem recordDecl_realisiert : RecordDeclRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (recordDeclForm scope).realisiert (rd_amOrt scope) platform args s running active live atPc

theorem recordDecl_annahme : RecordDeclAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (recordDeclForm scope)

theorem recordDecl_ideal : RecordDeclIdealAussage := by
  intro scope
  refine ⟨rd_amOrt scope, ?_⟩
  intro args
  exact ⟨((recordDeclForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem recordDecl_einheit : RecordDeclEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((recordDeclForm scope).befehl args).kommutation⟩

theorem recordDecl_impl : RecordDeclImplAussage := by
  intro scope args c s w plans u
  rfl

theorem recordDecl_erhaltung : RecordDeclErhaltungAussage := by
  intro scope platform args
  let p := (recordDeclForm scope).fragment args
  let b := (recordDeclForm scope).befehl args
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicher p platform (by rfl)⟩

theorem recordDecl_regelSicher : RecordDeclRegelSicherAussage := by
  intro scope platform args
  exact (recordDecl_erhaltung scope platform args).2.2.2

theorem recordDecl_erfuellbar : RecordDeclErfuellbarAmAussage := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let args : Surface.RecordDeclArgs :=
    ⟨false, name, [], (fun m h => (List.not_mem_nil h).elim), by decide⟩
  let form := recordDeclForm []
  let E := form.einheit platform args
  let s := (I.start E start).2
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s .start
    (form.realisiert (rd_amOrt []) platform args s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

theorem recordDecl_binding : RecordDeclBindingAussage := by
  intro scope args frame
  simp_all [recordDeclForm, Befehl.auswerten, recordBinding]

end Gabbro.Core.Ast.Semantik
