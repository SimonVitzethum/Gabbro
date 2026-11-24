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

theorem recordDecl_inversion : RecordDeclInversionAussage := by
  intro scope input tree rest exported name read
  cases read with
  | constant => contradiction
  | function => contradiction
  | record e n valid distinct memberRead =>
      refine ⟨⟨e, n, _, valid, distinct⟩, ?_, ?_, memberRead, ?_⟩
      · simp_all [recordDeclarationPrefix]
      · apply Subtype.ext
        simp_all [recordDeclarationPrefix]
      · rfl
  | tagged => contradiction

theorem recordDecl_suffix : RecordDeclSuffixAussage := by
  intro input fields rest read
  induction fields generalizing input rest with
  | nil =>
      cases read
      exact List.suffix_cons _ _
  | cons m ms ih =>
      cases read with
      | next n typeRead memberRead =>
          obtain ⟨t, ht⟩ := TypeReads.consumes typeRead
          have moreSuffix : _ := ⟨t ++ [comma], by rw [ht]; simp⟩
          have headSuffix : _ := ⟨[.word n.val, colon], rfl⟩
          exact ((ih memberRead).trans moreSuffix).trans headSuffix

private theorem recordMembers_print_reads (fields : List RecordMember) :
    RecordMembersRead
      ((fields.flatMap RecordMember.printPieces).map PrintedToken.value ++ [closeBrace, semicolon])
      fields [semicolon] := by
  induction fields with
  | nil =>
      simp [RecordMember.printPieces]
      exact .close
  | cons m ms ih =>
      change RecordMembersRead
        (.word m.name.val :: colon :: m.written.printPieces.map PrintedToken.value ++
          comma :: ((ms.flatMap RecordMember.printPieces).map PrintedToken.value ++ [closeBrace, semicolon]))
        (⟨m.name, m.written⟩ :: ms) [semicolon]
      apply RecordMembersRead.next
      · exact WrittenType.printReads m.written m.written.valid
          (by intro more same; cases same)
      · exact ih

private theorem recordDecl_print (scope : Scope) (args : RecordDeclArgs) :
    (recordDecl scope).production args
      (((Category.declaration scope).printPieces ((recordDecl scope).tree args)).map PrintedToken.value) := by
  refine ⟨(args.members.flatMap RecordMember.printPieces).map PrintedToken.value ++
    [closeBrace, semicolon], ?_, ?_⟩
  · rfl
  · exact recordMembers_print_reads args.members

theorem recordDecl_derivation : RecordDeclDerivationAussage := by
  intro scope
  refine ⟨
    (fun args tokens prod => by
      rcases prod with ⟨input, rfl, memberRead⟩
      exact DeclReads.record args.exported args.name args.valid args.distinct memberRead),
    recordDecl_print scope,
    ?_⟩
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let args : RecordDeclArgs := ⟨false, name, [], (fun m h => (List.not_mem_nil m).elim), by simp⟩
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
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let args : RecordDeclArgs := ⟨false, name, [], (fun m h => (List.not_mem_nil m).elim), by simp⟩
  let form := recordDeclForm []
  let E := form.einheit platform args
  let s := (I.start E start).2
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s .start
    (form.realisiert (rd_amOrt []) platform args s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

theorem recordDecl_binding : RecordDeclBindingAussage := by
  intro scope args frame
  simp [Befehl.auswerten, recordBinding]

end Gabbro.Core.Ast.Semantik
