module

public import Core.Ast.Variant.Obligations
import Core.Ast.Declaration.Members

/-!
# TaggedDecl

- `Surface.TaggedDeclInversionAussage`
- `Surface.TaggedDeclSuffixAussage`
- `Surface.TaggedDeclDerivationAussage`
- `TaggedDeclParseAussage`
- `TaggedDeclElaboriertAussage`
- `TaggedDeclRealisiertAussage`
- `TaggedDeclAnnahmeAussage`
- `TaggedDeclIdealAussage`
- `TaggedDeclEinheitAussage`
- `TaggedDeclImplAussage`
- `TaggedDeclErhaltungAussage`
- `TaggedDeclRegelSicherAussage`
- `TaggedDeclErfuellbarAmAussage`
- `TaggedDeclBindingAussage`
-/


@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem td_amOrt (scope : Scope) : (taggedDeclForm scope).RegelAmOrt := by
  intro a
  rfl

theorem taggedDecl_annahme : TaggedDeclAnnahmeAussage := by
  intro scope platform args
  let form := taggedDeclForm scope
  refine ⟨(form.befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, form.befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := (form.befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

theorem taggedDecl_erhaltung : TaggedDeclErhaltungAussage := by
  intro scope platform args
  let p := (taggedDeclForm scope).fragment args
  let b := (taggedDeclForm scope).befehl args
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicher p platform (by rfl)⟩

theorem taggedDecl_regelSicher : TaggedDeclRegelSicherAussage := by
  intro scope platform args
  exact (taggedDecl_erhaltung scope platform args).2.2.2

theorem taggedDecl_elaboriert : TaggedDeclElaboriertAussage := by
  intro scope platform args
  rfl

theorem taggedDecl_realisiert : TaggedDeclRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (taggedDeclForm scope).realisiert (td_amOrt scope) platform args s running active live atPc

theorem taggedDecl_ideal : TaggedDeclIdealAussage := by
  intro scope
  constructor
  · exact td_amOrt scope
  · intro args
    constructor
    · exact ((taggedDeclForm scope).befehl args).bestimmt
    · intro c s w plans u
      rfl

theorem taggedDecl_einheit : TaggedDeclEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((taggedDeclForm scope).befehl args).kommutation⟩

theorem taggedDecl_impl : TaggedDeclImplAussage := by
  intro scope args c s w plans u
  rfl

theorem taggedDecl_binding : Gabbro.Core.Ast.Semantik.TaggedDeclBindingAussage := by
  intro scope a frame
  exact ⟨rfl, rfl, rfl, rfl⟩

open Gabbro.Core.Text
open Surface

private theorem programWordValue (head : Char) (tail : List Char) (h1 h2) :
    (printProgramWord head tail h1 h2).value = .word (head :: tail) := rfl

theorem taggedDecl_inversion : TaggedDeclInversionAussage := by
  intro scope input tree rest exported name read
  generalize tokens : taggedDeclarationPrefix exported ++ [.word name.val, assignment, openBrace] ++ input = ts at read
  cases read with
  | tagged actual n valid distinct head tail =>
    have sameExport : actual = exported := by
      cases actual <;> cases exported <;> simp_all [taggedDeclarationPrefix, keyword]
    subst actual
    have same := List.append_cancel_left (by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using tokens :
      taggedDeclarationPrefix exported ++ (_ :: _ :: _ :: input) =
        taggedDeclarationPrefix exported ++ (.word n.val :: _ :: _ :: _))
    have sameName := Token.word.inj (List.cons.inj same).1
    have sameInput := (List.cons.inj (List.cons.inj (List.cons.inj same).2).2).2
    subst input
    exact ⟨⟨exported, n, _, _, valid, distinct⟩, _, rfl, Subtype.ext sameName.symm, head, tail, rfl⟩
  | record other n valid distinct members =>
    cases other <;> cases exported <;> simp_all [taggedDeclarationPrefix, recordDeclarationPrefix, keyword]
  | table item _ =>
    cases visibility : item.exported <;> cases exported <;>
      simp_all [taggedDeclarationPrefix, TableDeclaration.header, printPub, printTable, programWordValue, keyword]
  | effectGroup item _ =>
    cases visibility : item.exported <;> cases exported <;>
      simp_all [taggedDeclarationPrefix, EffectGroupDeclaration.header, printPub, printEffects, programWordValue, keyword]
  | _ => cases exported <;> simp_all [taggedDeclarationPrefix, keyword, assignment, colon, openBrace, openParen, semicolon]

private theorem taggedDeclPrints (scope : Scope) (args : TaggedDeclArgs scope) :
    (taggedDecl scope).production args
      (((Category.declaration scope).printPieces ((taggedDecl scope).tree args)).map PrintedToken.value) := by
  obtain ⟨more, head, tail⟩ := variantMembers_printReads args.first args.tail (rest := [semicolon]) args.valid
  refine ⟨_, more, ?_, head, tail⟩
  have prefixTokens : (taggedDeclarationHead args.exported).map PrintedToken.value =
      taggedDeclarationPrefix args.exported := by cases args.exported <;> rfl
  simp only [Category.printPieces, taggedDecl, Decl.printPieces, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.cons_append, List.nil_append, prefixTokens]
  rfl

theorem taggedDecl_derivation : TaggedDeclDerivationAussage := by
  intro scope
  refine ⟨?_, taggedDeclPrints scope, ?_⟩
  · rintro args tokens ⟨input, more, rfl, head, tail⟩
    exact .tagged args.exported args.name args.valid args.distinct head tail
  · let name := keywordName 'v' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
    let label := keywordName 'a' [] (by decide) (fun _ h => (List.not_mem_nil h).elim)
    let member : VariantMember := ⟨label, none⟩
    have valid (m : VariantMember) (h : m ∈ [member]) : m.valid scope := by
      cases List.mem_singleton.mp h
      have notDiscard : member.label.val ≠ ['_'] := by
        intro equal
        cases equal
      exact ⟨(directName_of_singleton (name := label) rfl).1, notDiscard, fun _ h => (List.not_mem_nil h).elim⟩
    let args : TaggedDeclArgs scope := ⟨false, name, member, [], valid, List.nodup_singleton _⟩
    exact Rule.satisfiableOfPrint args (taggedDeclPrints scope args)

theorem taggedDecl_suffix : Gabbro.Core.Ast.Surface.TaggedDeclSuffixAussage := by
  intro scope input variants rest read
  exact (List.suffix_cons Gabbro.Core.Ast.semicolon rest).trans read.consumes

theorem taggedDecl_parse : Gabbro.Core.Ast.Semantik.TaggedDeclParseAussage := by
  intro scope args text pieces lexed production
  apply (Gabbro.Core.Ast.Category.declaration scope).syntax.parse_iff.mpr
  refine ⟨pieces, lexed, ?_⟩
  rcases production with ⟨input, more, same, firstRead, tailRead⟩
  rw [same]
  exact .tagged args.exported args.name args.valid args.distinct firstRead tailRead

theorem taggedDecl_erfuellbarAm : Gabbro.Core.Ast.Semantik.TaggedDeclErfuellbarAmAussage := by
  intro platform start
  let name : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'v' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let lbl : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'a' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  let member : Gabbro.Core.Ast.VariantMember := ⟨lbl, none⟩
  have valid : ∀ m ∈ member :: [], m.valid [] := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst m
    refine ⟨(directName_of_singleton (name := lbl) rfl).1, (by intro same; cases same), ?_⟩
    intro type memberType
    cases memberType
  have distinct : ((Gabbro.Core.Ast.variantLabels [member]).map (fun x => x.val)).Nodup := by
    change [lbl.val].Nodup
    exact List.nodup_singleton _
  let a : Gabbro.Core.Ast.Surface.TaggedDeclArgs [] := ⟨false, name, member, [], valid, distinct⟩
  refine ⟨a, ?_⟩
  let form := taggedDeclForm []
  let s := (I.start (form.einheit platform a) start).2
  dsimp [Quellform.ErfuellbarAm]
  refine ⟨Ast.print (category := .declaration []) (form.produktion.tree a), s,
    Ast.parse_print _, rfl, .start, ?_, ?_⟩
  · exact form.realisiert (td_amOrt []) platform a s rfl rfl rfl rfl
  · intro g guard; cases guard

end Gabbro.Core.Ast.Semantik
