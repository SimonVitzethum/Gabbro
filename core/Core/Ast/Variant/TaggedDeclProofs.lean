module

public import Core.Ast.Variant.Obligations

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
  simp [Befehl.auswerten, taggedDeclForm]

private theorem td_member_suffix {input member rest}
    (read : Gabbro.Core.Ast.VariantMemberRead input member rest) : rest <:+ input := by
  cases read with
  | nullary name closed => exact List.suffix_cons _ _
  | payload name typeRead =>
      exact (List.suffix_cons Gabbro.Core.Ast.closeParen rest).trans
        ((TypeReads.consumes typeRead).trans
          ((List.suffix_cons Gabbro.Core.Ast.openParen _).trans (List.suffix_cons _ _)))

private theorem td_tail_suffix {input variants rest}
    (read : Gabbro.Core.Ast.VariantMembersTailRead input variants rest) : rest <:+ input := by
  induction read with
  | done => exact List.suffix_cons _ _
  | next memberRead tailRead ih =>
      exact ih.trans ((td_member_suffix memberRead).trans (List.suffix_cons _ _))

theorem taggedDecl_suffix : Gabbro.Core.Ast.Surface.TaggedDeclSuffixAussage := by
  intro input variants rest read
  exact (List.suffix_cons Gabbro.Core.Ast.semicolon rest).trans (td_tail_suffix read)

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
    Gabbro.Core.Ast.keywordName 'v' [] (by omega) (by simp)
  let lbl : Gabbro.Core.Ast.Identifier :=
    Gabbro.Core.Ast.keywordName 'a' [] (by omega) (by simp)
  let member : Gabbro.Core.Ast.VariantMember := ⟨lbl, none⟩
  have valid : ∀ m ∈ member :: [], m.valid := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst m
    simp [Gabbro.Core.Ast.VariantMember.valid, Gabbro.Core.Ast.ordinaryLocal, lbl]
  have distinct : ((Gabbro.Core.Ast.variantLabels [member]).map Subtype.val).Nodup := by simp
  let a : Gabbro.Core.Ast.Surface.TaggedDeclArgs := ⟨false, name, member, [], valid, distinct⟩
  refine ⟨a, ?_⟩
  let form := taggedDeclForm []
  let s := (I.start (form.einheit platform a) start).2
  exact form.erfuellbar_aus_erreichbar platform start a s .start
    (form.realisiert (td_amOrt []) platform a s rfl rfl rfl rfl) (by intro g guard; cases guard)

end Gabbro.Core.Ast.Semantik
