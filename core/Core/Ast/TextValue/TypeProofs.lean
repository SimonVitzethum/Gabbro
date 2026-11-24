module

public import Core.Ast.TextValue.Type
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.Semantik.Pflichten

/-!
# TextType

Prove the pinned statements in this file.

- `TextTypeInversionAussage`
- `TextTypeDerivationAussage`
- `TextTypeWidenAussage`
- `TextTypeParseAussage`
- `TextTypeElaboriertAussage`
- `TextTypeRealisiertAussage`
- `TextTypeAnnahmeAussage`
- `TextTypeIdealAussage`
- `TextTypeEinheitAussage`
- `TextTypeImplAussage`
- `TextTypeErhaltungAussage`
- `TextTypeKernOrtAussage`
- `TextTypeRegelSicherAussage`
- `TextTypeRegelAntwortSicherAussage`
- `TextTypeKostenUndSpurAussage`
- `TextTypeErfuellbarAmAussage`
-/

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter
open Gabbro.Core.Text

private theorem textTypeAtRoot (ctx : Scope × Option (Ty .value)) :
    (typeUseForm ctx textTypeUse).RegelAmOrt := by
  intro args
  change (((expr 0 args.val.value).code ++
      [Befehl.bindeWert 0 args.val.written.type false])[(expr 0 args.val.value).code.length]? =
    some (.bindeWert 0 args.val.written.type false))
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

private theorem textTypeOhneInvarianten (ctx : Scope × Option (Ty .value))
    (args : {a : Surface.MutableLocalArgs ctx.1 ctx.2 // textTypeUse a.written}) :
    ((typeUseForm ctx textTypeUse).fragment args).klauseln.invariant = [] := by
  exact stmt_keine_invarianten (((Surface.mutableLocal ctx.1 ctx.2).tree args.val).2)

private theorem stringToken_ne_bool : keyword "string" ≠ keyword "bool" := by intro same; cases same

private theorem stringToken_ne_intWord (signed : Bool) (width : Nat) :
    keyword "string" ≠ .word (intSpelling signed width) := by
  intro h
  cases signed
  · have hl : "string".toList = intSpelling false width := by
      injection h with hl
    exact (show ('s' : Char) ≠ 'u' from by intro same; cases same) (List.cons.inj hl).1
  · have hl : "string".toList = intSpelling true width := by
      injection h with hl
    exact (show ('s' : Char) ≠ 'i' from by intro same; cases same) (List.cons.inj hl).1

theorem TextTypeInversion : TextTypeInversionAussage := by
  intro scope input type rest read
  generalize htok : keyword "string" :: input = toks at read
  cases read with
  | text =>
      exact ⟨_, (List.cons.inj htok).2, rfl⟩
  | bool =>
      exact (stringToken_ne_bool (List.cons.inj htok).1).elim
  | integer valid closed =>
      rename_i width more
      exact (stringToken_ne_intWord width more (List.cons.inj htok).1).elim
  | interval valid ls rs =>
      rename_i signed width input' lo hi more
      exact (stringToken_ne_intWord signed width (List.cons.inj htok).1).elim
  | array count bound elemRead boundRead =>
      rename_i element boundInput
      have h : keyword "string" = openBracket := (List.cons.inj htok).1
      cases h
  | tuple firstRead secondRead tailRead =>
      rename_i first second more tail more'
      have h : keyword "string" = openParen := (List.cons.inj htok).1
      cases h
  | index _ _ | indexOption _ _ =>
      cases (List.cons.inj htok).1

theorem TextTypeDerivation : TextTypeDerivationAussage := by
  intro scope capacity rest
  change TypeReads scope (keyword "string" :: keyword "max" :: .natural capacity :: rest) (.text capacity) rest
  exact .text

theorem TextTypeWiden : TextTypeWidenAussage := by
  intro source target value fits
  have hb : value.bytes.size ≤ target := Nat.le_trans value.bound fits
  refine ⟨TextValue.widen value fits, ?_, rfl⟩
  simp only [wertIn, wertAls]
  rw [dif_pos hb]
  rfl

theorem TextTypeParse : TextTypeParseAussage := by
  intro ctx args text pieces lex prod
  apply (Category.statement ctx.1 ctx.2).syntax.parse_iff.mpr
  refine ⟨pieces, lex, ?_⟩
  exact prod

theorem TextTypeElaboriert : TextTypeElaboriertAussage := by
  intro ctx platform args
  rfl

theorem TextTypeRealisiert : TextTypeRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (typeUseForm ctx textTypeUse).realisiert (textTypeAtRoot ctx) platform args s running active live atPc

theorem TextTypeAnnahme : TextTypeAnnahmeAussage := by
  intro ctx
  exact Quellform.annahme (typeUseForm ctx textTypeUse)

theorem TextTypeIdeal : TextTypeIdealAussage := by
  intro ctx
  refine ⟨textTypeAtRoot ctx, ?_⟩
  intro args
  exact ⟨((typeUseForm ctx textTypeUse).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem TextTypeEinheit : TextTypeEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((typeUseForm ctx textTypeUse).befehl args).kommutation⟩

theorem TextTypeImpl : TextTypeImplAussage := by
  intro ctx args c s w plans u
  rfl

theorem TextTypeErhaltung : TextTypeErhaltungAussage := by
  intro ctx
  exact Quellform.erhaltung (typeUseForm ctx textTypeUse)
    (fun args => textTypeOhneInvarianten ctx args)

theorem TextTypeKernOrt : TextTypeKernOrtAussage := by
  intro ctx
  exact textTypeAtRoot ctx

theorem TextTypeRegelSicher : TextTypeRegelSicherAussage := by
  intro ctx platform args
  exact (Quellform.erhaltung (typeUseForm ctx textTypeUse)
    (fun a => textTypeOhneInvarianten ctx a) platform args).2.2.2

theorem TextTypeRegelAntwortSicher : TextTypeRegelAntwortSicherAussage := by
  intro ctx platform args
  change RegelAntwortSicher ((typeUseForm ctx textTypeUse).fragment args) platform
    ((typeUseForm ctx textTypeUse).befehl args)
  let form := typeUseForm ctx textTypeUse
  let b := form.befehl args
  intro t c s choice stepPlan u spur next head impl execute
  have hp : stepPlan = plan := (List.cons.inj impl.1).1
  subst stepPlan
  obtain ⟨hspur, _⟩ := b.vollzug_genau (w := choice) impl execute
  subst spur
  constructor
  · intro answer
    change Aktion.intern ≠ Aktion.verbrauche answer
    intro h
    cases h
  · intro answer
    exact List.not_mem_nil

theorem TextTypeKostenUndSpur : TextTypeKostenUndSpurAussage := by
  intro ctx platform args
  change TextInstructionCost ((typeUseForm ctx textTypeUse).fragment args) platform
    ((typeUseForm ctx textTypeUse).befehl args)
  let form := typeUseForm ctx textTypeUse
  let b := form.befehl args
  intro t c s choice stepPlan u spur next head impl execute
  obtain ⟨hspur, _⟩ := b.vollzug_genau (w := choice) impl execute
  subst spur
  refine ⟨rfl, rfl, ?_⟩
  change ((form.fragment args).einheit platform).stotterLaenge b + [stepPlan].length = 1
  simp only [Fragment.einheit, List.length_cons, List.length_nil, Nat.zero_add]

theorem TextTypeErfuellbarAm : TextTypeErfuellbarAmAussage := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], ⟨'x', [], rfl,
      Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      by intro a m; cases m⟩⟩
  have ordinary : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
  let capacity := (sourceUtf8 []).size
  let written : WrittenType := .text capacity
  let value : Expr [] (.text capacity) := .textLiteral []
  let argsVal : Surface.MutableLocalArgs [] none :=
    ⟨name, ordinary, written, by simp only [written, WrittenType.valid], .text capacity, value,
      by
        simp only [written, Fits, WrittenType.type]
        exact Nat.le_refl _⟩
  let args : {a : Surface.MutableLocalArgs [] none // textTypeUse a.written} :=
    ⟨argsVal, by simp only [argsVal, written, textTypeUse]⟩
  let form := typeUseForm ([], none) textTypeUse
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.textLiteral 0 []).nach eintritt s₀
  have initializer : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.textLiteral 0 [], rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start initializer
  refine ⟨args, ?_⟩
  dsimp [Quellform.TextErfuellbar]
  refine ⟨Ast.print (form.produktion.tree args), s₁, Ast.parse_print _, ?_, reached, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact form.realisiert (textTypeAtRoot ([], none)) platform args s₁ rfl rfl rfl rfl
  · intro g guard
    cases guard
  · rfl
  · rfl

end Gabbro.Core.Ast.Semantik
