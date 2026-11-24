module

public import Core.Ast.Aggregate.Carrier.Effects.Group
public import Core.Ast.Semantik.Formbeweise
import Init.Omega

/-!
# Effect group

Prove the pinned statements in this file.

- `EffectGroupInversionAussage`
- `EffectGroupDerivationAussage`
- `EffectGroupScopeAussage`
- `EffectGroupExpansionAussage`
- `EffectGroupVisibilityAussage`
- `EffectGroupCaptureAussage`
- `EffectGroupSignatureAussage`
- `EffectGroupInferredAussage`
- `EffectGroupCallAussage`
- `EffectGroupBindingAussage`
- `EffectGroupParseAussage`
- `EffectGroupElaboriertAussage`
- `EffectGroupRealisiertAussage`
- `EffectGroupAnnahmeAussage`
- `EffectGroupIdealAussage`
- `EffectGroupEinheitAussage`
- `EffectGroupImplAussage`
- `EffectGroupErhaltungAussage`
- `EffectGroupRegelSicherAussage`
- `EffectGroupErfuellbarAmAussage`
- `EffectGroupUseErfuellbarAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter
open Gabbro.Core.Text
open Gabbro.Core.Ast

private theorem identPrintVal (i : Identifier) : i.print.value = Token.word i.val := by rfl
private theorem ppwVal (h : Char) (t : List Char) (p1 p2) :
    (printProgramWord h t p1 p2).value = Token.word (h :: t) := by rfl
private theorem printOpenBraceVal : printOpenBrace.value = openBrace := by rfl
private theorem printSemicolonVal : printSemicolon.value = semicolon := by rfl
private theorem printCloseBraceVal : printCloseBrace.value = closeBrace := by rfl

private def egName : Identifier :=
  ⟨['g'], 'g', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
    fun _ member => (List.not_mem_nil member).elim⟩

private def egTableName : Identifier :=
  ⟨['t'], 't', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
    fun _ member => (List.not_mem_nil member).elim⟩

private theorem egWrittenPrintReads (effect : WrittenCarrierEffect) (rest : List Token) :
    CarrierEffectReads ((WrittenCarrierEffect.printPieces effect).map PrintedToken.value ++ rest)
      effect rest := by
  rcases effect with ⟨access, carrier, slots⟩
  cases access <;> cases slots
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, printSlots, identPrintVal, List.map_append, List.append_assoc] using
      (CarrierEffectReads.bare CarrierAccess.read carrier (rest := rest))
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, printSlots, identPrintVal, List.map_append, List.append_assoc] using
      (CarrierEffectReads.slots CarrierAccess.read carrier (rest := rest))
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, printSlots, identPrintVal, List.map_append, List.append_assoc] using
      (CarrierEffectReads.bare CarrierAccess.write carrier (rest := rest))
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, printSlots, identPrintVal, List.map_append, List.append_assoc] using
      (CarrierEffectReads.slots CarrierAccess.write carrier (rest := rest))

private theorem egEffectListPrintReads : ∀ (written : List WrittenCarrierEffect),
    EffectListReads CarrierEffectReads
      ((commaSeparated (written.map WrittenCarrierEffect.printPieces) ++
        [printCloseBrace, printSemicolon]).map PrintedToken.value)
      written [semicolon] := by
  intro written
  induction written with
  | nil =>
      simp [commaSeparated, printCloseBrace, printSemicolon, printPunctuation,
        PrintedToken.unquoted]
      exact EffectListReads.close
  | cons effect more ih =>
      cases more with
      | nil =>
          simp [commaSeparated, List.map_append, printCloseBraceVal, printSemicolonVal]
          exact EffectListReads.last (egWrittenPrintReads effect [closeBrace, semicolon])
      | cons effect2 rest =>
          simp only [List.map_cons, commaSeparated, List.intersperse_cons_cons,
            List.flatten_append, List.flatten_cons, List.map_append, List.append_assoc,
            List.singleton_append, List.nil_append]
          refine EffectListReads.next (read := CarrierEffectReads) (head := effect)
            (next := effect2) (tail := rest) ?_ ?_
          · simpa [List.append_assoc] using egWrittenPrintReads effect (comma ::
              ((commaSeparated ((effect2 :: rest).map WrittenCarrierEffect.printPieces) ++
                [printCloseBrace, printSemicolon]).map PrintedToken.value))
          · simpa [commaSeparated] using ih

private theorem egPrint (scope : Scope) (item : EffectGroupDeclaration scope) :
    (effectGroupForm scope).produktion.production item
      (((Category.declaration scope).printPieces ((effectGroupForm scope).produktion.tree item)).map
        PrintedToken.value) := by
  change ∃ input,
    ((item.header ++ commaSeparated (item.written.map WrittenCarrierEffect.printPieces) ++
      [printCloseBrace, printSemicolon]).map PrintedToken.value) =
      item.header.map PrintedToken.value ++ input ∧
    EffectListReads CarrierEffectReads input item.written [semicolon]
  refine ⟨(commaSeparated (item.written.map WrittenCarrierEffect.printPieces) ++
    [printCloseBrace, printSemicolon]).map PrintedToken.value, ?_, ?_⟩
  · simp only [List.map_append, List.append_assoc]
  · exact egEffectListPrintReads item.written

theorem effectGroup_inversion : EffectGroupInversionAussage := by
  intro scope input tree rest head read
  generalize hh : head.header.map PrintedToken.value ++ input = hs at read
  cases read with
  | effectGroup item effectRead =>
      rename_i input'
      by_cases he : head.exported
      · by_cases ie : item.exported
        · have hh' := hh
          simp [EffectGroupDeclaration.header, he, ie, printPub, printEffects,
            identPrintVal, printOpenBraceVal] at hh'
          obtain ⟨hval, hin⟩ := hh'
          have hnameval : head.name.val = item.name.val := by
            simpa [identPrintVal] using hval
          refine ⟨item, Subtype.ext hnameval.symm, by rw [he, ie], ?_, ?_⟩
          · rw [← hin]
            exact effectRead
          · rfl
        · have hh' := hh
          simp [EffectGroupDeclaration.header, he, ie, printPub, printEffects,
            identPrintVal, printOpenBraceVal] at hh'
      · by_cases ie : item.exported
        · have hh' := hh
          simp [EffectGroupDeclaration.header, he, ie, printPub, printEffects,
            identPrintVal, printOpenBraceVal] at hh'
        · have hh' := hh
          simp [EffectGroupDeclaration.header, he, ie, printPub, printEffects,
            identPrintVal, printOpenBraceVal] at hh'
          obtain ⟨hval, hin⟩ := hh'
          have hnameval : head.name.val = item.name.val := by
            simpa [identPrintVal] using hval
          have hhe : head.exported = false := by cases head.exported <;> simp_all
          have hie : item.exported = false := by cases item.exported <;> simp_all
          refine ⟨item, Subtype.ext hnameval.symm, by rw [hhe, hie], ?_, ?_⟩
          · rw [← hin]
            exact effectRead
          · rfl
  | constant =>
      by_cases he : head.exported <;>
        simp [EffectGroupDeclaration.header, he, printPub, printEffects, identPrintVal,
          printOpenBraceVal, keyword, printConst] at hh
  | function =>
      by_cases he : head.exported <;>
        simp [EffectGroupDeclaration.header, he, printPub, printEffects, identPrintVal,
          printOpenBraceVal, keyword, printFn] at hh
  | record exported name fields valid distinct memberRead =>
      rename_i input'
      by_cases he : head.exported <;> by_cases ex : exported <;>
        simp [EffectGroupDeclaration.header, he, printPub, printEffects, identPrintVal,
          printOpenBraceVal, recordDeclarationPrefix, keyword, printTypeDecl, ex] at hh
  | tagged exported name valid distinct first more =>
      rename_i input'
      by_cases he : head.exported <;> by_cases ex : exported <;>
        simp [EffectGroupDeclaration.header, he, printPub, printEffects, identPrintVal,
          printOpenBraceVal, taggedDeclarationPrefix, keyword, printTypeDecl, ex] at hh
  | table item =>
      rename_i input'
      by_cases he : head.exported <;> by_cases ex : item.exported <;>
        simp [EffectGroupDeclaration.header, he, printPub, printEffects, identPrintVal,
          printOpenBraceVal, TableDeclaration.header, keyword, ex] at hh

theorem effectGroup_derivation : EffectGroupDerivationAussage := by
  intro scope
  refine ⟨?reads, egPrint scope, ?sat⟩
  · intro item tokens production
    rcases production with ⟨input, rfl, effectRead⟩
    exact DeclReads.effectGroup item effectRead
  · exact Rule.satisfiableOfPrint egName (egPrint scope
      ⟨false, egName, [], [], rfl⟩)

private theorem eg_amOrt (scope : Scope) : (effectGroupForm scope).RegelAmOrt := by
  intro item
  rfl

theorem effectGroup_parse : EffectGroupParseAussage := by
  intro scope args text pieces lexed prod
  exact (effectGroup_derivation scope).parse lexed prod

theorem effectGroup_elaboriert : EffectGroupElaboriertAussage := by
  intro scope platform args
  rfl

theorem effectGroup_realisiert : EffectGroupRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (effectGroupForm scope).realisiert (eg_amOrt scope) platform args s running active live atPc

theorem effectGroup_annahme : EffectGroupAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (effectGroupForm scope)

theorem effectGroup_ideal : EffectGroupIdealAussage := by
  intro scope
  refine ⟨eg_amOrt scope, ?_⟩
  intro args
  exact ⟨((effectGroupForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem effectGroup_einheit : EffectGroupEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((effectGroupForm scope).befehl args).kommutation⟩

theorem effectGroup_impl : EffectGroupImplAussage := by
  intro scope args c s w plans u
  rfl

theorem effectGroup_erhaltung : EffectGroupErhaltungAussage := by
  intro scope platform args
  let p := (effectGroupForm scope).fragment args
  let b := (effectGroupForm scope).befehl args
  exact ⟨b.abgleich p platform, b.fortschritt p, b.komponierbar p platform,
    b.sicher p platform (by rfl)⟩

theorem effectGroup_regelSicher : EffectGroupRegelSicherAussage := by
  intro scope platform args
  exact (effectGroup_erhaltung scope platform args).2.2.2

private theorem mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.length = ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp [List.mapM] at h
      subst ys
      rfl
  | cons x xs ih =>
      intro ys h
      simp only [List.mapM_cons] at h
      cases hfx : f x with
      | none => simp [hfx] at h
      | some y =>
          cases hrest : xs.mapM f with
          | none => simp [hfx, hrest] at h
          | some ys' =>
              simp [hfx, hrest] at h
              subst ys
              simp [ih xs ys' hrest]

private theorem mapM_option_getElem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β) (i : Nat),
      xs.mapM f = some ys → i < xs.length → ∃ y, f (xs[i]) = some y ∧ ys[i] = y := by
  intro xs
  induction xs with
  | nil =>
      intro ys i h hi
      simp [List.mapM] at hi
  | cons x xs ih =>
      intro ys i h hi
      simp only [List.mapM_cons] at h
      cases hfx : f x with
      | none => simp [hfx] at h
      | some y =>
          cases hrest : xs.mapM f with
          | none => simp [hfx, hrest] at h
          | some ys' =>
              simp [hfx, hrest] at h
              subst ys
              cases i with
              | zero => exact ⟨y, hfx, rfl⟩
              | succ i =>
                  have hi' : i < xs.length := by simpa using hi
                  obtain ⟨y', hy', hys'⟩ := ih ys' i hrest hi'
                  exact ⟨y', hy', by simpa using hys'⟩

theorem effectGroup_expansion : EffectGroupExpansionAussage := by
  intro scope bound terms expanded h
  let f := EffectTerm.resolve scope bound
  rcases hm : terms.mapM f with _ | parts
  · simp [expandEffects, hm] at h
  · refine ⟨parts, ?_, ?_, ?_⟩
    · exact (mapM_option_length f terms parts hm).symm
    · intro i term part hterm hpart
      have ht : terms[i] = term := (List.getElem?_eq_some_iff.mp hterm).2
      have hp : parts[i] = part := (List.getElem?_eq_some_iff.mp hpart).2
      rw [← ht, ← hp]
      obtain ⟨y, hy, hys⟩ := mapM_option_getElem f terms parts i hm
        (List.getElem?_eq_some_iff.mp hterm).1
      rw [hys]
      exact hy
    · simpa [expandEffects, hm] using h

theorem effectGroup_scope : EffectGroupScopeAussage := by
  intro scope item
  constructor
  · simp [Scope.effectGroup, EffectGroupDeclaration.binding, effectGroupBinding,
      beq_iff_eq]
  constructor
  · simp [EffectGroupDeclaration.binding, effectGroupBinding, Ty.valueBinding]
  · intro name hne
    simp [Scope.effectGroup, EffectGroupDeclaration.binding, effectGroupBinding,
      beq_iff_eq, hne, Ne.symm hne]

theorem effectGroup_visibility : EffectGroupVisibilityAussage := by
  intro scope item hexported effect heffect
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp heffect
  have hi_lt : i < item.written.length := (List.getElem?_eq_some_iff.mp hi).1
  have hpoint := mapM_option_getElem (WrittenCarrierEffect.resolve scope item.exported)
    item.written item.resolved i item.checked hi_lt
  have hw : item.written[i] = effect := (List.getElem?_eq_some_iff.mp hi).2
  rw [hw] at hpoint
  obtain ⟨value, hresolve, _⟩ := hpoint
  dsimp [WrittenCarrierEffect.resolve] at hresolve
  cases hc : scope.effectCarrier effect.carrier with
  | none => simp [hc] at hresolve
  | some pair =>
      rcases pair with ⟨position, exportedFlag⟩
      by_cases hflag : exportedFlag
      · exact ⟨position, by simpa [hc, hflag]⟩
      · simp [hc, hexported, hflag] at hresolve

theorem effectGroup_capture : EffectGroupCaptureAussage := by
  intro scope bound name effects hscope hcap
  dsimp [EffectTerm.resolve]
  rcases hcap with hb | ⟨effect, heffect, hb⟩
  · simp [hb]
  · have hany : effects.any (fun effect => bound.contains effect.carrier) = true :=
      List.any_eq_true.mpr ⟨effect, heffect, hb⟩
    simp [hscope, hany]

private theorem codeRufe_effects (code : List Befehl) (E : Option (List CarrierEffect)) :
    ∀ site ∈ code.filterMap (fun
        | .rufe target args bind => some ⟨target, args, bind, E⟩
        | _ => none), site.effects = E := by
  induction code with
  | nil => simp
  | cons cmd cmds ih =>
      intro site hmem
      simp only [List.filterMap_cons] at hmem
      cases cmd with
      | rufe target args bind =>
          simp at hmem
          rcases hmem with h | h
          · subst site
            rfl
          · exact ih site h
      | _ =>
          simp at hmem
          exact ih site hmem

theorem effectGroup_signature : EffectGroupSignatureAussage := by
  intro scope a frame
  dsimp only
  let code := functionCode a.result a.measure a.body
  let E := declaredEffects a.effects
  let f : Funktion := ⟨a.name, frame.pc + 1, a.parameters.map (fun p => p.written.type),
    writtenResult a.result, scope.length, a.measure.isSome,
    code.code.filterMap (fun
      | .rufe target args bind => some ⟨target, args, bind, E⟩
      | _ => none), E⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · simp [functionForm, functionInstruction, Befehl.auswerten, f, E, code]
  · simp [f, E]
  · intro site hsite
    exact codeRufe_effects code.code E site hsite

theorem effectGroup_call : EffectGroupCallAussage := by
  intro site functions target provided hfind heff hpasses effect hrequired
  have hp := hpasses
  simp only [Rufstelle.passt, hfind, heff] at hp
  have hall : (Funktion.requiredEffects functions target).all
      (fun effect => decide (effect ∈ provided)) = true := by
    simpa only [Bool.and_eq_true] using hp.2.2.1
  exact List.all_eq_true.mp hall effect hrequired

theorem effectGroup_binding : EffectGroupBindingAussage := by
  intro scope item frame
  simp [effectGroupForm, Befehl.auswerten, EffectGroupDeclaration.binding,
    effectGroupBinding, Rahmen.installSchema]

theorem effectGroup_erfuellbarAm : EffectGroupErfuellbarAmAussage := by
  intro platform start
  let scope : Scope := [carrierBinding egTableName 1 [] true]
  let written : WrittenCarrierEffect := ⟨.read, egTableName, false⟩
  let eff : CarrierEffect := ⟨0, egTableName.val, .read⟩
  have hchecked : [written].mapM (WrittenCarrierEffect.resolve scope true) = some [eff] := by
    simp [written, eff, scope, WrittenCarrierEffect.resolve, Scope.effectCarrier,
      carrierBinding, egTableName]
  let item : EffectGroupDeclaration scope := ⟨true, egName, [written], [eff], hchecked⟩
  refine ⟨scope, item, ?_, ?_⟩
  · simp [item, eff]
  · let form := effectGroupForm scope
    let E := form.einheit platform item
    let s := (I.start E start).2
    refine form.erfuellbar_aus_erreichbar platform start item s .start
      (form.realisiert (eg_amOrt scope) platform item s rfl rfl rfl rfl) ?_
    intro g guard
    cases guard

end Gabbro.Core.Ast.Semantik
