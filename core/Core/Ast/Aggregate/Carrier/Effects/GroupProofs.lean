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
private theorem printDotVal : printDot.value = dot := by rfl
private theorem printSlotsVal : printSlots.value = Token.word ['s', 'l', 'o', 't', 's'] := by rfl
private theorem printCommaVal : printComma.value = comma := by rfl
private theorem ifTrue {α : Type} (t e : α) : (if True then t else e) = t := rfl
private theorem ifFalse {α : Type} (t e : α) : (if False then t else e) = e := rfl
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
      printDot, dot, printPunctuation, printSlots, keywordName, Identifier.print,
      PrintedToken.unquoted, identPrintVal, printDotVal, printSlotsVal,
      List.map_append, List.append_assoc] using
      (CarrierEffectReads.bare CarrierAccess.read carrier (rest := rest))
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, dot, printPunctuation, printSlots, keywordName, Identifier.print,
      PrintedToken.unquoted, identPrintVal, printDotVal, printSlotsVal,
      List.map_append, List.append_assoc] using
      (CarrierEffectReads.slots CarrierAccess.read carrier (rest := rest))
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, dot, printPunctuation, printSlots, keywordName, Identifier.print,
      PrintedToken.unquoted, identPrintVal, printDotVal, printSlotsVal,
      List.map_append, List.append_assoc] using
      (CarrierEffectReads.bare CarrierAccess.write carrier (rest := rest))
  · simpa [WrittenCarrierEffect.printPieces, CarrierAccess.print, printProgramWord, keyword,
      printDot, dot, printPunctuation, printSlots, keywordName, Identifier.print,
      PrintedToken.unquoted, identPrintVal, printDotVal, printSlotsVal,
      List.map_append, List.append_assoc] using
      (CarrierEffectReads.slots CarrierAccess.write carrier (rest := rest))
private def egTokens : List WrittenCarrierEffect → List Token
  | [] => []
  | effect :: more =>
      (WrittenCarrierEffect.printPieces effect).map PrintedToken.value ++
        match more with
        | [] => []
        | _ => comma :: egTokens more
private theorem egTokens_eq (written : List WrittenCarrierEffect) :
    egTokens written = (commaSeparated (written.map WrittenCarrierEffect.printPieces)).map
      PrintedToken.value := by
  induction written with
  | nil => rfl
  | cons effect more ih =>
      cases more with
      | nil => simpa [egTokens, commaSeparated]
      | cons effect2 rest =>
          change (WrittenCarrierEffect.printPieces effect).map PrintedToken.value ++
            comma :: egTokens (effect2 :: rest) =
            (commaSeparated ((effect :: effect2 :: rest).map
              WrittenCarrierEffect.printPieces)).map PrintedToken.value
          rw [ih]
          simp only [commaSeparated, printCommaVal, List.map_append, List.append_assoc,
            List.cons_append, List.nil_append, List.intersperse_cons_cons, List.flatten_cons,
            List.flatten_nil, List.map_cons, List.map_nil]
private theorem egTokensReads : ∀ (written : List WrittenCarrierEffect) (rest : List Token),
    EffectListReads CarrierEffectReads (egTokens written ++ closeBrace :: rest) written rest := by
  intro written
  induction written with
  | nil =>
      intro rest
      simp only [egTokens, List.nil_append]
      exact EffectListReads.close
  | cons effect more ih =>
      intro rest
      cases more with
      | nil =>
          simp only [egTokens, List.append_nil]
          exact EffectListReads.last (egWrittenPrintReads effect (closeBrace :: rest))
      | cons effect2 tail =>
          simp only [egTokens, List.map_append, List.append_assoc, List.cons_append]
          refine EffectListReads.next (read := CarrierEffectReads) (head := effect)
            (more := egTokens (effect2 :: tail) ++ closeBrace :: rest)
            (next := effect2) (tail := tail) ?_ ?_
          · simpa [egTokens, List.append_assoc] using egWrittenPrintReads effect
              (comma :: egTokens (effect2 :: tail) ++ closeBrace :: rest)
          · exact ih rest
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
  · simpa [List.map_append, egTokens_eq, printCloseBraceVal, printSemicolonVal,
      List.append_assoc] using (egTokensReads item.written [semicolon])
theorem effectGroup_inversion : EffectGroupInversionAussage := by
  intro scope input tree rest head read
  generalize hh : head.header.map PrintedToken.value ++ input = hs at read
  cases read with
  | effectGroup item effectRead =>
      rename_i input'
      by_cases he : head.exported
      · by_cases ie : item.exported
        · have hh' := hh
          simp only [EffectGroupDeclaration.header, he, ie, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, ifTrue, ifFalse, Bool.false_eq_true, Bool.true_eq, keywordName, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc] at hh'
          have c1 := List.cons.inj hh'
          have c2 := List.cons.inj c1.2
          have c3 := List.cons.inj c2.2
          have c4 := List.cons.inj c3.2
          have hnameval : item.name = head.name := by
            apply Subtype.ext
            exact (Token.word.inj c3.1).symm
          have hin : input = input' := c4.2
          refine ⟨item, hnameval, by rw [he, ie], ?_, ?_⟩
          · rw [hin]
            exact effectRead
          · rfl
        · have hh' := hh
          simp only [EffectGroupDeclaration.header, he, ie, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, ifTrue, ifFalse, Bool.false_eq_true, Bool.true_eq, keywordName, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc] at hh'
          cases hh'
      · by_cases ie : item.exported
        · have hh' := hh
          simp only [EffectGroupDeclaration.header, he, ie, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, ifTrue, ifFalse, Bool.false_eq_true, Bool.true_eq, keywordName, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc] at hh'
          cases hh'
        · have hh' := hh
          simp only [EffectGroupDeclaration.header, he, ie, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, ifTrue, ifFalse, Bool.false_eq_true, Bool.true_eq, keywordName, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc] at hh'
          have c1 := List.cons.inj hh'
          have c2 := List.cons.inj c1.2
          have c3 := List.cons.inj c2.2
          have hnameval : item.name = head.name := by
            apply Subtype.ext
            exact (Token.word.inj c2.1).symm
          have hin : input = input' := c3.2
          have hhe : head.exported = false := by simpa using he
          have hie : item.exported = false := by simpa using ie
          refine ⟨item, hnameval, by rw [hhe, hie], ?_, ?_⟩
          · rw [hin]
            exact effectRead
          · rfl
  | constant =>
      by_cases he : head.exported <;>
        simp_all [EffectGroupDeclaration.header, he, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, keyword, printConst]
  | function =>
      by_cases he : head.exported <;>
        simp_all [EffectGroupDeclaration.header, he, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, keyword, printFn]
  | record exported name valid distinct memberRead =>
      rename_i fields input'
      by_cases he : head.exported <;> by_cases ex : exported <;>
        simp_all [EffectGroupDeclaration.header, he, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, recordDeclarationPrefix, keyword, printTypeDecl, ex]
  | tagged exported name valid distinct firstRead tailRead =>
      by_cases he : head.exported <;> by_cases ex : exported <;>
        simp_all [EffectGroupDeclaration.header, he, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, taggedDeclarationPrefix, keyword, printTypeDecl, ex]
  | table item =>
      by_cases he : head.exported <;> by_cases ex : item.exported <;>
        simp_all [EffectGroupDeclaration.header, he, printPub, printEffects, ppwVal, identPrintVal, printOpenBraceVal, TableDeclaration.header, printTable, printCount, printSlot, keywordName, Identifier.print, PrintedToken.unquoted, ppwVal, keyword, ex]
theorem effectGroup_derivation : EffectGroupDerivationAussage := by
  intro scope
  refine ⟨?reads, egPrint scope, ?sat⟩
  · intro item tokens production
    rcases production with ⟨input, rfl, effectRead⟩
    exact DeclReads.effectGroup item effectRead
  · exact Surface.Rule.satisfiableOfPrint ⟨false, egName, [], [], rfl⟩
      (egPrint scope ⟨false, egName, [], [], rfl⟩)
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
    b.sicherheitsPflichten p platform (by rfl)⟩
theorem effectGroup_regelSicher : EffectGroupRegelSicherAussage := by
  intro scope platform args
  exact (effectGroup_erhaltung scope platform args).2.2.2.1
private theorem mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → xs.length = ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst ys
      rfl
  | cons x xs ih =>
      intro ys h
      simp only [List.mapM_cons] at h
      cases hfx : f x with
      | none => simp only [hfx, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
      | some y =>
          cases hrest : xs.mapM f with
          | none => simp only [hfx, hrest, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.pure_def, Option.some.injEq, reduceCtorEq] at h
          | some ys' =>
              simp only [hfx, hrest, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.pure_def, Option.some.injEq, reduceCtorEq] at h
              subst ys
              simpa [ih ys' hrest]
private theorem mapM_option_getElem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β) (i : Nat) (hi : i < xs.length) (hi' : i < ys.length),
      xs.mapM f = some ys → f (xs[i]'hi) = some (ys[i]'hi') := by
  intro xs
  induction xs with
  | nil =>
      intro ys i hi hi' h
      simp at hi
  | cons x xs ih =>
      intro ys i hi hi' h
      simp only [List.mapM_cons] at h
      cases hfx : f x with
      | none => simp only [hfx, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
      | some y =>
          cases hrest : xs.mapM f with
          | none => simp only [hfx, hrest, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.pure_def, Option.some.injEq, reduceCtorEq] at h
          | some ys' =>
              simp only [hfx, hrest, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.pure_def, Option.some.injEq, reduceCtorEq] at h
              subst ys
              cases i with
              | zero => exact hfx
              | succ i =>
                  have hsuccess : i < xs.length := by simpa using hi
                  have hsuccess' : i < ys'.length := by simpa using hi'
                  exact ih ys' i hsuccess hsuccess' hrest
theorem effectGroup_expansion : EffectGroupExpansionAussage := by
  intro scope bound terms expanded h
  let f := EffectTerm.resolve scope bound
  rcases hm : terms.mapM f with _ | parts
  · rw [expandEffects] at h
    rw [show (terms.mapM f).map List.flatten = none by simp only [hm, Option.map_none]] at h
    cases h
  · refine ⟨parts, ?_, ?_, ?_⟩
    · exact (mapM_option_length f terms parts hm).symm
    · intro i term part hterm hpart
      have hi : i < terms.length := (List.getElem?_eq_some_iff.mp hterm).1
      have hi' : i < parts.length := by
        rw [← mapM_option_length f terms parts hm]
        exact hi
      have ht : terms[i]'hi = term := by
        simpa using (List.getElem?_eq_some_iff.mp hterm).2
      have hp : parts[i]'hi' = part := by
        simpa using (List.getElem?_eq_some_iff.mp hpart).2
      rw [← ht, ← hp]
      exact mapM_option_getElem f terms parts i hi hi' hm
    · rw [expandEffects] at h
      have hmapped : (terms.mapM f).map List.flatten = some parts.flatten := by simp only [hm, Option.map_some]
      rw [hmapped] at h
      cases h
      rfl
theorem effectGroup_scope : EffectGroupScopeAussage := by
  intro scope item
  constructor
  · simpa [Scope.effectGroup, EffectGroupDeclaration.binding, effectGroupBinding, beq_iff_eq]
  constructor
  · simpa [EffectGroupDeclaration.binding, effectGroupBinding, Ty.valueBinding]
  · intro name hne
    simpa [Scope.effectGroup, EffectGroupDeclaration.binding, effectGroupBinding, beq_iff_eq, hne, Ne.symm hne]
theorem effectGroup_visibility : EffectGroupVisibilityAussage := by
  intro scope item hexported effect heffect
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp heffect
  have hi_lt : i < item.written.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_lt' : i < item.resolved.length := by
    rw [← mapM_option_length (WrittenCarrierEffect.resolve scope item.exported)
      item.written item.resolved item.checked]
    exact hi_lt
  have hresolve := mapM_option_getElem (WrittenCarrierEffect.resolve scope item.exported)
    item.written item.resolved i hi_lt hi_lt' item.checked
  have hw : item.written[i]'hi_lt = effect := by
    simpa using (List.getElem?_eq_some_iff.mp hi).2
  rw [hw] at hresolve
  dsimp [WrittenCarrierEffect.resolve] at hresolve
  cases hc : scope.effectCarrier effect.carrier with
  | none => simp only [WrittenCarrierEffect.resolve, hc, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hresolve
  | some pair =>
      rcases pair with ⟨position, exportedFlag⟩
      by_cases hflag : exportedFlag
      · exact ⟨position, by simpa [hc, hflag]⟩
      · simp_all
theorem effectGroup_capture : EffectGroupCaptureAussage := by
  intro scope bound name effects hscope hcap
  dsimp [EffectTerm.resolve]
  simp only [hscope, Option.bind_some]
  split
  · rfl
  · rename_i hcond
    split
    · rfl
    · rename_i hnotany
      rcases hcap with hb | ⟨effect, heffect, hb⟩
      · exact (hcond (Or.inr hb)).elim
      · exact (hnotany (List.any_eq_true.mpr ⟨effect, heffect, hb⟩)).elim
private theorem codeRufe_effects (code : List Befehl) (E : Option (List CarrierEffect)) :
    ∀ site ∈ code.filterMap (fun
        | .rufe target args bind => some (⟨target, args, bind, E⟩ : Rufstelle)
        | _ => none), site.effects = E := by
  induction code with
  | nil => intro site hmem; simp at hmem
  | cons cmd cmds ih =>
      intro site hmem
      cases hcmd : (match cmd with
        | .rufe target args bind => some (⟨target, args, bind, E⟩ : Rufstelle)
        | _ => none) with
      | none =>
          simp only [hcmd, List.mem_filterMap] at hmem
          obtain ⟨a, ha, hfa⟩ := hmem
          cases ha with
          | head =>
              cases cmd with
              | rufe target args bind => simp at hcmd
              | _ => simp at hfa
          | tail _ ha =>
              exact ih site (List.mem_filterMap.mpr ⟨a, ha, hfa⟩)
      | some first =>
          cases cmd with
          | rufe target args bind =>
              injection hcmd with hfirst
              subst first
              simp at hmem
              rcases hmem with h | hmem
              · subst site
                rfl
              · exact ih site (List.mem_filterMap.mpr hmem)
          | _ => simp at hcmd
theorem effectGroup_signature : EffectGroupSignatureAussage := by
  intro scope a frame
  dsimp only
  let code := functionCode a.result a.measure a.body
  let E := declaredEffects a.effects
  let f : Funktion := ⟨a.name, frame.pc + 1, a.parameters.map (fun p => p.written.type),
    writtenResult a.result, scope.length, a.measure.isSome,
    code.code.filterMap (fun
      | .rufe target args bind => some (⟨target, args, bind, E⟩ : Rufstelle)
      | _ => none), E⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · simp only [functionForm, functionInstruction, Befehl.auswerten, f, E, code]
    rfl
  · simpa [f, E]
  · intro site hsite
    exact codeRufe_effects code.code E site hsite
theorem effectGroup_call : EffectGroupCallAussage := by
  intro site functions target provided hfind heff hpasses effect hrequired
  have hp := hpasses
  simp only [Rufstelle.passt, hfind, heff] at hp
  simp only [Bool.and_eq_true] at hp
  have hall : (Funktion.requiredEffects functions target).all
      (fun effect => decide (effect ∈ provided)) = true := hp.left.right
  exact decide_eq_true_iff.mp (List.all_eq_true.mp hall effect hrequired)
theorem effectGroup_binding : EffectGroupBindingAussage := by
  intro scope item frame
  simpa [effectGroupForm, Befehl.auswerten, EffectGroupDeclaration.binding, effectGroupBinding, Rahmen.installSchema]
theorem effectGroup_erfuellbarAm : EffectGroupErfuellbarAmAussage := by
  intro platform start
  let scope : Scope := [carrierBinding egTableName 1 [] true]
  let written : WrittenCarrierEffect := ⟨.read, egTableName, false⟩
  let eff : CarrierEffect := ⟨0, egTableName.val, .read⟩
  have hchecked : [written].mapM (WrittenCarrierEffect.resolve scope true) = some [eff] := by
    simpa [written, eff, scope, WrittenCarrierEffect.resolve, Scope.effectCarrier, carrierBinding, egTableName]
  let item : EffectGroupDeclaration scope := ⟨true, egName, [written], [eff], hchecked⟩
  refine ⟨scope, item, ?_, ?_⟩
  · simpa [item, eff]
  · let form := effectGroupForm scope
    let E := form.einheit platform item
    let s := (I.start E start).2
    refine form.erfuellbar_aus_erreichbar platform start item s .start
      (form.realisiert (eg_amOrt scope) platform item s rfl rfl rfl rfl) ?_
    intro g guard
    cases guard
theorem effectGroup_useErfuellbar : EffectGroupUseErfuellbarAussage := by
  intro platform start
  let carrier : TableDeclaration [] :=
    ⟨true, egTableName, 1, [], (by intro f h; cases h), by exact List.nodup_nil⟩
  let written : WrittenCarrierEffect := ⟨.read, egTableName, false⟩
  let eff : CarrierEffect := ⟨0, egTableName.val, .read⟩
  have hresolve : WrittenCarrierEffect.resolve [carrier.binding] true written = some eff := by
    simpa [WrittenCarrierEffect.resolve, Scope.effectCarrier, carrier, carrierBinding, TableDeclaration.binding, written, eff, egTableName]
  have hchecked : [written].mapM (WrittenCarrierEffect.resolve [carrier.binding] true) =
      some [eff] := by
    simpa [List.mapM_cons, List.mapM_nil, hresolve]
  let group : EffectGroupDeclaration [carrier.binding] :=
    ⟨true, egName, [written], [eff], hchecked⟩
  let scope : Scope := [group.binding, carrier.binding]
  have hclause : expandEffects scope [] [.group group.name] = some [eff] := by
    simpa [expandEffects, EffectTerm.resolve, Scope.effectGroup, EffectGroupDeclaration.binding, effectGroupBinding, scope, group, eff, egName, beq_iff_eq]
  let clause : EffectClause scope [] := ⟨[.group group.name], [eff], hclause⟩
  let fnName : Identifier :=
    ⟨['f'], 'f', [], rfl, Or.inl (Or.inl ⟨by decide, by decide⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have hdirect : directName fnName := by
    simpa [directName, ordinaryLocal, ordinaryAtomWord, fnName]
  let body : BracedBlock (writtenResult none) (functionScope scope []) := .braces .done
  let a : Surface.FunctionArgs scope :=
    ⟨fnName, hdirect, [], none, (by intro t h; cases h), none, body, by simp_all,
      (by intro h; cases h), some clause⟩
  let tree : Ast.Unit :=
    ⟨_, .step (.table carrier) (.step (.effectGroup group) (.step a.declaration .done))⟩
  let E := elaborieren (category := .unit) platform tree
  let bt : Befehl := tableInstruction carrier
  let bg : Befehl := .definiereEffektgruppe group.resolved
  let b : Befehl := (functionForm scope).befehl a
  let s0 := (I.start E start).2
  let s1 := bt.nach eintritt s0
  let s := bg.nach eintritt s1
  have hhead0 : E.system.kopf s0 eintritt = some bt := by
    change kopf (programm tree).code s0 eintritt = some bt
    simpa [E, tree, kopf, programm, unitBody, decl, tableInstruction, s0, I.start, Zustand.start, startdaten, Fragment.einheit, Fragment.anhaengen, Fragment.einzel, Fragment.leer, elaborieren, fragment, eintritt, Rahmen.start, bt]
  have hhead1 : E.system.kopf s1 eintritt = some bg := by
    change kopf (programm tree).code s1 eintritt = some bg
    simpa [E, tree, kopf, programm, unitBody, decl, tableInstruction, s1, s0, I.start, Zustand.start, startdaten, Fragment.einheit, Fragment.anhaengen, Fragment.einzel, Fragment.leer, elaborieren, fragment, eintritt, Rahmen.start, Rahmen.installSchema, Befehl.nach, Befehl.auswerten, EffectGroupDeclaration.binding, effectGroupBinding, bt, bg]
  have hhead2 : E.system.kopf s eintritt = some b := by
    change kopf (programm tree).code s eintritt = some b
    simpa [E, tree, kopf, programm, unitBody, decl, tableInstruction, s, s1, s0, I.start, Zustand.start, startdaten, Fragment.einheit, Fragment.anhaengen, Fragment.einzel, Fragment.leer, elaborieren, fragment, eintritt, Rahmen.start, Rahmen.installSchema, Befehl.nach, Befehl.auswerten, EffectGroupDeclaration.binding, effectGroupBinding, functionForm, functionInstruction, bt, bg, b, scope, a, Surface.FunctionArgs.declaration]
  have hstep0 : E.system.ISchritt eintritt s0 () [plan] s1 := ⟨bt, hhead0, rfl, rfl⟩
  have hstep1 : E.system.ISchritt eintritt s1 () [plan] s := ⟨bg, hhead1, rfl, rfl⟩
  have hstep2 : E.system.ISchritt eintritt s () [plan] (b.nach eintritt s) :=
    ⟨b, hhead2, rfl, rfl⟩
  have himpl2 : E.system.ImplSchritt eintritt s () [plan] (b.nach eintritt s) :=
    ⟨b, hhead2, rfl, rfl⟩
  have reached : E.system.IErreichbar s0 s :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start hstep0) hstep1
  refine ⟨carrier, group, a, Ast.print (category := .unit) tree, s, ?_⟩
  dsimp only
  refine ⟨?_, ?_, Ast.parse_print (category := .unit) tree, rfl, reached, hhead2,
    hstep2, himpl2, ?_⟩
  · simpa [group, eff]
  · exact ⟨clause, rfl, rfl⟩
  · let after := b.auswerten (s.lokal eintritt)
    let sig : Funktion := ⟨a.name, (s.lokal eintritt).pc + 1, [], none, scope.length,
      false, [], some [eff]⟩
    refine ⟨sig, ?_, ?_⟩
    · simpa [after, sig, b, functionForm, functionInstruction, Befehl.auswerten,
        a, scope, clause, body, functionCode, bracedBlock, Fragment.anhaengen, Fragment.einzel,
        Fragment.leer, block, writtenResult, declaredEffects]
    · simpa [sig, group, eff]
end Gabbro.Core.Ast.Semantik
