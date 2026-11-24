module

public import Core.Ast.Semantik.Formbeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem trueLit_parse (ctx : Scope) : (trueLitForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.trueLit_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem trueLit_elaboriert (ctx : Scope) : (trueLitForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem trueLit_realisiert (ctx : Scope) : (trueLitForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (trueLitForm ctx).realisiert (fun _ => rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem trueLit_annahme (ctx : Scope) : (trueLitForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (trueLitForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem trueLit_ideal (ctx : Scope) : (trueLitForm ctx).IdealAussage := by
  refine ⟨(fun _ => rfl), fun args => ?_⟩
  exact ⟨((trueLitForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem trueLit_einheit (ctx : Scope) : (trueLitForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((trueLitForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem trueLit_impl (ctx : Scope) : (trueLitForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem trueLit_erhaltung (ctx : Scope) : (trueLitForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (trueLitForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.trueLit ctx).tree args).2)

-- Mirror literal_erfuellbar using the actual source head and its pre-state.
theorem trueLit_erfuellbar : trueLitJoint := by
  intro platform start
  let form := trueLitForm []
  let s := (Maschine.I.start (form.einheit platform PUnit.unit) start).2
  refine form.erfuellbar_aus_erreichbar platform start PUnit.unit s .start
    (form.realisiert (fun _ => rfl) platform PUnit.unit s rfl rfl rfl rfl) ?_
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem falseLit_parse (ctx : Scope) : (falseLitForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.falseLit_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem falseLit_elaboriert (ctx : Scope) : (falseLitForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem falseLit_realisiert (ctx : Scope) : (falseLitForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (falseLitForm ctx).realisiert (fun _ => rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem falseLit_annahme (ctx : Scope) : (falseLitForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (falseLitForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem falseLit_ideal (ctx : Scope) : (falseLitForm ctx).IdealAussage := by
  refine ⟨(fun _ => rfl), fun args => ?_⟩
  exact ⟨((falseLitForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem falseLit_einheit (ctx : Scope) : (falseLitForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((falseLitForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem falseLit_impl (ctx : Scope) : (falseLitForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem falseLit_erhaltung (ctx : Scope) : (falseLitForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (falseLitForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.falseLit ctx).tree args).2)

-- Mirror literal_erfuellbar using the actual source head and its pre-state.
theorem falseLit_erfuellbar : falseLitJoint := by
  intro platform start
  let form := falseLitForm []
  let s := (Maschine.I.start (form.einheit platform PUnit.unit) start).2
  refine form.erfuellbar_aus_erreichbar platform start PUnit.unit s .start
    (form.realisiert (fun _ => rfl) platform PUnit.unit s rfl rfl rfl rfl) ?_
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem variable_parse (ctx : Scope) : (variableForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.variable_entry args).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem variable_elaboriert (ctx : Scope) : (variableForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem variable_realisiert (ctx : Scope) : (variableForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (variableForm ctx).realisiert (fun _ => rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem variable_annahme (ctx : Scope) : (variableForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (variableForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem variable_ideal (ctx : Scope) : (variableForm ctx).IdealAussage := by
  refine ⟨(fun _ => rfl), fun args => ?_⟩
  exact ⟨((variableForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem variable_einheit (ctx : Scope) : (variableForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((variableForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem variable_impl (ctx : Scope) : (variableForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem variable_erhaltung (ctx : Scope) : (variableForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (variableForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.localValue ctx).tree args).2)

-- Mirror literal_erfuellbar using the actual source head and its pre-state.
theorem variable_erfuellbar : variableJoint := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl,
      Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : ordinaryLocal name := (directName_of_singleton (name := name) rfl).1
  let scope : Scope := [⟨name, .bool, false, false⟩]
  let ref : Local scope .bool := .here
  let args : Surface.VariableArgs scope := ⟨ref, ⟨trivial, trivial⟩, ordinary⟩
  let form := variableForm scope
  let s := (Maschine.I.start (form.einheit platform args) start).2
  refine ⟨scope, args, form.erfuellbar_aus_erreichbar platform start args s .start
    (form.realisiert (fun _ => rfl) platform args s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem negativeLit_parse (ctx : Scope) : (negativeLitForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.negativeLit_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem negativeLit_elaboriert (ctx : Scope) : (negativeLitForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem negativeLit_realisiert (ctx : Scope) : (negativeLitForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (negativeLitForm ctx).realisiert (fun _ => rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem negativeLit_annahme (ctx : Scope) : (negativeLitForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (negativeLitForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem negativeLit_ideal (ctx : Scope) : (negativeLitForm ctx).IdealAussage := by
  refine ⟨(fun _ => rfl), fun args => ?_⟩
  exact ⟨((negativeLitForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem negativeLit_einheit (ctx : Scope) : (negativeLitForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((negativeLitForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem negativeLit_impl (ctx : Scope) : (negativeLitForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem negativeLit_erhaltung (ctx : Scope) : (negativeLitForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (negativeLitForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.negativeLit ctx).tree args).2)

-- Mirror literal_erfuellbar using the actual source head and its pre-state.
theorem negativeLit_erfuellbar : negativeLitJoint := by
  intro platform start
  let form := negativeLitForm []
  let s := (Maschine.I.start (form.einheit platform 1) start).2
  refine ⟨1, by omega, form.erfuellbar_aus_erreichbar platform start 1 s .start
    (form.realisiert (fun _ => rfl) platform 1 s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem neg_parse (ctx : Scope) : (negForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.neg_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem neg_elaboriert (ctx : Scope) : (negForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem neg_realisiert (ctx : Scope) : (negForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (negForm ctx).realisiert (fun args => by
    change ((expr 0 args.operand).code ++ [Befehl.negieren 0])[(expr 0 args.operand).code.length]? =
      some (.negieren 0)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem neg_annahme (ctx : Scope) : (negForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (negForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem neg_ideal (ctx : Scope) : (negForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args.operand).code ++ [Befehl.negieren 0])[(expr 0 args.operand).code.length]? =
      some (.negieren 0)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · exact ⟨((negForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem neg_einheit (ctx : Scope) : (negForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((negForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem neg_impl (ctx : Scope) : (negForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem neg_erhaltung (ctx : Scope) : (negForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (negForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.neg ctx).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem neg_erfuellbar : negJoint := by
  intro platform start
  let form := negForm []
  let args : Surface.NegArgs [] := ⟨.lit 1⟩
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (fun args => by
      change ((expr 0 args.operand).code ++ [Befehl.negieren 0])[(expr 0 args.operand).code.length]? =
        some (.negieren 0)
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl) platform args s₁ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem notValue_parse (ctx : Scope) : (notValueForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.notValue_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem notValue_elaboriert (ctx : Scope) : (notValueForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem notValue_realisiert (ctx : Scope) : (notValueForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (notValueForm ctx).realisiert (fun args => by
    change ((expr 0 args).code ++ [Befehl.verneinen 0])[(expr 0 args).code.length]? =
      some (.verneinen 0)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem notValue_annahme (ctx : Scope) : (notValueForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (notValueForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem notValue_ideal (ctx : Scope) : (notValueForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args).code ++ [Befehl.verneinen 0])[(expr 0 args).code.length]? =
      some (.verneinen 0)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · exact ⟨((notValueForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem notValue_einheit (ctx : Scope) : (notValueForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((notValueForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem notValue_impl (ctx : Scope) : (notValueForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem notValue_erhaltung (ctx : Scope) : (notValueForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (notValueForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.notValue ctx).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem notValue_erfuellbar : notValueJoint := by
  intro platform start
  let form := notValueForm []
  let args : Expr [] .bool := .trueLit
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (fun args => by
      change ((expr 0 args).code ++ [Befehl.verneinen 0])[(expr 0 args).code.length]? =
        some (.verneinen 0)
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl) platform args s₁ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
