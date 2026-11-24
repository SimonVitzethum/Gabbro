module

public import Core.Ast.Semantik.Formbeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem subtraction_parse (ctx : Scope) : (subtractionForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.subtraction_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem subtraction_elaboriert (ctx : Scope) : (subtractionForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem subtraction_realisiert (ctx : Scope) : (subtractionForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (subtractionForm ctx).realisiert (fun args => by
    change ((expr 0 args.val.left).code ++ (expr 1 args.val.right).code ++
      [Befehl.binaer args.val.op 0])[(expr 0 args.val.left).code.length +
        (expr 1 args.val.right).code.length]? = some (.binaer .sub 0)
    rw [args.2]
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem subtraction_annahme (ctx : Scope) : (subtractionForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (subtractionForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem subtraction_ideal (ctx : Scope) : (subtractionForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args.val.left).code ++ (expr 1 args.val.right).code ++
      [Befehl.binaer args.val.op 0])[(expr 0 args.val.left).code.length +
        (expr 1 args.val.right).code.length]? = some (.binaer .sub 0)
    rw [args.2]
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl
  · exact ⟨((subtractionForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem subtraction_einheit (ctx : Scope) : (subtractionForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((subtractionForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem subtraction_impl (ctx : Scope) : (subtractionForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem subtraction_erhaltung (ctx : Scope) : (subtractionForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (subtractionForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.subtraction ctx).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem subtraction_erfuellbar : subtractionJoint := by
  intro platform start
  let form := subtractionForm []
  let args : Surface.SubtractArgs [] := ⟨⟨.sub, .lit 1, .lit 2⟩, rfl⟩
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 2).nach eintritt s₁
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 2, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₂ reached
    (form.realisiert (fun args => by
      change ((expr 0 args.val.left).code ++ (expr 1 args.val.right).code ++
        [Befehl.binaer args.val.op 0])[(expr 0 args.val.left).code.length +
          (expr 1 args.val.right).code.length]? = some (.binaer .sub 0)
      rw [args.2]
      rw [List.getElem?_append_right (by rw [List.length_append])]
      rw [List.length_append, Nat.sub_self]
      rfl) platform args s₂ rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem division_parse (ctx : Scope) : (divisionForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.division_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem division_elaboriert (ctx : Scope) : (divisionForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem division_realisiert (ctx : Scope) : (divisionForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (divisionForm ctx).realisiert (fun args => by
    change ((expr 0 args.left).code ++ (expr 1 args.right).code ++
      [Befehl.teilen 0])[(expr 0 args.left).code.length +
        (expr 1 args.right).code.length]? = some (.teilen 0)
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem division_annahme (ctx : Scope) : (divisionForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (divisionForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem division_ideal (ctx : Scope) : (divisionForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args.left).code ++ (expr 1 args.right).code ++
      [Befehl.teilen 0])[(expr 0 args.left).code.length +
        (expr 1 args.right).code.length]? = some (.teilen 0)
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl
  · exact ⟨((divisionForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem division_einheit (ctx : Scope) : (divisionForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((divisionForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem division_impl (ctx : Scope) : (divisionForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem division_erhaltung (ctx : Scope) : (divisionForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (divisionForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.division ctx).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem division_erfuellbar : divisionJoint := by
  intro platform start unsigned
  let form := divisionForm []
  let amOrt : (divisionForm []).RegelAmOrt := fun args => by
    change ((expr 0 args.left).code ++ (expr 1 args.right).code ++
      [Befehl.teilen 0])[(expr 0 args.left).code.length +
        (expr 1 args.right).code.length]? = some (.teilen 0)
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl
  by_cases h : unsigned = true
  · let args : Surface.DivisionArgs [] := ⟨.lit 1, .lit 2, Or.inl (by omega)⟩
    let E := form.einheit platform args
    let s₀ := (Maschine.I.start E start).2
    let s₁ := (Befehl.literal 0 1).nach eintritt s₀
    let s₂ := (Befehl.literal 1 2).nach eintritt s₁
    have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
    have second : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 2, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₂ :=
      .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
    refine ⟨args, ?_, form.erfuellbar_aus_erreichbar platform start args s₂ reached
      (form.realisiert amOrt platform args s₂ rfl rfl rfl) ?_⟩
    · subst unsigned
      change (0 ≤ (1 : Int) ∧ 1 ≤ (2 : Int)) ↔ true = true
      constructor
      · intro _
        rfl
      · intro _
        constructor <;> omega
    · intro g guard
      change (Befehl.teilen 0).guard (s₂.lokal eintritt) = some g at guard
      have htemp0 : (s₂.lokal eintritt).temp 0 = some ⟨.int 1 1, Zahl.literal 1⟩ := rfl
      have htemp1 : (s₂.lokal eintritt).temp (0 + 1) = some ⟨.int 2 2, Zahl.literal 2⟩ := rfl
      have hg : (Befehl.teilen 0).guard (s₂.lokal eintritt) = some ⟨.division, (1, 2)⟩ := by
        simp only [Befehl.guard, Rahmen.zahl, alsGanzzahl, htemp0, htemp1,
          Option.bind_eq_bind, Option.bind_some, Option.pure_def, Zahl.literal]
        rfl
      have eq : g = ⟨.division, (1, 2)⟩ := (Option.some.inj (hg.symm.trans guard)).symm
      subst g
      change (2 : Nat) ≠ 0
      omega
  · let args : Surface.DivisionArgs [] := ⟨.negativeLit 1, .lit 2, Or.inl (by omega)⟩
    let E := form.einheit platform args
    let s₀ := (Maschine.I.start E start).2
    let s₁ := (Befehl.negativ 0 1).nach eintritt s₀
    let s₂ := (Befehl.literal 1 2).nach eintritt s₁
    have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.negativ 0 1, rfl, rfl, rfl⟩
    have second : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 2, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₂ :=
      .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
    refine ⟨args, ?_, form.erfuellbar_aus_erreichbar platform start args s₂ reached
      (form.realisiert amOrt platform args s₂ rfl rfl rfl) ?_⟩
    · cases unsigned
      · change (0 ≤ (-(1 : Int)) ∧ 1 ≤ (2 : Int)) ↔ false = true
        constructor
        · intro both
          omega
        · intro impossible
          cases impossible
      · contradiction
    · intro g guard
      change (Befehl.teilen 0).guard (s₂.lokal eintritt) = some g at guard
      have htemp0 : (s₂.lokal eintritt).temp 0 = some ⟨.int (-1) (-1), Zahl.literal (-1)⟩ := rfl
      have htemp1 : (s₂.lokal eintritt).temp (0 + 1) = some ⟨.int 2 2, Zahl.literal 2⟩ := rfl
      have hg : (Befehl.teilen 0).guard (s₂.lokal eintritt) = some ⟨.division, (1, 2)⟩ := by
        simp only [Befehl.guard, Rahmen.zahl, alsGanzzahl, htemp0, htemp1,
          Option.bind_eq_bind, Option.bind_some, Option.pure_def, Zahl.literal]
        rfl
      have eq : g = ⟨.division, (1, 2)⟩ := (Option.some.inj (hg.symm.trans guard)).symm
      subst g
      change (2 : Nat) ≠ 0
      omega

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem comparison_parse (ctx : Scope) : (comparisonForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.comparison_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem comparison_elaboriert (ctx : Scope) : (comparisonForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem comparison_realisiert (ctx : Scope) : (comparisonForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (comparisonForm ctx).realisiert (fun args => by
    change ((expr 0 args.left).code ++ (expr 1 args.right).code ++
      [Befehl.vergleichen args.op 0])[(expr 0 args.left).code.length +
        (expr 1 args.right).code.length]? = some (.vergleichen args.op 0)
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem comparison_annahme (ctx : Scope) : (comparisonForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (comparisonForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem comparison_ideal (ctx : Scope) : (comparisonForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args.left).code ++ (expr 1 args.right).code ++
      [Befehl.vergleichen args.op 0])[(expr 0 args.left).code.length +
        (expr 1 args.right).code.length]? = some (.vergleichen args.op 0)
    rw [List.getElem?_append_right (by rw [List.length_append])]
    rw [List.length_append, Nat.sub_self]
    rfl
  · exact ⟨((comparisonForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem comparison_einheit (ctx : Scope) : (comparisonForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((comparisonForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem comparison_impl (ctx : Scope) : (comparisonForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem comparison_erhaltung (ctx : Scope) : (comparisonForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (comparisonForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.comparison ctx).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem comparison_erfuellbar : comparisonJoint := by
  intro platform start op
  let form := comparisonForm []
  let args : Surface.CompareArgs [] := ⟨op, .lit 1, .lit 2⟩
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 2).nach eintritt s₁
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 1, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 2, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
  refine ⟨args, rfl, form.erfuellbar_aus_erreichbar platform start args s₂ reached
    (form.realisiert (fun args => by
      change ((expr 0 args.left).code ++ (expr 1 args.right).code ++
        [Befehl.vergleichen args.op 0])[(expr 0 args.left).code.length +
          (expr 1 args.right).code.length]? = some (.vergleichen args.op 0)
      rw [List.getElem?_append_right (by rw [List.length_append])]
      rw [List.length_append, Nat.sub_self]
      rfl) platform args s₂ rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem logic_parse (ctx : Scope) : (logicForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.logic_entry ctx).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem logic_elaboriert (ctx : Scope) : (logicForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem logic_realisiert (ctx : Scope) : (logicForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (logicForm ctx).realisiert (fun args => by
    change ((((expr 0 args.left).code ++
      [Befehl.springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1)]) ++
        (expr 0 args.right).code)[(expr 0 args.left).code.length]?) =
      some (.springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1))
    rw [List.getElem?_append_left (by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        Nat.lt_succ_self])]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem logic_annahme (ctx : Scope) : (logicForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (logicForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem logic_ideal (ctx : Scope) : (logicForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((((expr 0 args.left).code ++
      [Befehl.springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1)]) ++
        (expr 0 args.right).code)[(expr 0 args.left).code.length]?) =
      some (.springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1))
    rw [List.getElem?_append_left (by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        Nat.lt_succ_self])]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · exact ⟨((logicForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem logic_einheit (ctx : Scope) : (logicForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((logicForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem logic_impl (ctx : Scope) : (logicForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem logic_erhaltung (ctx : Scope) : (logicForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (logicForm ctx)
    (fun args => expr_keine_invarianten 0 ((Surface.logic ctx).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem logic_erfuellbar : logicJoint := by
  intro platform start op bit
  let form := logicForm []
  let amOrt : (logicForm []).RegelAmOrt := fun args => by
    change ((((expr 0 args.left).code ++
      [Befehl.springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1)]) ++
        (expr 0 args.right).code)[(expr 0 args.left).code.length]?) =
      some (.springeWenn 0 args.op.skips ((expr 0 args.right).code.length + 1))
    rw [List.getElem?_append_left (by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
        Nat.lt_succ_self])]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  cases bit
  · let args : Surface.LogicArgs [] := ⟨op, .falseLit, .trueLit⟩
    let E := form.einheit platform args
    let s₀ := (Maschine.I.start E start).2
    let s₁ := (Befehl.wahrheitswert 0 false).nach eintritt s₀
    have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
      ⟨.wahrheitswert 0 false, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
    refine ⟨args, rfl, rfl, form.erfuellbar_aus_erreichbar platform start args s₁ reached
      (form.realisiert amOrt platform args s₁ rfl rfl rfl) ?_⟩
    intro g guard
    cases guard
  · let args : Surface.LogicArgs [] := ⟨op, .trueLit, .trueLit⟩
    let E := form.einheit platform args
    let s₀ := (Maschine.I.start E start).2
    let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
    have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
      ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
    refine ⟨args, rfl, rfl, form.erfuellbar_aus_erreichbar platform start args s₁ reached
      (form.realisiert amOrt platform args s₁ rfl rfl rfl) ?_⟩
    intro g guard
    cases guard

end Gabbro.Core.Ast.Semantik
