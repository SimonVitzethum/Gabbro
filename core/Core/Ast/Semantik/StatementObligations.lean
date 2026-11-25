module

public import Core.Ast.Semantik.Formbeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem assignVar_parse (ctx : StatementContext) : (assignVarForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.assignVar_entry args ctx.2).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem assignVar_elaboriert (ctx : StatementContext) : (assignVarForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem assignVar_realisiert (ctx : StatementContext) : (assignVarForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (assignVarForm ctx).realisiert (fun args => by
    change ((expr 0 args.value).code ++ [Befehl.zuweisen 0 args.ref.index args.ref.binding.type])[
      (expr 0 args.value).code.length]? = some (.zuweisen 0 args.ref.index args.ref.binding.type)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem assignVar_annahme (ctx : StatementContext) : (assignVarForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (assignVarForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem assignVar_ideal (ctx : StatementContext) : (assignVarForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args.value).code ++ [Befehl.zuweisen 0 args.ref.index args.ref.binding.type])[
      (expr 0 args.value).code.length]? = some (.zuweisen 0 args.ref.index args.ref.binding.type)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · exact ⟨(assignVarForm ctx).bestimmt args, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem assignVar_einheit (ctx : StatementContext) : (assignVarForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((assignVarForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem assignVar_impl (ctx : StatementContext) : (assignVarForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem assignVar_erhaltung (ctx : StatementContext) : (assignVarForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (assignVarForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.assignVar ctx.1 ctx.2).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem assignVar_erfuellbar : assignVarJoint := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl,
      Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  let scope : Scope := [⟨name, .int 0 1, true, false⟩]
  let ref : Local scope (.int 0 1) := .here
  let args : Surface.AssignArgs scope := ⟨ref, ⟨trivial, trivial⟩, rfl, .lit 0, ⟨by omega, by omega⟩⟩
  let form := assignVarForm (scope, none)
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
  refine ⟨scope, args, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (fun args => by
      change ((expr 0 args.value).code ++ [Befehl.zuweisen 0 args.ref.index args.ref.binding.type])[
        (expr 0 args.value).code.length]? = some (.zuweisen 0 args.ref.index args.ref.binding.type)
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl) platform args s₁ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem returnValue_parse (ctx : ReturnContext) : (returnValueForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.returnValue_entry args).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem returnValue_elaboriert (ctx : ReturnContext) : (returnValueForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem returnValue_realisiert (ctx : ReturnContext) : (returnValueForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (returnValueForm ctx).realisiert (fun args => by
    change ((expr 0 args.value).code ++ [Befehl.zurueck 0 ctx.2])[
      (expr 0 args.value).code.length]? = some (.zurueck 0 ctx.2)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem returnValue_annahme (ctx : ReturnContext) : (returnValueForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (returnValueForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem returnValue_ideal (ctx : ReturnContext) : (returnValueForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((expr 0 args.value).code ++ [Befehl.zurueck 0 ctx.2])[
      (expr 0 args.value).code.length]? = some (.zurueck 0 ctx.2)
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · exact ⟨(returnValueForm ctx).bestimmt args, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem returnValue_einheit (ctx : ReturnContext) : (returnValueForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((returnValueForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem returnValue_impl (ctx : ReturnContext) : (returnValueForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem returnValue_erhaltung (ctx : ReturnContext) : (returnValueForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (returnValueForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.returnValue ctx.1 ctx.2).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem returnValue_erfuellbar : returnValueJoint := by
  intro platform start
  let expected : Ty .value := .int 0 1
  let args : Surface.ReturnArgs [] expected := ⟨.lit 0, ⟨by omega, by omega⟩⟩
  let form := returnValueForm ([], expected)
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.literal 0 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
  refine ⟨expected, args, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (fun args => by
      change ((expr 0 args.value).code ++ [Befehl.zurueck 0 expected])[
        (expr 0 args.value).code.length]? = some (.zurueck 0 expected)
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl) platform args s₁ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem ifElse_parse (ctx : StatementContext) : (ifElseForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.ifElse_entry ctx.1 ctx.2).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem ifElse_elaboriert (ctx : StatementContext) : (ifElseForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem ifElse_realisiert (ctx : StatementContext) : (ifElseForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (ifElseForm ctx).realisiert (fun args => by
    have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
        ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length]? = some sw := by
      intro cond yes no sw spr
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
          Nat.lt_succ_self])]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
      (bracedBlock args.no).code
      (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
      (Befehl.springe ((bracedBlock args.no).code.length + 1))) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem ifElse_annahme (ctx : StatementContext) : (ifElseForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (ifElseForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem ifElse_ideal (ctx : StatementContext) : (ifElseForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
        ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length]? = some sw := by
      intro cond yes no sw spr
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
          Nat.lt_succ_self])]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
      (bracedBlock args.no).code
      (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
      (Befehl.springe ((bracedBlock args.no).code.length + 1))
  · exact ⟨(ifElseForm ctx).bestimmt args, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem ifElse_einheit (ctx : StatementContext) : (ifElseForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((ifElseForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem ifElse_impl (ctx : StatementContext) : (ifElseForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem ifElse_erhaltung (ctx : StatementContext) : (ifElseForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (ifElseForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.ifElse ctx.1 ctx.2).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem ifElse_erfuellbar : ifElseJoint := by
  intro platform start bit
  let form := ifElseForm ([], none)
  cases bit
  · let args : Surface.IfArgs [] none := ⟨.falseLit, .braces .done, .braces .done⟩
    let E := form.einheit platform args
    let s₀ := (Maschine.I.start E start).2
    let s₁ := (Befehl.wahrheitswert 0 false).nach eintritt s₀
    have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
      ⟨.wahrheitswert 0 false, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
    refine ⟨args, rfl, form.erfuellbar_aus_erreichbar platform start args s₁ reached
      (form.realisiert (fun args => by
        have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
            ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length]? = some sw := by
          intro cond yes no sw spr
          rw [List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
            omega)]
          rw [List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
            omega)]
          rw [List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
              Nat.lt_succ_self])]
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
          (bracedBlock args.no).code
          (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
          (Befehl.springe ((bracedBlock args.no).code.length + 1))) platform args s₁ rfl rfl rfl rfl) ?_⟩
    intro g guard
    cases guard
  · let args : Surface.IfArgs [] none := ⟨.trueLit, .braces .done, .braces .done⟩
    let E := form.einheit platform args
    let s₀ := (Maschine.I.start E start).2
    let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
    have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
      ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
    have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start first
    refine ⟨args, rfl, form.erfuellbar_aus_erreichbar platform start args s₁ reached
      (form.realisiert (fun args => by
        have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
            ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length]? = some sw := by
          intro cond yes no sw spr
          rw [List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
            omega)]
          rw [List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
            omega)]
          rw [List.getElem?_append_left (by
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
              Nat.lt_succ_self])]
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
          (bracedBlock args.no).code
          (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
          (Befehl.springe ((bracedBlock args.no).code.length + 1))) platform args s₁ rfl rfl rfl rfl) ?_⟩
    intro g guard
    cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem braced_parse (ctx : StatementContext) : (bracedForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.braced_entry ctx.1 ctx.2).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem braced_elaboriert (ctx : StatementContext) : (bracedForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem braced_realisiert (ctx : StatementContext) : (bracedForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (bracedForm ctx).realisiert (fun args => by
    change ((block args.2).code ++ [Befehl.blockEnde (args.1.length - ctx.1.length)])[
      (block args.2).code.length]? = some (.blockEnde (args.1.length - ctx.1.length))
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem braced_annahme (ctx : StatementContext) : (bracedForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (bracedForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem braced_ideal (ctx : StatementContext) : (bracedForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    change ((block args.2).code ++ [Befehl.blockEnde (args.1.length - ctx.1.length)])[
      (block args.2).code.length]? = some (.blockEnde (args.1.length - ctx.1.length))
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · exact ⟨(bracedForm ctx).bestimmt args, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem braced_einheit (ctx : StatementContext) : (bracedForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((bracedForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem braced_impl (ctx : StatementContext) : (bracedForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem braced_erhaltung (ctx : StatementContext) : (bracedForm ctx).ErhaltungsAussage := by
  refine Quellform.erhaltung (bracedForm ctx) ?_
  intro args
  change (bracedBlock (.braces args.2)).klauseln.invariant = []
  exact bracedBlock_keine_invarianten (.braces args.2)

-- Mirror let_erfuellbar using the actual source head and its pre-state.
theorem braced_erfuellbar : bracedJoint := by
  intro platform start
  let args : Statements none [] := ⟨[], .done⟩
  let form := bracedForm ([], none)
  let s := (Maschine.I.start (form.einheit platform args) start).2
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s .start
    (form.realisiert (fun args => by
      change ((block args.2).code ++ [Befehl.blockEnde (args.1.length - ([], none).1.length)])[
        (block args.2).code.length]? = some (.blockEnde (args.1.length - ([], none).1.length))
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl) platform args s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

-- Mirror Rule.Entry.parse using the source production's reads lemma.
theorem thenJump_parse (ctx : StatementContext) : (thenJumpForm ctx).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.ifElse_entry ctx.1 ctx.2).parse lexed production

-- Mirror elab_korrekt with the descriptor's compositional fragment.
theorem thenJump_elaboriert (ctx : StatementContext) : (thenJumpForm ctx).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the new instruction's lookup.
theorem thenJump_realisiert (ctx : StatementContext) : (thenJumpForm ctx).RealisiertAussage := by
  intro platform args s running active atPc
  exact (thenJumpForm ctx).realisiert (fun args => by
    have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
        ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length + 1 + yes.length]? = some spr := by
      intro cond yes no sw spr
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.getElem?_append_right (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.length_append, List.length_append, List.length_cons, List.length_nil,
        Nat.add_zero, Nat.sub_self]
      rfl
    exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
      (bracedBlock args.no).code
      (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
      (Befehl.springe ((bracedBlock args.no).code.length + 1))) platform args s running active atPc

-- Mirror Quellform.annahme including the guard operands at the source head.
theorem thenJump_annahme (ctx : StatementContext) : (thenJumpForm ctx).AnnahmeAussage := by
  exact Quellform.annahme (thenJumpForm ctx)

-- Mirror binary_am_ort and Befehl.bestimmt with the named plan and successor.
theorem thenJump_ideal (ctx : StatementContext) : (thenJumpForm ctx).IdealAussage := by
  refine ⟨?_, fun args => ?_⟩
  · intro args
    have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
        ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length + 1 + yes.length]? = some spr := by
      intro cond yes no sw spr
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.getElem?_append_right (by
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
        omega)]
      rw [List.length_append, List.length_append, List.length_cons, List.length_nil,
        Nat.add_zero, Nat.sub_self]
      rfl
    exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
      (bracedBlock args.no).code
      (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
      (Befehl.springe ((bracedBlock args.no).code.length + 1))
  · exact ⟨(thenJumpForm ctx).bestimmt args, fun _ _ _ _ _ => Iff.rfl⟩

-- Mirror the unit field of Quellform.eintrag via Befehl.kommutation.
theorem thenJump_einheit (ctx : StatementContext) : (thenJumpForm ctx).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((thenJumpForm ctx).befehl args).kommutation⟩

-- Mirror the implementation field of Quellform.eintrag with the exact successor equation.
theorem thenJump_impl (ctx : StatementContext) : (thenJumpForm ctx).ImplAussage := by
  intro args c s w plans u
  rfl

-- Mirror Quellform.erhaltung with the frame-only instruction transfer.
theorem thenJump_erhaltung (ctx : StatementContext) : (thenJumpForm ctx).ErhaltungsAussage := by
  exact Quellform.erhaltung (thenJumpForm ctx)
    (fun args => stmt_keine_invarianten ((Surface.ifElse ctx.1 ctx.2).tree args).2)

-- Mirror binary_erfuellbar using the actual source head and its pre-state.
theorem thenJump_erfuellbar : thenJumpJoint := by
  intro platform start
  let form := thenJumpForm ([], none)
  let args : Surface.IfArgs [] none := ⟨.trueLit, .braces .done, .braces .done⟩
  let E := form.einheit platform args
  let s₀ := (Maschine.I.start E start).2
  let s₁ := (Befehl.wahrheitswert 0 true).nach eintritt s₀
  let s₂ := (Befehl.springeWenn 0 false 3).nach eintritt s₁
  let s₃ := (Befehl.blockEnde 0).nach eintritt s₂
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.wahrheitswert 0 true, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.springeWenn 0 false 3, rfl, rfl, rfl⟩
  have third : E.system.ISchritt eintritt s₂ () [plan] s₃ :=
    ⟨.blockEnde 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan]
      (.schritt eintritt () [plan] .start first) second) third
  refine ⟨args, rfl, form.erfuellbar_aus_erreichbar platform start args s₃ reached
    (form.realisiert (fun args => by
      have nested : ∀ (cond yes no : List Befehl) (sw spr : Befehl),
          ((((cond ++ [sw]) ++ yes) ++ [spr]) ++ no)[cond.length + 1 + yes.length]? = some spr := by
        intro cond yes no sw spr
        rw [List.getElem?_append_left (by
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
          omega)]
        rw [List.getElem?_append_right (by
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
          omega)]
        rw [List.length_append, List.length_append, List.length_cons, List.length_nil,
          Nat.add_zero, Nat.sub_self]
        rfl
      exact nested (expr 0 args.condition).code (bracedBlock args.yes).code
        (bracedBlock args.no).code
        (Befehl.springeWenn 0 false ((bracedBlock args.yes).code.length + 2))
        (Befehl.springe ((bracedBlock args.no).code.length + 1))) platform args s₃ rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
