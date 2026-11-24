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
  · exact ⟨((assignVarForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

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
  let scope : Scope := [⟨name, .int 0 1, true⟩]
  let ref : Local scope (.int 0 1) := .here
  let args : Surface.AssignArgs scope := ⟨ref, trivial, rfl, .lit 0, ⟨by omega, by omega⟩⟩
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
      rfl) platform args s₁ rfl rfl rfl) ?_⟩
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
  · exact ⟨((returnValueForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

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
      rfl) platform args s₁ rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
