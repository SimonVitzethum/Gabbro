module

public import Core.Ast.Semantik.ProgramForms

/-
M6 batch 2 prover checklist

These definitions describe the ordinary scalar program fragment from SYNTAX §1, §2, §6–§8.
Leave constructor order, source spellings and transfer equations fixed in the proof handoff.

  Syntax — ProgramHeader: SignedReads, TypeReads, ParamsRead, ArgsRead and CallReads,
    ProgramSurface: each _print, _reads, _syntax_erfuellbar and _entry,
    Declaration: both inversions, suffix, determinism and printer derivation.
  Semantics — For each form below: _parse, _elaboriert, _realisiert, _annahme,
    _ideal, _einheit, _impl, _erhaltung, _sicher and _erfuellbar.
    The safety statements expose all fields of SchrittSicherheit through RegelSicher.
  Control — ProgramProgress fixes one step per instruction, caller restoration,
    recursive entry measures, and the static while and for pass budgets.

  Stmt.retVoid — SYNTAX §6, explicit void return
  Stmt.letMutable — SYNTAX §7, scalar mutable local
  Stmt.directCall — syntax.call and surface.SAnw.call
  Stmt.bindDirect — SYNTAX §7, typed result binding
  Stmt.whileBounded — syntax.whileloop and surface.SBoundedHeader.whileLoop
  Stmt.forRange — SYNTAX §8 and surface.SBoundedHeader.forRange
  Decl.constant — syntax.constdecl and surface.SItemTief.constT
  Decl.function — syntax.fndecl and surface.SItemTief.fnT
  UnitBody.step — syntax.program, ordinary entry selected as main
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem returnVoid_parse (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.returnVoid_entry scope result args.declared).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem returnVoid_elaboriert (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem returnVoid_realisiert (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  let form := returnVoidForm scope result
  have head : kopf (form.fragment args).code s eintritt = some (form.befehl args) := by
    simp only [kopf, ite_true, running, active, live, atPc]
  exact ⟨atPc, head, ⟨_, head, rfl, rfl⟩, ⟨_, head, rfl, rfl⟩⟩

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem returnVoid_annahme (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((returnVoidForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (returnVoidForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((returnVoidForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem returnVoid_ideal (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).IdealAussage := by
  exact ⟨fun _ => rfl, fun args => ⟨((returnVoidForm scope result).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩⟩

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem returnVoid_einheit (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((returnVoidForm scope result).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem returnVoid_impl (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem returnVoid_erhaltung (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ErhaltungsAussage := by
  intro platform args
  exact ⟨((returnVoidForm scope result).befehl args).abgleich ((returnVoidForm scope result).fragment args) platform,
    ((returnVoidForm scope result).befehl args).fortschritt ((returnVoidForm scope result).fragment args),
    ((returnVoidForm scope result).befehl args).komponierbar ((returnVoidForm scope result).fragment args) platform,
    ((returnVoidForm scope result).befehl args).sicher ((returnVoidForm scope result).fragment args) platform rfl⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem returnVoid_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((returnVoidForm scope result).fragment a).sicherheitsEinheit platform)
      ((returnVoidForm scope result).befehl a) := by
  exact ((returnVoidForm scope result).befehl a).sicher ((returnVoidForm scope result).fragment a) platform rfl

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem returnVoid_erfuellbar : returnVoidJoint := by
  intro platform start
  let form := returnVoidForm [] none
  let a : Surface.ReturnVoidArgs [] none := ⟨rfl⟩
  let s := (I.start (form.einheit platform a) start).2
  refine ⟨a, Ast.print (form.produktion.tree a), s,
    Ast.parse_print (form.produktion.tree a), rfl, .start,
    form.realisiert (fun _ => rfl) platform a s rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def returnVoidProofs : RegistryEntry ``Stmt.retVoid
    ⟨.surface, Quellform.statements (Context := PUnit) (fun _ => returnVoidForm [] none) returnVoidJoint ``Stmt.retVoid⟩ where
  realization := .surface (fun _ => returnVoid_parse [] none) (fun _ => returnVoid_elaboriert [] none) (fun _ => returnVoid_realisiert [] none)
  acceptanceRule := fun _ => returnVoid_annahme [] none
  idealRule := fun _ => returnVoid_ideal [] none
  unitsAndCommutation := fun _ => returnVoid_einheit [] none
  implementationRule := fun _ => returnVoid_impl [] none
  preservation := fun _ => returnVoid_erhaltung [] none
  jointlySatisfiable := returnVoid_erfuellbar

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem mutableLocal_parse (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.mutableLocal_entry scope result).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem mutableLocal_elaboriert (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem mutableLocal_realisiert (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  let form := mutableLocalForm scope result
  have head : kopf (form.fragment args).code s eintritt = some (form.befehl args) := by
    simp only [kopf, ite_true, running, active, live, atPc]
    change ((expr 0 args.value).anhaengen (.einzel (.bindeWert 0 args.written.type false))).code[(expr 0 args.value).code.length]? = some (.bindeWert 0 args.written.type false)
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  exact ⟨atPc, head, ⟨_, head, rfl, rfl⟩, ⟨_, head, rfl, rfl⟩⟩

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem mutableLocal_annahme (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((mutableLocalForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (mutableLocalForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((mutableLocalForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem mutableLocal_ideal (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).IdealAussage := by
  constructor
  · intro args
    change ((expr 0 args.value).anhaengen (.einzel (.bindeWert 0 args.written.type false))).code[(expr 0 args.value).code.length]? = some (.bindeWert 0 args.written.type false)
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    constructor
    · exact ((mutableLocalForm scope result).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem mutableLocal_einheit (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((mutableLocalForm scope result).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem mutableLocal_impl (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem mutableLocal_erhaltung (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ErhaltungsAussage := by
  intro platform args
  exact ⟨((mutableLocalForm scope result).befehl args).abgleich ((mutableLocalForm scope result).fragment args) platform,
    ((mutableLocalForm scope result).befehl args).fortschritt ((mutableLocalForm scope result).fragment args),
    ((mutableLocalForm scope result).befehl args).komponierbar ((mutableLocalForm scope result).fragment args) platform,
    ((mutableLocalForm scope result).befehl args).sicher ((mutableLocalForm scope result).fragment args) platform (by
      change (stmt ((mutableLocalForm scope result).produktion.tree args).2).klauseln.invariant = []
      exact stmt_keine_invarianten _)⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem mutableLocal_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((mutableLocalForm scope result).fragment a).sicherheitsEinheit platform)
      ((mutableLocalForm scope result).befehl a) := by
  exact ((mutableLocalForm scope result).befehl a).sicher ((mutableLocalForm scope result).fragment a) platform (by
    change (stmt ((mutableLocalForm scope result).produktion.tree a).2).klauseln.invariant = []
    exact stmt_keine_invarianten _)

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem mutableLocal_erfuellbar : mutableLocalJoint := by
  intro platform start
  let ctx : StatementContext := ([], none)
  let form := mutableLocalForm ctx.1 ctx.2
  let name : Identifier := keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)
  have ordinaryName : ordinaryLocal name := by
    change ['x'] ≠ ['t', 'r', 'u', 'e'] ∧ ['x'] ≠ ['f', 'a', 'l', 's', 'e']
    constructor
    · intro h
      cases h
    · intro h
      cases h
  let a : Surface.MutableLocalArgs [] none := ⟨name, ordinaryName, .bool, trivial, .bool, Expr.trueLit, trivial⟩
  let s := (I.start (form.einheit platform a) start).2
  refine ⟨ctx, a, Ast.print (form.produktion.tree a), s,
    Ast.parse_print (form.produktion.tree a), rfl, .start,
    form.realisiert (fun args => by
      change ((expr 0 args.value).anhaengen (.einzel (.bindeWert 0 args.written.type false))).code
        [(expr 0 args.value).code.length]? = some (.bindeWert 0 args.written.type false)
      simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem?_cons_zero])
      platform a s rfl rfl rfl rfl, ?_⟩
  intro g guard
  cases guard

def mutableLocalProofs : RegistryEntry ``Stmt.letMutable
    ⟨.surface, Quellform.statements (Context := StatementContext) (fun ctx => mutableLocalForm ctx.1 ctx.2) mutableLocalJoint ``Stmt.letMutable⟩ where
  realization := .surface (fun ctx => mutableLocal_parse ctx.1 ctx.2) (fun ctx => mutableLocal_elaboriert ctx.1 ctx.2) (fun ctx => mutableLocal_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => mutableLocal_annahme ctx.1 ctx.2
  idealRule := fun ctx => mutableLocal_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => mutableLocal_einheit ctx.1 ctx.2
  implementationRule := fun ctx => mutableLocal_impl ctx.1 ctx.2
  preservation := fun ctx => mutableLocal_erhaltung ctx.1 ctx.2
  jointlySatisfiable := mutableLocal_erfuellbar

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem directCall_parse (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.directCall_entry scope result).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem directCall_elaboriert (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem directCall_realisiert (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  let form := directCallForm scope result
  have head : kopf (form.fragment args).code s eintritt = some (form.befehl args) := by
    simp only [kopf, ite_true, running, active, live, atPc]
    change ((argsCode 0 args.args).anhaengen (.einzel (callInstruction args none))).code[(argsCode 0 args.args).code.length]? = some (callInstruction args none)
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  exact ⟨atPc, head, ⟨_, head, rfl, rfl⟩, ⟨_, head, rfl, rfl⟩⟩

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem directCall_annahme (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((directCallForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (directCallForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((directCallForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem directCall_ideal (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).IdealAussage := by
  constructor
  · intro args
    change ((argsCode 0 args.args).anhaengen (.einzel (callInstruction args none))).code[(argsCode 0 args.args).code.length]? = some (callInstruction args none)
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    constructor
    · exact ((directCallForm scope result).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem directCall_einheit (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((directCallForm scope result).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem directCall_impl (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem directCall_erhaltung (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ErhaltungsAussage := by
  intro platform args
  exact ⟨((directCallForm scope result).befehl args).abgleich ((directCallForm scope result).fragment args) platform,
    ((directCallForm scope result).befehl args).fortschritt ((directCallForm scope result).fragment args),
    ((directCallForm scope result).befehl args).komponierbar ((directCallForm scope result).fragment args) platform,
    ((directCallForm scope result).befehl args).sicher ((directCallForm scope result).fragment args) platform (by
      change (stmt ((directCallForm scope result).produktion.tree args).2).klauseln.invariant = []
      exact stmt_keine_invarianten _)⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem directCall_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((directCallForm scope result).fragment a).sicherheitsEinheit platform)
      ((directCallForm scope result).befehl a) := by
  exact ((directCallForm scope result).befehl a).sicher ((directCallForm scope result).fragment a) platform (by
    change (stmt ((directCallForm scope result).produktion.tree a).2).klauseln.invariant = []
    exact stmt_keine_invarianten _)

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem directCall_erfuellbar : directCallJoint := by
  sorry

def directCallProofs : RegistryEntry ``Stmt.directCall
    ⟨.surface, Quellform.statements (Context := StatementContext) (fun ctx => directCallForm ctx.1 ctx.2) directCallJoint ``Stmt.directCall⟩ where
  realization := .surface (fun ctx => directCall_parse ctx.1 ctx.2) (fun ctx => directCall_elaboriert ctx.1 ctx.2) (fun ctx => directCall_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => directCall_annahme ctx.1 ctx.2
  idealRule := fun ctx => directCall_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => directCall_einheit ctx.1 ctx.2
  implementationRule := fun ctx => directCall_impl ctx.1 ctx.2
  preservation := fun ctx => directCall_erhaltung ctx.1 ctx.2
  jointlySatisfiable := directCall_erfuellbar

-- Mirror Rule.Entry.parse using the source production and lexical premises.
theorem bindDirect_parse (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ParseAussage := by
  intro args text pieces lexed production
  exact (Surface.bindDirect_entry scope result).parse lexed production

-- Mirror elab_korrekt using the compositional fragment.
theorem bindDirect_elaboriert (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ElaboriertAussage := by
  intro platform args
  rfl

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem bindDirect_realisiert (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).RealisiertAussage := by
  intro platform args s running active live atPc
  let form := bindDirectForm scope result
  have head : kopf (form.fragment args).code s eintritt = some (form.befehl args) := by
    simp only [kopf, ite_true, running, active, live, atPc]
    change ((argsCode 0 args.call.args).anhaengen (.einzel (callInstruction args.call (some args.written.type)))).code[(argsCode 0 args.call.args).code.length]? = some (callInstruction args.call (some args.written.type))
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  exact ⟨atPc, head, ⟨_, head, rfl, rfl⟩, ⟨_, head, rfl, rfl⟩⟩

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem bindDirect_annahme (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).AnnahmeAussage := by
  intro platform args
  refine ⟨((bindDirectForm scope result).befehl args).lokal _ rfl, ?_, ?_⟩
  · rintro s c ⟨op, operands⟩ head guard
    exact ⟨c, (bindDirectForm scope result).befehl args, head, guard⟩
  · intro t c s w stepPlan u spur next step execute ev
    obtain ⟨rfl, _⟩ := ((bindDirectForm scope result).befehl args).vollzug_genau (w := w) step execute
    exact List.not_mem_nil

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem bindDirect_ideal (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).IdealAussage := by
  constructor
  · intro args
    change ((argsCode 0 args.call.args).anhaengen (.einzel (callInstruction args.call (some args.written.type)))).code[(argsCode 0 args.call.args).code.length]? = some (callInstruction args.call (some args.written.type))
    simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
  · intro args
    constructor
    · exact ((bindDirectForm scope result).befehl args).bestimmt
    · intro c s w plans u
      exact Iff.rfl

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem bindDirect_einheit (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).EinheitAussage := by
  intro platform args
  exact ⟨rfl, ((bindDirectForm scope result).befehl args).kommutation⟩

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem bindDirect_impl (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ImplAussage := by
  intro args c s w plans u
  exact Iff.rfl

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem bindDirect_erhaltung (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ErhaltungsAussage := by
  intro platform args
  exact ⟨((bindDirectForm scope result).befehl args).abgleich ((bindDirectForm scope result).fragment args) platform,
    ((bindDirectForm scope result).befehl args).fortschritt ((bindDirectForm scope result).fragment args),
    ((bindDirectForm scope result).befehl args).komponierbar ((bindDirectForm scope result).fragment args) platform,
    ((bindDirectForm scope result).befehl args).sicher ((bindDirectForm scope result).fragment args) platform (by
      change (stmt ((bindDirectForm scope result).produktion.tree args).2).klauseln.invariant = []
      exact stmt_keine_invarianten _)⟩

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem bindDirect_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((bindDirectForm scope result).fragment a).sicherheitsEinheit platform)
      ((bindDirectForm scope result).befehl a) := by
  exact ((bindDirectForm scope result).befehl a).sicher ((bindDirectForm scope result).fragment a) platform (by
    change (stmt ((bindDirectForm scope result).produktion.tree a).2).klauseln.invariant = []
    exact stmt_keine_invarianten _)

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem bindDirect_erfuellbar : bindDirectJoint := by
  sorry

def bindDirectProofs : RegistryEntry ``Stmt.bindDirect
    ⟨.surface, Quellform.statements (Context := StatementContext) (fun ctx => bindDirectForm ctx.1 ctx.2) bindDirectJoint ``Stmt.bindDirect⟩ where
  realization := .surface (fun ctx => bindDirect_parse ctx.1 ctx.2) (fun ctx => bindDirect_elaboriert ctx.1 ctx.2) (fun ctx => bindDirect_realisiert ctx.1 ctx.2)
  acceptanceRule := fun ctx => bindDirect_annahme ctx.1 ctx.2
  idealRule := fun ctx => bindDirect_ideal ctx.1 ctx.2
  unitsAndCommutation := fun ctx => bindDirect_einheit ctx.1 ctx.2
  implementationRule := fun ctx => bindDirect_impl ctx.1 ctx.2
  preservation := fun ctx => bindDirect_erhaltung ctx.1 ctx.2
  jointlySatisfiable := bindDirect_erfuellbar

end Gabbro.Core.Ast.Semantik
