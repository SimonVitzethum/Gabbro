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
  sorry

-- Mirror elab_korrekt using the compositional fragment.
theorem returnVoid_elaboriert (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ElaboriertAussage := by
  sorry

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem returnVoid_realisiert (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).RealisiertAussage := by
  sorry

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem returnVoid_annahme (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).AnnahmeAussage := by
  sorry

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem returnVoid_ideal (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).IdealAussage := by
  sorry

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem returnVoid_einheit (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).EinheitAussage := by
  sorry

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem returnVoid_impl (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ImplAussage := by
  sorry

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem returnVoid_erhaltung (scope : Scope) (result : Option (Ty .value)) : (returnVoidForm scope result).ErhaltungsAussage := by
  sorry

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem returnVoid_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((returnVoidForm scope result).fragment a).sicherheitsEinheit platform)
      ((returnVoidForm scope result).befehl a) := by
  sorry

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem returnVoid_erfuellbar : returnVoidJoint := by
  sorry

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
  sorry

-- Mirror elab_korrekt using the compositional fragment.
theorem mutableLocal_elaboriert (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ElaboriertAussage := by
  sorry

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem mutableLocal_realisiert (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).RealisiertAussage := by
  sorry

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem mutableLocal_annahme (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).AnnahmeAussage := by
  sorry

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem mutableLocal_ideal (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).IdealAussage := by
  sorry

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem mutableLocal_einheit (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).EinheitAussage := by
  sorry

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem mutableLocal_impl (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ImplAussage := by
  sorry

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem mutableLocal_erhaltung (scope : Scope) (result : Option (Ty .value)) : (mutableLocalForm scope result).ErhaltungsAussage := by
  sorry

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem mutableLocal_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((mutableLocalForm scope result).fragment a).sicherheitsEinheit platform)
      ((mutableLocalForm scope result).befehl a) := by
  sorry

-- Mirror binary_erfuellbar at the actual instruction and reachable pre-state.
theorem mutableLocal_erfuellbar : mutableLocalJoint := by
  sorry

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
  sorry

-- Mirror elab_korrekt using the compositional fragment.
theorem directCall_elaboriert (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ElaboriertAussage := by
  sorry

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem directCall_realisiert (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).RealisiertAussage := by
  sorry

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem directCall_annahme (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).AnnahmeAussage := by
  sorry

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem directCall_ideal (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).IdealAussage := by
  sorry

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem directCall_einheit (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).EinheitAussage := by
  sorry

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem directCall_impl (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ImplAussage := by
  sorry

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem directCall_erhaltung (scope : Scope) (result : Option (Ty .value)) : (directCallForm scope result).ErhaltungsAussage := by
  sorry

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem directCall_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((directCallForm scope result).fragment a).sicherheitsEinheit platform)
      ((directCallForm scope result).befehl a) := by
  sorry

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
  sorry

-- Mirror elab_korrekt using the compositional fragment.
theorem bindDirect_elaboriert (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ElaboriertAussage := by
  sorry

-- Mirror Quellform.realisiert using the concrete instruction position.
theorem bindDirect_realisiert (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).RealisiertAussage := by
  sorry

-- Mirror Quellform.annahme at the source head with the exact operands.
theorem bindDirect_annahme (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).AnnahmeAussage := by
  sorry

-- Mirror binary_am_ort and Befehl.bestimmt for the new instruction.
theorem bindDirect_ideal (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).IdealAussage := by
  sorry

-- Mirror Befehl.kommutation with one linearisation point and zero private steps.
theorem bindDirect_einheit (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).EinheitAussage := by
  sorry

-- Mirror Quellform.ImplAussage with the explicit transfer and its plan.
theorem bindDirect_impl (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ImplAussage := by
  sorry

-- Mirror Quellform.erhaltung with the instruction-local transfer and safety.
theorem bindDirect_erhaltung (scope : Scope) (result : Option (Ty .value)) : (bindDirectForm scope result).ErhaltungsAussage := by
  sorry

-- Mirror Befehl.sicher to discharge the six SchrittSicherheit fields at every concrete cut.
theorem bindDirect_sicher (scope : Scope) (result : Option (Ty .value)) platform a :
    Sicherheit.RegelSicher (((bindDirectForm scope result).fragment a).sicherheitsEinheit platform)
      ((bindDirectForm scope result).befehl a) := by
  sorry

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
