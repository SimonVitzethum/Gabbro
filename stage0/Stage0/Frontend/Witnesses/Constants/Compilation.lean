module
public import Stage0.Frontend.Witnesses.Constants.Basis
public import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Actual function-level results, kept together before the assembler projects their fields. -/
structure Functions (unit : UProg) where
  values : (f : Fin unit.fns.length) → EnsTy unit f × RumpTy unit f × ReqTy unit f
  equations : ∀ f, lowerFnAt unit f = .ok (values f)
  noInvariants : unit.invs = []
  noMeasures : ∀ f, (fnAt unit f).decreases = none
  contracts : contractGate unit = true

def Functions.program {unit : UProg} (functions : Functions unit) : Programm (declOf unit) :=
  progOfFn unit (fun f => (functions.values f).1)
    (fun f => (functions.values f).2.1) (fun f => (functions.values f).2.2)
    (fun i => by
      have bound := i.isLt
      have empty : unit.invs.length = 0 := congrArg List.length functions.noInvariants
      omega)
    (ptrVertragOf unit)
    (fun a => axVertragOf unit a (Bool.and_eq_true_iff.mp functions.contracts).2)

/-- The production assembler returns exactly the certified function results, not a second program. -/
theorem Functions.lowered {unit : UProg} (functions : Functions unit) :
    lowerAllg unit = .ok (functions.program, List.finRange unit.fns.length) := by
  obtain ⟨raw, fs, success⟩ := ConstPhases.lowered functions.noInvariants
    (fun f => ⟨by rw [functions.equations f]; rfl, functions.noMeasures f⟩) functions.contracts
  have same : raw = functions.program ∧ fs = List.finRange unit.fns.length := by
    unfold lowerAllg at success
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · obtain ⟨programEq, enumeration⟩ := Measures.checkedProgram_eq success
          refine ⟨programEq.trans ?_, enumeration⟩
          unfold Functions.program
          congr 1
          · funext f
            exact congrArg Prod.fst (lowerAtPair_of_ok unit f _ (functions.equations f))
          · funext f
            exact congrArg (fun value => value.2.1)
              (lowerAtPair_of_ok unit f _ (functions.equations f))
          · funext f
            exact congrArg (fun value => value.2.2)
              (lowerAtPair_of_ok unit f _ (functions.equations f))
          · funext i
            have bound := i.isLt
            have empty : unit.invs.length = 0 := congrArg List.length functions.noInvariants
            omega
        · cases success
  rw [same.1, same.2] at success
  exact success

/-- The source phases and the selected original metadata side of this concrete witness family. -/
structure Header (text : String) where
  source : Frontend.Source text
  sourceEq : Frontend.source text = .ok source
  expanded : List SItemTief
  requirements : List (STyp × String)
  expansion : Modules.prepare (pre108 source.prepared.elaborierbar) = .ok (expanded, requirements)
  constants : Konst.checkSourceConstants (uMembers (pre108 source.prepared.elaborierbar)) = .ok ()
  ordinary : (uMembers (pre108 source.prepared.elaborierbar)).any Frontend.expansionHeader = false
  metadata : Konst.checkSourceMetadata (uMembers (pre108 source.prepared.elaborierbar)) = .ok ()
  candidate : UProg
  elaborated : ((Frontend.elabWithScopes (pre108 source.prepared.elaborierbar)
    source.scopes.values source.scopes.types source.scopes.functions
    (Frontend.tableWithEmpty source.scopes.values source.scopes.types)).bind
      (Profil.selectUnit {})) = .ok candidate

def Header.unit {text : String} (header : Header text) : UProg :=
  { header.candidate with exportGate :=
      Konst.checkSourceMetadata (uMembers (pre108 header.source.prepared.elaborierbar)) }

/-- Every remaining phase is an equation of the existing compiler, including all final gates. -/
structure Body {text : String} (header : Header text) where
  functions : Functions header.unit
  main : (declOf header.unit).Fn
  entry : fnIdx header.unit.fns (Profil.entryName {}) = .ok main
  initializers : Frontend.checkInitializers
    (uMembers (pre108 header.source.prepared.elaborierbar)) header.unit = .ok ()
  arrays : PLift (∀ item ∈ uMembers (pre108 header.source.prepared.elaborierbar),
    Frontend.ArrayMeaning header.unit header.source.scopes item)
  arrayEq : Frontend.checkArrays header.unit header.source.scopes
    (uMembers (pre108 header.source.prepared.elaborierbar)) = .ok arrays
  program : Programm (declOf header.unit)
  restored : OldSource.restore (pre108 header.source.prepared.elaborierbar)
    header.unit functions.program = .ok program
  accepted : OldSource.accepts header.unit program = .ok true

/-- Replay the canonical compiler with the complete typed packets before taking any projection. -/
theorem compiled {text : String} (header : Header text) (body : Body header) :
    ∃ result : Compiled text, compile text = .ok result ∧ result.unit = header.unit := by
  unfold compile
  rw [header.sourceEq]
  dsimp only [bind, Except.bind]
  -- Select the dependent source gates while preserving the proofs passed to compileChecked.
  split
  · rename_i error rejected
    cases rejected.symm.trans header.constants
  · split
    · rename_i error rejected
      cases rejected.symm.trans header.expansion
    · rename_i expanded requirements prepared
      have same : (expanded, requirements) = (header.expanded, header.requirements) :=
        Except.ok.inj (prepared.symm.trans header.expansion)
      have expandedEq := congrArg Prod.fst same
      have requirementsEq := congrArg Prod.snd same
      dsimp only at expandedEq requirementsEq
      subst expanded
      subst requirements
      simp only [header.ordinary, Bool.false_eq_true, ↓reduceIte]
      split
      · unfold compileChecked
        dsimp only
        split
        · rename_i error rejected
          cases rejected.symm.trans header.elaborated
        · rename_i candidate selected
          have same : candidate = header.candidate :=
            Except.ok.inj (selected.symm.trans header.elaborated)
          subst candidate
          -- Normalize the same complete unit in each certificate before any indexed dispatch.
          have initializers := body.initializers
          have arrays := body.arrayEq
          have entry := body.entry
          have lowered := body.functions.lowered
          have restored := body.restored
          have accepted := body.accepted
          dsimp only [Header.unit] at initializers arrays entry lowered restored accepted
          dsimp only
          split
          · rename_i error rejected
            cases rejected.symm.trans initializers
          · dsimp only [bind, Except.bind]
            split
            · rename_i error rejected
              cases rejected.symm.trans arrays
            · rename_i actualArrays selected
              have same : actualArrays = body.arrays :=
                Except.ok.inj (selected.symm.trans arrays)
              subst actualArrays
              split
              · rename_i error rejected
                cases rejected.symm.trans entry
              · rename_i actualMain selected
                have same : actualMain = body.main :=
                  Except.ok.inj (selected.symm.trans entry)
                subst actualMain
                split
                · rename_i error rejected
                  cases rejected.symm.trans lowered
                · rename_i raw fs selected
                  -- Inject the entire assembly result before entering the restoration continuation.
                  have same : (raw, fs) =
                      (body.functions.program, List.finRange header.unit.fns.length) :=
                    Except.ok.inj (selected.symm.trans lowered)
                  have rawEq := congrArg Prod.fst same
                  have enumerationEq := congrArg Prod.snd same
                  dsimp only at rawEq enumerationEq
                  subst raw
                  subst fs
                  split
                  · rename_i error rejected
                    cases rejected.symm.trans restored
                  · rename_i program selected
                    have same : program = body.program :=
                      Except.ok.inj (selected.symm.trans restored)
                    subst program
                    split
                    · rename_i error rejected
                      cases rejected.symm.trans accepted
                    · rename_i rejected
                      have impossible : (false : Bool) = true :=
                        Except.ok.inj (rejected.symm.trans accepted)
                      cases impossible
                    · exact ⟨_, rfl, rfl⟩
      · rename_i error rejected
        cases rejected.symm.trans header.metadata

end Gabbro.Stage0.Frontend.ConstPhases
