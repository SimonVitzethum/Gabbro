module
public import Stage0.SourceWitness.Owners
import all Stage0.SourceWitness.Owners
import all Stage0.Compiler

@[expose] public section
namespace Gabbro.Stage0.ImagePhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

-- A certificate of the existing compiler's actual complete constructor, not
-- an alternative program. Header/Body contain every original production gate.
def compiled {text : String} (header : Header text) (body : Body header) :
    {result : Compiled text // compile text = .ok result} := by
  refine ⟨{
    source := header.source
    unit := header.unit
    main := body.main
    program := body.program
    expanded := header.expanded
    requirements := header.requirements
    gateMembers := uMembers (pre108 header.source.prepared.elaborierbar)
    gateExpansion := header.expansion
    elaborated := ?_
    entry := body.entry
    lowered := ⟨body.functions.program, List.finRange header.unit.fns.length,
      body.functions.lowered, body.restored⟩
    accepted := body.accepted
    arrayConstants := body.arrays.down
    initializerExports := body.initializers
    constantExports := header.constants
    gateChecked := Or.inr ⟨rfl, header.metadata⟩
    metadata := rfl }, ?_⟩
  · rw [header.elaborated]
    rfl
  · unfold compile
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
                      · rfl
        · rename_i error rejected
          cases rejected.symm.trans header.metadata

/-- Opaque exact-domain projections of the actual complete compile constructor. -/
theorem compiled_source {text : String} (header : Header text) (body : Body header) :
    (compiled header body).val.source = header.source := rfl

theorem compiled_unit {text : String} (header : Header text) (body : Body header) :
    (compiled header body).val.unit = header.unit := rfl

theorem compiled_main {text : String} (header : Header text) (body : Body header) :
    (compiled header body).val.main = body.main := rfl

/-- The restored program, not the pre-restoration function assembler. -/
theorem compiled_program {text : String} (header : Header text) (body : Body header) :
    (compiled header body).val.program = body.program := rfl

end Gabbro.Stage0.ImagePhases
