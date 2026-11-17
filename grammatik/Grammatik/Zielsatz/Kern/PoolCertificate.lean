module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Logik.Invarianten.Pruefer.Program
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

/-- Shared source metadata for the probe, pool and linked library fixtures. -/
def zPoolSources : Invarianten.Pruefer.LockSources zS := fun _ => some
  { resources := [], expression := .tru, correct := fun _ => rfl }

namespace PoolCertificate

local instance : DecidableEq zD.Ax := inferInstanceAs (DecidableEq Empty)
open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness Invarianten.Pruefer

abbrev scalar := Ty.int 0 100
abbrev context := zD.params zLies
abbrev slotExpr : Expr zD context zL scalar := .slot () () zIdx zDarf

def body : Endblock zD (vertragVon zD zLies) false context zL :=
  .bind slotExpr (.ret (.val (.var .here)) (List.Perm.refl _))

theorem body_eq : zPB.rumpf zLies = body := rfl

abbrev Bodies := (f : zD.Fn) → Endblock zD (vertragVon zD f) false
  (zD.params f) (Signatur.anfang zD (zD.signatur f))

def withBodies (bodies : Bodies) : Programm zD := { zPB with rumpf := bodies }

open Invarianten.Frag.Symbolic Vertraege.Pruefer.Symbolic

abbrev symbols : SymEnv zD Nat context := .nil

theorem symbols_bounded : symbols.Bounded 0 := trivial

def invariantsFor (bodies : Bodies) : InvariantFormula (withBodies bodies) (zD.invs.filter (schuldet zLies)) :=
  (invariantFormula (withBodies bodies) []).toOption.get (by rfl)

def compiled (bodies : Bodies) (sources : LockSources zS) :=
  ending (requiresPolicy (withBodies bodies) (entryContext symbols symbols_bounded))
    (lockFormula zS sources) {} none 128 body symbols symbols_bounded
    (contractGoals (withBodies bodies) zLies symbols symbols_bounded (invariantsFor bodies))

theorem compiled_present (bodies : Bodies) (sources : LockSources zS) :
    (compiled bodies sources).toOption.isSome = true := by with_unfolding_all rfl

def certificate (bodies : Bodies) (sources : LockSources zS) :=
  (compiled bodies sources).toOption.get (compiled_present bodies sources)

theorem compiled_result (bodies : Bodies) (sources : LockSources zS) :
    compiled bodies sources = .ok (certificate bodies sources) := by with_unfolding_all rfl

/-- One universally quantified slot snapshot suffices for the actual binder. -/
theorem compiled_valid (bodies : Bodies) (sources : LockSources zS)
    (values : Assignment (Key zD Nat)) : (certificate bodies sources).formula.denote values := by
  with_unfolding_all
    change ∀ value : Int, ((0 ≤ value ∧ value ≤ 100) ∧ value = values (.inl (.slot () () 0))) →
      (value = values (.inl (.slot () () 0)) ∧ True)
    exact fun _ guarded => ⟨guarded.2, trivial⟩

/-- The original nonconstant reader keeps its checked post for arbitrary
    unrelated bodies and the actual atomic replay certificate. -/
theorem reader_checked_for (bodies : Bodies) (same : bodies zLies = body)
    (sources : LockSources zS)
    (replay : (Invarianten.Pruefer.atomicReplay? (withBodies bodies) zLies).isSome = true) :
    (checkFunction (withBodies bodies) zS sources {} none zLies).toOption.isSome = true := by
  with_unfolding_all
    apply function_success (withBodies bodies) zS sources {} none zLies
    · rfl
    · exact replay
    · apply execution_success (withBodies bodies) zS sources {} none zLies (by rfl)
        (invariantsFor bodies) (by rfl)
        ((parameters (D := zD) 128 0 context).toOption.get (by with_unfolding_all rfl)) (by with_unfolding_all rfl)
      · change argumentSpecializations 16384 context *
          endSpecializations (withBodies bodies) false 128 16384 (bodies zLies) ≤ 16384
        rw [same]
        change 1 ≤ 16384
        decide
      · intro entry
        rcases entry with ⟨selected, member⟩
        cases selected
        have entryBounded : symbols.Bounded 0 := trivial
        let requirement := (Invarianten.Frag.Symbolic.translate ((withBodies bodies).requires zLies) symbols).toOption.get (by rfl)
        have ready : ∃ pre : Symbolic.EndCondition (S := zS)
            (requiresPolicy (withBodies bodies) (entryContext symbols symbols_bounded)).semantic
            (bodies zLies) symbols (contractGoals (withBodies bodies) zLies symbols symbols_bounded (invariantsFor bodies)),
            ending (requiresPolicy (withBodies bodies) _) (lockFormula zS sources) {} none 128
              (bodies zLies) symbols symbols_bounded
              (contractGoals (withBodies bodies) zLies symbols symbols_bounded (invariantsFor bodies)) = .ok pre ∧
              ∀ values, pre.formula.denote values := by
          rw [same]
          exact ⟨certificate bodies sources, compiled_result bodies sources, compiled_valid bodies sources⟩
        obtain ⟨pre, hbody, valid⟩ := ready
        apply environment_success (withBodies bodies) zS symbols symbols_bounded (requiresPolicy (withBodies bodies) _)
          sources {} none (invariantsFor bodies) (by rfl) requirement (by rfl) pre hbody
        apply (close_decide_true_iff _).mpr
        intro values
        apply (lower_denote _ values).mpr
        intro _ _ _
        exact valid values

theorem reader_checked (sources : LockSources zS) :
    (checkFunction zPB zS sources {} none zLies).toOption.isSome = true :=
  reader_checked_for zPB.rumpf body_eq sources (by decide +kernel)

/-- Full function enumeration retains the strict gate; only the reader's
    kernel proof uses the symbolic certificate above. -/
theorem contracts_checked : KontrakteGeprueftB zPB zS zFs zPoolSources = true := by
  apply contracts_success zPB zS zPoolSources {} zFs
  intro f
  cases f with
  | ein => decide +kernel
  | lies => exact reader_checked zPoolSources
  | wrap => decide +kernel
  | haupt => decide +kernel

#print axioms contracts_checked

/-- Both existing VC gates accept; no invariant or contract duty is skipped. -/
theorem vc_checked : Invarianten.Pruefer.invariantVCB zPB zS zFs zPoolSources {}
    (fun _ => none) [()] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, contracts_checked⟩

#print axioms vc_checked

end PoolCertificate

end Gabbro.Grammatik.Zielsatz
