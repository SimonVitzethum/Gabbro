module

public import Grammatik.Logik.Invarianten.Pruefer.Locks
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil1Basis
public import Grammatik.Logik.Vertraege.Pruefer.Fixtures
import Lean.Elab.Tactic.Cbv

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.LockWitness

/-- A real lock identifier from the existing concurrent fixture. The source
    evidence states correspondence, not truth of arbitrary memory. -/
def sources : LockSources (SperrInv.leer mD) := fun _ => some
  { resources := []
    expression := .tru
    correct := fun _ => rfl }

theorem reified_zeuge :
    (lockFormula (SperrInv.leer mD) sources ()).toOption.isSome = true := by rfl

/-- Absence of syntax does not become a fabricated true predicate. -/
theorem opaque_zeuge :
    (lockFormula (SperrInv.leer mD) (fun _ => none) ()).toOption.isSome = false := by rfl

open Frag Zielsatz

/-- A single parameterless writer and one lock protecting a real scalar cell.
    Its invariant is not a constant predicate over arbitrary memories. -/
def declaration : Deklaration :=
  { Vertraege.Pruefer.Witness.declaration with
    Lock := Unit
    decLock := inferInstance
    rang := fun _ => 0
    maskiert := fun _ => false
    gbraucht := fun name => if name then [] else [.inl ()]
    sigNr := fun _ =>
      { params := [], erg := none, gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun name => !name
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible }

abbrev held : List (Res declaration) := [.held ()]
abbrev contract := vertragVon declaration ()

theorem cell_access : gdarf declaration false held := by
  intro resource member
  have same : resource = .inl () := List.mem_singleton.mp member
  subst resource
  exact List.mem_cons_self

def invariant : Expr declaration [] held .bool :=
  .eq (.glob false cell_access) (.lit 0)

def family : SperrInv declaration where
  orte := fun _ => [.inr false]
  inv := fun _ memory => decide ((memory.globs false).n = 0)

def cellSources : LockSources family := fun _ => some
  (ReifiedLock.ofExpression held invariant family () (fun _ => rfl))

/-- The generic source correspondence and formula soundness apply jointly
    to a predicate that distinguishes zero from one in a real guarded cell. -/
theorem lockFormula_sound_zeuge :
    ∃ fact : VC.LockFormula family (), lockFormula family cellSources () = .ok fact ∧
      ∀ world, fact.formula.denote (assignment world) ↔
        family.inv () world.speicher = true := by
  have available : (lockFormula family cellSources ()).toOption.isSome = true := by decide_cbv
  cases computed : lockFormula family cellSources () with
  | error cause => simp only [computed, Except.toOption, Option.isSome] at available; cases available
  | ok fact => exact ⟨fact, rfl, lockFormula_sound family cellSources () fact computed⟩

/-- The same section either restores zero or violates the release condition.
    The bad body remains well typed; only the checked invariant distinguishes it. -/
def writeCell (preserves : Bool) : Stmt declaration contract false [] held held :=
  .assignGlob false
    (if preserves then .widen (by decide) (by decide) (.lit 0)
      else .widen (by decide) (by decide) (.lit 1))
    rfl cell_access

def sectionBody (preserves : Bool) : Block declaration contract false [] held held :=
  .cons (writeCell preserves) .nil

def program (preserves : Bool) : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ =>
    .cons (.locks () (fun _ member => nomatch member) (sectionBody preserves))
      (.ret .empty (List.Perm.refl _))

def initial : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def unit (preserves : Bool) : Einheit declaration where
  P := program preserves
  S := family
  Q := fun item => nomatch item
  starts := [⟨(), .nil⟩]
  sp0 := initial.speicher
  lockFormulas := cellSources
  axiomSources := some
    { items := []
      complete := fun item => nomatch item
      resources := fun item => nomatch item
      expression := fun item => nomatch item
      correct := fun item => nomatch item }
  pointerSignatures := some { count := 0, outside := fun _ _ _ => rfl }

theorem invariant_nontrivial_zeuge :
    family.inv () initial.speicher = true ∧
    family.inv () ({ initial with globs := fun _ => ⟨1, by decide, by decide⟩ }).speicher = false := by
  decide

theorem lock_initial_checked_zeuge :
    (checkUnitLock (unit true) ()).toOption.isSome = true := by decide_cbv

theorem program_accepted_zeuge :
    programInvariantsB (program true) family [()] cellSources {} [()] = true := by decide_cbv

theorem contracts_accepted_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (program true) family [()] cellSources = true := by decide_cbv

theorem invariants_accepted_zeuge : invariantenGeprueftB (unit true) [()] [()] = true := by decide_cbv

theorem logic_accepted_zeuge : nutzerPflichtGeprueftB (unit true) [()] [()] = true := by decide_cbv

/-- Acceptance through the complete concrete checker, including both new unit
    gates, the program invariant gate and the contract gate. -/
theorem checker_accepted_zeuge :
    akzeptiertX_pruefer.akzeptiert (unit true) [()] [()] [.inl (), .inr false, .inr true] = true := by
  have core : AkzeptiertX (program true) family [()] [()] [.inl (), .inr false, .inr true]
      (unit true).ws [] [] [] [] cellSources = true := by
    unfold AkzeptiertX
    rw [program_accepted_zeuge, contracts_accepted_zeuge]
    simp only [Bool.and_true]
    decide
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨core, besitzB_leer rfl⟩,
      Kernzelle.akkuStartB_leer (unit true)⟩, invariants_accepted_zeuge⟩, logic_accepted_zeuge⟩

theorem program_refused_zeuge :
    programInvariantsB (program false) family [()] cellSources {} [()] = false := by decide_cbv

theorem contracts_refused_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (program false) family [()] cellSources = false := by decide_cbv

theorem logic_refused_zeuge : nutzerPflichtGeprueftB (unit false) [()] [()] = false := by decide_cbv

theorem checker_refused_zeuge :
    akzeptiertX_pruefer.akzeptiert (unit false) [()] [()] [.inl (), .inr false, .inr true] = false := by
  change (_ && nutzerPflichtGeprueftB (unit false) [()] [()]) = false
  rw [logic_refused_zeuge, Bool.and_false]

/-- Lexical return crosses the acquired scope and must establish the same
    cell predicate before cleanup. This also exercises scopedReturnCondition. -/
def scopedProgram (preserves : Bool) : Programm declaration :=
  { program preserves with
    rumpf := fun _ =>
      .cons (.locks () (fun _ member => nomatch member)
        (.cons (writeCell preserves)
          (.cons (.retScoped .empty { scopes := [()], genau := List.Perm.refl _ }) .nil)))
        (.ret .empty (List.Perm.refl _)) }

theorem scoped_return_accepted_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (scopedProgram true) family [()] cellSources = true := by
  decide

theorem scoped_return_refused_zeuge :
    Vertraege.Pruefer.KontrakteGeprueftB (scopedProgram false) family [()] cellSources = false := by
  decide

def invalidInitial : Einheit declaration :=
  { unit true with sp0 :=
      ({ initial with globs := fun _ => ⟨1, by decide, by decide⟩ }).speicher }

theorem false_initial_refused_zeuge :
    (checkUnitLock invalidInitial ()).toOption.isSome = false := by decide_cbv

theorem opaque_unit_refused_zeuge :
    (checkUnitLock { unit true with lockFormulas := fun _ => none } ()).toOption.isSome = false := by
  decide

#print axioms lockFormula_sound_zeuge
#print axioms contracts_accepted_zeuge
#print axioms contracts_refused_zeuge

end Gabbro.Grammatik.Invarianten.Pruefer.LockWitness
