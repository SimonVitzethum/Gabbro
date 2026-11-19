/- A two-valued result fixture beside the unchanged replay counterexample.
   Its function proves that its actual returned Boolean is true; returning
   false keeps the same types and violates the declared postcondition. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T10CallSiteZeuge
public import Grammatik.Logik.Vertraege.Pruefer.Goal

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker.Positive

/-- Retain the unused software item, with a genuinely two-valued function result. -/
def decl : Deklaration :=
  { Gabbro.Grammatik.CallSiteZeuge.decl with
    sigNr := fun _ => { Gabbro.Grammatik.CallSiteZeuge.sig with erg := some .bool }
    passt := fun _ _ => false
    passt_ok := fun _ _ impossible => by cases impossible
    rzusage := fun item => nomatch item }

instance : DecidableEq decl.Fn := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq decl.Ax := inferInstanceAs (DecidableEq Unit)

def contract : CallContract decl (decl.asignatur ()) where
  pre := .fls
  post := .fls

def program : Programm decl where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .var .here
  rumpf := fun _ => .ret (.val .tru) List.Perm.nil
  axVertrag := fun _ => contract

def memory : Speicher decl where
  slots := fun item => nomatch item
  globs := fun item => nomatch item

def world : World decl := memory.welt []

def rho : Env decl (decl.aparams ()) := .cons ⟨1, by decide, by decide⟩ .nil

def traceOracle : Orakel decl where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, 0)
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun item => nomatch item

def unit : Einheit decl where
  P := program
  S := SperrInv.leer decl
  Q := fun _ _ _ => false
  starts := [⟨(), .nil⟩]
  sp0 := memory
  axiomSources := some
    { items := [()]
      complete := fun item => by cases item; exact List.mem_cons_self
      resources := fun _ => []
      expression := fun _ => .fls
      correct := fun _ _ _ => rfl }
  pointerSignatures := some { count := 0, outside := fun _ _ _ => rfl }

theorem functions_complete : ∀ f : decl.Fn, f ∈ [()] := fun f => by
  cases f
  exact List.mem_cons_self

/-- The source post reads the two-valued return variable, not literal truth. -/
theorem good_checker : akzeptiertX_pruefer.akzeptiert unit [()] [] [] = true := by
  simp only [akzeptiertX_pruefer, AkzeptiertX, Bool.and_eq_true]
  and_intros
  all_goals first
    | exact (schnittstellenB_iff functions_complete).mpr (schnittstellen_standard _ _)
    | decide +kernel

theorem good_user : NutzerPflichtA unit :=
  nutzerPflicht_of_akzeptiert ⟨[()], functions_complete⟩
    ⟨[], fun item => nomatch item⟩ good_checker

def wrongUnit : Einheit decl :=
  { unit with P := { program with rumpf := fun _ => .ret (.val .fls) List.Perm.nil } }

theorem post_cover : PostDeckt unit := by
  intro a hsw old locals next value impossible
  exact False.elim (Bool.false_ne_true impossible)

theorem binding : ForeignVertrag unit traceOracle := by
  constructor
  · intro a hsw σ locals impossible
    exact False.elim (Bool.false_ne_true impossible)
  · intro a hsw σ locals
    change some (Sum.inl ()) ≠ none
    intro impossible
    cases impossible

theorem oracle_good : GutO traceOracle := by
  intro a σ locals
  refine ⟨rahmen_gleich rfl rfl, rfl, ?_⟩
  intro tables globals
  refine ⟨[], [], [], ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals intro item; exact nomatch item

theorem hardware [RootNativeFloat.Hardware] : HardwareAnnahmenHw traceOracle unit.Q := by
  refine ⟨oracle_good, ?_, (fun a hsw => absurd rfl hsw), inferInstance⟩
  exact ⟨(fun item => nomatch item), (fun item => nomatch item)⟩

theorem no_global_summary : ¬ AxVertragO unit.Q traceOracle := by
  intro summary
  exact Bool.false_ne_true (summary () world rho () rfl)

end Gabbro.Grammatik.Zielsatz.CallSiteReplayBlocker.Positive
