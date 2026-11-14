module

public import Grammatik.Logik.Invarianten.VC.Writer
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

set_option profiler true

namespace Gabbro.Grammatik.Invarianten.VC.Witness

open Frag Elim Elim.Korrekt Modell

/-- Two bounded globals, one real writer, and a nonempty owed invariant. -/
def declaration : Deklaration :=
  { Frag.Witness.declaration with
    Fn := Unit
    sig := fun _ => 0
    sigNr := fun _ =>
      { params := []
        erg := none
        gruende := 0
        haelt := []
        schreibt := fun _ => false
        gschreibt := fun name => !name
        konsumiert := []
        produziert := [] }
    passt := fun _ n => decide (0 = n)
    passt_ok := fun _ _ _ => SigPasst.refl _ _
    rzusage := fun item => nomatch item
    invarianten_gehalten := fun _ _ _ _ _ lock => nomatch lock }

abbrev contract : Vertrag declaration := vertragVon declaration ()

def access (name : declaration.Glob) : gdarf declaration name [] := fun _ h => nomatch h

def lengthValue {Γ : Ctx} : Expr declaration Γ [] (.int 0 10) := .glob false (access false)

def capacityValue {Γ : Ctx} : Expr declaration Γ [] (.int 0 10) := .glob true (access true)

def invariant {Γ : Ctx} : Expr declaration Γ [] .bool := .le lengthValue capacityValue

def guard {Γ : Ctx} : Expr declaration Γ [] .bool := .lt lengthValue capacityValue

/-- The canonical model requires interval narrowing on `len + 1`. Its fallback
    leaves len alone; at the guarded increment it is unreachable on typed states. -/
def increment {Γ : Ctx} {l : Bool} : Stmt declaration contract l Γ [] [] :=
  .assignGlob false (.eng (.add lengthValue (.lit 1)) 0 10 lengthValue) rfl (access false)

def guarded : Endblock declaration contract false [] [] :=
  .cons (.ite guard (.cons increment .nil) .nil) (.ret .empty (List.Perm.refl _))

def unguarded : Endblock declaration contract false [] [] :=
  .cons increment (.ret .empty (List.Perm.refl _))

def program : Programm declaration where
  invariante := fun _ => invariant
  requires := fun _ => invariant
  ensures := fun _ => .tru
  rumpf := fun _ => guarded

def entry : LProp (Observation declaration) := .le (.var (.glob false)) (.var (.glob true))

def post : QF (Observation declaration) := lower entry

def noFacts : declaration.Fn → List declaration.Inv := fun _ => []

def guardedCompiled : EndVC program noFacts guarded .nil post :=
  ((endBlock program noFacts guarded .nil post).toOption).get (by decide)

def unguardedCompiled : EndVC program noFacts unguarded .nil post :=
  ((endBlock program noFacts unguarded .nil post).toOption).get (by decide)

/- This decision is on the VC generated from the typed G writer, rather than
   on a manually supplied preservation formula. -/
private def incrementTerm : LTerm (Observation declaration) :=
  .add (.var (.glob false)) (.konst 1)

private def incrementRange : LProp (Observation declaration) :=
  .and (.le (.konst 0) incrementTerm) (.le incrementTerm (.konst 10))

private def incrementFormula : QF (Observation declaration) :=
  lower (.and (.imp incrementRange (quoteQF (post.subst (.glob false) incrementTerm)))
    (.imp (.not incrementRange) (quoteQF (post.subst (.glob false) (.var (.glob false))))))

private theorem guarded_formula : guardedCompiled.formula =
    lower (.and (.imp (.lt (.var (.glob false)) (.var (.glob true))) (quoteQF incrementFormula))
      (.imp (.not (.lt (.var (.glob false)) (.var (.glob true)))) (quoteQF post))) := rfl

private theorem unguarded_formula : unguardedCompiled.formula = incrementFormula := rfl

theorem guarded_decided_zeuge : decideB (writerVC guardedCompiled entry .tru) = true := by
  apply (close_decide_true_iff _).mpr
  intro values
  rw [writerMatrix, lower_denote]
  intro _
  rw [quoteQF_denote, lower_denote]
  intro initial
  rw [quoteQF_denote, guarded_formula]
  simp only [lower_denote, LProp.denote, quoteQF_denote, incrementFormula,
    incrementRange, subst_denote, post, entry, incrementTerm, LTerm.denote] at *
  simp only [Assignment.bind, ↓reduceIte] at *
  omega

/-- A concrete typed pre-state realizes the failed unguarded increment. -/
def counterexampleWorld : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨4, by decide, by decide⟩
  spur := []

def oracle : Orakel declaration where
  wirktL := fun item => nomatch item
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun _ _ => true

def calls (f : declaration.Fn) (world : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .ok world ()

theorem counterexample_entry_zeuge :
    eval counterexampleWorld invariant counterexampleWorld .nil = true := by decide

theorem counterexample_step_zeuge :
    (match execEnd oracle 0 calls unguarded counterexampleWorld .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide

theorem unguarded_decided_zeuge : decideB (writerVC unguardedCompiled entry .tru) = false := by
  apply (close_decide_false_iff _).mpr
  refine ⟨assignment counterexampleWorld, ?_⟩
  rw [writerMatrix, lower_denote]
  intro valid
  have step := (quoteQF_denote _ _).mp (valid (typeFacts_sound _ counterexampleWorld))
  rw [lower_denote] at step
  have initial : entry.denote (assignment counterexampleWorld) ∧ LProp.denote _ .tru := by
    exact ⟨by decide, trivial⟩
  have result := (quoteQF_denote _ _).mp (step initial)
  rw [unguarded_formula] at result
  norm_num [incrementFormula, lower_denote, quoteQF_denote, subst_denote,
    incrementRange, incrementTerm, post, entry, LProp.denote, LTerm.denote,
    Assignment.bind, assignment, counterexampleWorld, scalarValue] at result

/-- P17 also extracts a model for the FALSE generated closed VC. The concrete
    failing G step above separately rules out a merely arithmetic witness. -/
theorem counterexample_extracted_zeuge :
    ∃ values : Assignment (Observation declaration),
      writerCounterexample unguardedCompiled entry .tru = some values :=
  writerCounterexample_complete unguardedCompiled entry .tru unguarded_decided_zeuge

theorem checked_call_zeuge :
    decideB (close (callWP (D := declaration) () post post)) = true := by
  apply (close_decide_true_iff _).mpr
  apply havoc_of_valid
  intro values
  apply (lower_denote _ _).mpr
  exact fun initial => initial.2

theorem unchecked_call_havoc_zeuge :
    decideB (close (callWP (D := declaration) () .tru post)) = false := by
  apply (close_decide_false_iff _).mpr
  let next : World declaration :=
    { counterexampleWorld with globs := fun name => if name then ⟨4, by decide, by decide⟩
      else ⟨5, by decide, by decide⟩ }
  refine ⟨assignment counterexampleWorld, ?_⟩
  intro valid
  have result := callWP_sound () .tru post counterexampleWorld next valid ?_ trivial
  · norm_num [post, lower_denote, entry, LProp.denote, LTerm.denote, assignment,
      next, scalarValue] at result
  · constructor
    · intro table _ index field
      rfl
    · intro name unchanged
      cases name
      · cases unchanged
      · rfl

/-- The invariant is actually owed by the witness's function. -/
theorem owed_zeuge : schuldet (D := declaration) () () = true := by decide

theorem guarded_preserves_zeuge (O : Orakel declaration) (passes : Nat)
    (R : ∀ f : declaration.Fn, World declaration → Env declaration (declaration.params f) → RufAusgang f)
    (evidence : CallEvidence program noFacts R) (world : World declaration)
    (initial : entry.denote (assignment world)) :
    WP.wpE O passes R guarded (EndFlow post) world .nil :=
  writerVC_wp_sound guardedCompiled entry .tru guarded_decided_zeuge
    O passes R evidence world initial trivial

/-- The same fixture discharges the model obligation, with a genuinely owed
    invariant and without assuming any callee ensures. -/
def owedPost : InvariantFormula program
    (declaration.invs.filter (fun item => schuldet (D := declaration) () item)) where
  formula := post
  correct := fun world => by
    rw [lower_denote]
    have translated := translateDeclared_sound program () entry rfl world
    constructor
    · intro h item _
      cases item
      exact translated.mpr h
    · intro h
      exact translated.mp (h () (by decide))

theorem guarded_invGutS_zeuge (passes : Nat) (Q : AxEns declaration)
    (S : SperrInv declaration) : InvGutS program passes Q S () := by
  apply writerVC_sound program noFacts () passes Q S owedPost
    (fun locals => by cases locals; exact guardedCompiled) entry .tru
  · intro locals
    cases locals
    exact guarded_decided_zeuge
  · intro world locals initial
    cases locals
    exact ⟨(translateDeclared_sound program () entry rfl world).mp initial, trivial⟩
  · intro R respects _
    exact frameOnlyEvidence program R respects
  · decide

end Gabbro.Grammatik.Invarianten.VC.Witness
