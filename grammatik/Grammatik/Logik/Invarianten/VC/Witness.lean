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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem guarded_decided_zeuge : decideB (writerVC guardedCompiled entry .tru) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem unguarded_decided_zeuge : decideB (writerVC unguardedCompiled entry .tru) = false := by
  decide

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

/-- P17 also extracts a model for the FALSE generated closed VC. The concrete
    failing G step above separately rules out a merely arithmetic witness. -/
theorem counterexample_extracted_zeuge :
    ∃ values : Assignment (Observation declaration),
      writerCounterexample unguardedCompiled entry .tru = some values :=
  writerCounterexample_complete unguardedCompiled entry .tru unguarded_decided_zeuge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem checked_call_zeuge :
    decideB (close (callWP (D := declaration) () post post)) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem unchecked_call_havoc_zeuge :
    decideB (close (callWP (D := declaration) () .tru post)) = false := by decide

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
