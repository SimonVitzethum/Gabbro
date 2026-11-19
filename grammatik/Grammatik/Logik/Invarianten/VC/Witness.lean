module

public import Grammatik.Logik.Invarianten.VC.Writer
public import Grammatik.Logik.Invarianten.Frag.Witness
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section

set_option profiler true

namespace Gabbro.Grammatik.Invarianten.VC.Witness

open Frag Elim Elim.Korrekt Modell

/-- Two bounded globals, one real writer, and a nonempty owed invariant. -/
abbrev declaration : Deklaration :=
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

/-- The same fixture discharges the model obligation, with a genuinely owed
    invariant and without assuming any callee ensures. -/
def owedPost : InvariantFormula program
    (declaration.invs.filter (fun item => schuldet (D := declaration) () item)) where
  formula := post
  correct := fun world => by
    rw [post, lower_denote]
    have translated := translateDeclared_sound program () entry rfl world
    constructor
    · intro h item _
      cases item
      exact translated.mpr h
    · intro h
      exact translated.mp (h () (by decide))

end Gabbro.Grammatik.Invarianten.VC.Witness
