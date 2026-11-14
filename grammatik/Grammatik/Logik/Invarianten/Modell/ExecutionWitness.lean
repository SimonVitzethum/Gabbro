module

public import Grammatik.Logik.Invarianten.Modell.Decision
public import Grammatik.Logik.Invarianten.Frag.Witness
public import Grammatik.Zielsatz.Kern.Spec.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Modell.ExecutionWitness

open Zielsatz

/-- One actual writer, with no locks and one declared invariant. The scalar
    carriers and their types are the small translation fixture's carriers. -/
def declaration : Deklaration := { Frag.Witness.declaration with
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => ⟨[], none, 0, [], fun _ => false, fun g => !g, [], [], none, {}⟩
  passt := fun _ n => decide (0 = n)
  passt_ok := by
    intro _ n h
    have same : 0 = n := of_decide_eq_true h
    subst n
    exact SigPasst.refl _ _
  rzusage := fun r => nomatch r
  invarianten_gehalten := fun _ _ _ _ _ L => nomatch L }

private theorem globalAccess (resources : List (Res declaration)) :
    gdarf declaration false resources := fun _ member => nomatch member

/-- The positive predicate uses the declared type bound; the negative one is
    refuted by the writer's value 1. Both predicates really read memory. -/
def predicate (valid : Bool) : Expr declaration [] (invSicht declaration ()) .bool :=
  if valid then .le (.glob false (globalAccess _)) (.lit 10)
  else .eq (.glob false (globalAccess _)) (.lit 0)

def program (valid : Bool) : Programm declaration where
  invariante _ := predicate valid
  requires _ := .tru
  ensures _ := .tru
  rumpf _ := .cons
    (.assignGlob false (.widen (by decide) (by decide) (.lit 1)) rfl (globalAccess _))
    (.ret .empty (.refl _))

def initial : World declaration where
  slots _ _ _ := ⟨0, by decide, by decide⟩
  globs _ := ⟨1, by decide, by decide⟩
  spur := []

def unit (valid : Bool) : Einheit declaration where
  P := program valid
  S := SperrInv.leer declaration
  Q := fun a => nomatch a
  starts := [⟨(), .nil⟩]
  sp0 := initial.speicher

/-- Non-degeneracy: the declared start is a writer owing the invariant. -/
theorem writer_owes_zeuge :
    schuldet (D := declaration) () () = true ∧ (unit true).starts.length = 1 :=
  ⟨by decide, rfl⟩

/-- Execute translation, computed typed closure, budget and Cooper decision.
    This proof deliberately does not use either semantic validity equivalence. -/
theorem positive_computed_zeuge :
    decideInvariant (declaration.traeger ()) ((unit true).P.invariante ()) = .ok true := by
  decide

theorem negative_computed_zeuge :
    decideInvariant (declaration.traeger ()) ((unit false).P.invariante ()) = .ok false := by
  decide

/-- Execute the extractor as well, without imposing a particular choice of
    counterexample among the nonzero typed values. -/
theorem counterexample_computed_zeuge :
    (invariantCounterexample initial (declaration.traeger ())
      ((unit false).P.invariante ())).isSome = true := by
  decide

theorem positive_sound_zeuge (world : World declaration) :
    eval world ((unit true).P.invariante ()) world .nil = true :=
  decideInvariant_sound _ _ none positive_computed_zeuge world

theorem negative_sound_zeuge :
    ∃ world : World declaration,
      invariantCounterexample initial (declaration.traeger ())
        ((unit false).P.invariante ()) = some world ∧
      eval world ((unit false).P.invariante ()) world .nil = false :=
  decideInvariant_complete initial _ _ none negative_computed_zeuge

end Gabbro.Grammatik.Invarianten.Modell.ExecutionWitness
