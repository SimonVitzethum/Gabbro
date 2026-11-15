module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Fixtures


@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.RecursionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Pruefer Zielsatz

/-- A three-value parameter range permits a small, real recursive fixture. -/
def declaration : Deklaration :=
  { Witness.declaration with
    sigNr := fun _ =>
      { params := [.int 0 2], erg := none, gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun _ => false
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible }

instance : DecidableEq declaration.Fn := inferInstanceAs (DecidableEq Unit)

abbrev contract := vertragVon declaration ()

def fits : RufPasst declaration contract (declaration.signatur ()) [] where
  hw := fun _ impossible => by cases impossible
  hg := fun _ impossible => by cases impossible
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh := fun _ impossible => nomatch impossible

def smaller : Expr declaration [.int 0 2] [] (.int 0 2) :=
  .eng (.sub (.var .here) (.lit 1)) 0 2 (.widen (by decide) (by decide) (.lit 0))

def recursive (decrease : Bool) : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ =>
    .cons (.ite (.lt (.lit 0) (.var .here))
      (.cons (.call () (.cons (if decrease then smaller else .var .here) .nil) fits rfl) .nil) .nil)
      (.ret .empty (List.Perm.refl _))

def measure : Mass declaration := fun _ => [⟨2, .var .here, rfl⟩]

def anchor : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

/-- A true result of the actual measure VC gate, including its canonical
    computed recursion cycle. No recursive-call descent proof is supplied. -/
theorem recursive_decreases_checked_zeuge :
    (checkMeasure (recursive true) (SperrInv.leer declaration) (fun _ => none) {} none
      measure (zykS (recursive true) [()]) anchor ()).toOption.isSome = true := by
  decide +kernel

theorem unchanged_decreases_refused_zeuge :
    (checkMeasure (recursive false) (SperrInv.leer declaration) (fun _ => none) {} none
      measure (zykS (recursive false) [()]) anchor ()).toOption.isSome = false := by
  decide +kernel

/-- The checked Bool derives MassPflicht, uniformly in execution budget,
    hardware contracts and the admitted atomic rely. -/
theorem massPflicht_zeuge (passes : Nat) (Q : AxEns declaration)
    (shared : declaration.Tab ⊕ declaration.Glob → Prop)
    (subset : ∀ carrier, shared carrier → AtomarAusgenommen carrier) :
    MassPflicht (recursive true) passes Q (SperrInv.leer declaration) shared measure
      (zykS (recursive true) [()]) () := by
  cases result : checkMeasure (recursive true) (SperrInv.leer declaration) (fun _ => none) {} none
      measure (zykS (recursive true) [()]) anchor () with
  | error cause =>
      have accepted := recursive_decreases_checked_zeuge
      simp only [result, Except.toOption, Option.isSome_none, Bool.false_eq_true]
        at accepted
  | ok certificate => exact certificate.down passes Q shared subset

end Gabbro.Grammatik.Vertraege.Pruefer.RecursionWitness
