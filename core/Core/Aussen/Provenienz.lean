/-
  File:      core/Core/Aussen/Provenienz.lean
  Subject:   OUTSIDE PROVENANCE (PERFECT-MODEL §4, step M10): every outside answer carries the
             outside object and its generation; provenance flows transitively through data,
             control, aliases and derived handles. A value records the set of answers it depends
             on; propagation only grows that set (`propagierung_monoton`); every value derived
             from an outside answer carries its provenance (`abgeleitet_traegt`).
-/
module

public import Core.Katalog.Aussen

@[expose] public section

namespace Gabbro.Core.Aussen

open Gabbro.Core.Katalog

/-- **Outside provenance**: the set of outside answers (object and generation) a value or
    a handle label depends on. -/
abbrev Provenienz := Herkunft → Prop

/-- No outside dependence. -/
def leer : Provenienz := fun _ => False

/-- The provenance of one outside answer. -/
def einzel (h : Herkunft) : Provenienz := fun h' => h' = h

/-- Joint dependence of two provenances. -/
def vereinige (P Q : Provenienz) : Provenienz := fun h => P h ∨ Q h

/-- **A value with its provenance**: the content and the outside answers it depends on. -/
structure Wert (A : Type) where
  inhalt : A
  spur : Provenienz

/-- A fresh value depends on nothing. -/
def rein (x : A) : Wert A := ⟨x, leer⟩

/-- Data flow: combining two values unites their provenances. -/
def kombiniere (u : Wert B) (v : Wert C) (x : A) : Wert A := ⟨x, vereinige u.spur v.spur⟩

/-- Control flow: branching on a condition adds the condition's provenance to both branches. -/
def verzweige (c : Wert Bool) (t e : Wert A) (x : A) : Wert A :=
  ⟨x, vereinige c.spur (vereinige t.spur e.spur)⟩

/-- An alias keeps the provenance of the value it names. -/
def aliasWeiter (u : Wert A) : Wert A := u

/-- A value read from an outside answer carries that answer's object and generation. -/
def ausAntwort (a : Antwort) (x : A) : Wert A := ⟨x, einzel a.origin⟩

/-- A handle derived from an outside answer carries that answer's object and generation. -/
def griffAus (a : Antwort) (h : Handle) : Wert Handle := ⟨h, einzel a.origin⟩

/-- One propagation step through data, control, an alias or a derived handle. -/
inductive PropSchritt : Provenienz → Provenienz → Prop
  | datenLinks (P Q : Provenienz) : PropSchritt P (vereinige P Q)
  | datenRechts (P Q : Provenienz) : PropSchritt Q (vereinige P Q)
  | kontrolle (C T E : Provenienz) : PropSchritt C (vereinige C (vereinige T E))
  | zweig (C T E : Provenienz) : PropSchritt T (vereinige C (vereinige T E))
  | zweigRechts (C T E : Provenienz) : PropSchritt E (vereinige C (vereinige T E))
  | alias (P : Provenienz) : PropSchritt P P
  | antwort (a : Antwort) : PropSchritt (einzel a.origin) (einzel a.origin)

/-- **Propagation is monotone**: every step only grows the provenance label. -/
theorem propagierung_monoton {P P' : Provenienz} (step : PropSchritt P P')
    (q : Herkunft) (h : P q) : P' q := by
  cases step with
  | datenLinks P Q => exact Or.inl h
  | datenRechts P Q => exact Or.inr h
  | kontrolle C T E => exact Or.inl h
  | zweig C T E => exact Or.inr (Or.inl h)
  | zweigRechts C T E => exact Or.inr (Or.inr h)
  | alias P => exact h
  | antwort a => exact h

/-- A derivation tree: how a value was built from outside answers. -/
inductive Abgeleitet : {A : Type} → Wert A → Antwort → Prop
  | direkt {A : Type} (a : Antwort) (x : A) : Abgeleitet (ausAntwort a x) a
  | griff (a : Antwort) (h : Handle) : Abgeleitet (griffAus a h) a
  | links {A B C : Type} {u : Wert B} {v : Wert C} {x : A} {a : Antwort}
      (h : Abgeleitet u a) : Abgeleitet (kombiniere u v x) a
  | rechts {A B C : Type} {u : Wert B} {v : Wert C} {x : A} {a : Antwort}
      (h : Abgeleitet v a) : Abgeleitet (kombiniere u v x) a
  | bedingung {A : Type} {c : Wert Bool} {t e : Wert A} {x : A} {a : Antwort}
      (h : Abgeleitet c a) : Abgeleitet (verzweige c t e x) a
  | zweigLinks {A : Type} {c : Wert Bool} {t e : Wert A} {x : A} {a : Antwort}
      (h : Abgeleitet t a) : Abgeleitet (verzweige c t e x) a
  | zweigRechts {A : Type} {c : Wert Bool} {t e : Wert A} {x : A} {a : Antwort}
      (h : Abgeleitet e a) : Abgeleitet (verzweige c t e x) a
  | alias {A : Type} {u : Wert A} {a : Antwort}
      (h : Abgeleitet u a) : Abgeleitet (aliasWeiter u) a

/-- **Every value derived from an outside answer carries its provenance**: the answer's
    object and generation are in the value's label. -/
theorem abgeleitet_traegt {A : Type} (u : Wert A) (a : Antwort)
    (h : Abgeleitet u a) : u.spur a.origin := by
  induction h with
  | direkt a x => rfl
  | griff a h => rfl
  | links h ih => exact Or.inl ih
  | rechts h ih => exact Or.inr ih
  | bedingung h ih => exact Or.inl ih
  | zweigLinks h ih => exact Or.inr (Or.inl ih)
  | zweigRechts h ih => exact Or.inr (Or.inr ih)
  | alias h ih => exact ih

/-- Satisfiability: a value read from a hosted answer carries that answer's provenance. -/
theorem provenienz_erfuellbar :
    ∃ (a : Antwort) (u : Wert Nat), Abgeleitet u a ∧ u.spur a.origin := by
  let a : Antwort := ⟨⟨⟨.hosted, 0⟩, 0⟩, [], .ok (.data [])⟩
  exact ⟨a, ausAntwort a 0, .direkt a 0, rfl⟩

end Gabbro.Core.Aussen
