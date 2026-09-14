/-
  File:      Grammatik/Isabelle/RestrictAlleinzugriff.lean
  Port of:   beweise/Restrict_Alleinzugriff.thy (template
              `restrict.alleinzugriff` -- when the generator may write
              `restrict`)

  C11 6.7.3.1 says what is promised: if the object X is reached in block B
  through the `restrict` pointer P, then EVERY access to X inside B must run
  through a pointer derived from P. This theory shows UNDER WHICH conditions
  Gabbro may claim that -- and makes the conditions hypotheses, so the checker
  must discharge each one individually. It does NOT prove that `own` means
  exclusivity: that is a language decision and stands here as a named
  assumption, not a theorem.

  Adaptations (same content, Lean core without mathlib):
  - Roots and the access set are predicates (`wurzel → Prop`) instead of
    string sets (Isabelle: `wurzel set` in `record rumpf`); `⊆` becomes
    `∀ w, ... → ...`. Same mathematical content.
-/

namespace Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff

/-- A root: the name a access runs through (a parameter name or a global
    name). (Isabelle: `type_synonym wurzel = string`.) -/
abbrev Wurzel := String

/-- A place: the memory cell a root denotes. (Isabelle: `type_synonym ort`.) -/
abbrev Ort := Nat

/-- A body: its accesses (as roots) and the place each root denotes.
    (Isabelle: `record rumpf`.) -/
structure Rumpf where
  zugriffe : Wurzel → Prop
  ortVon : Wurzel → Ort

/-- The C condition, verbatim: every access hitting `p`'s place runs through
    `p`. (Isabelle: `restrict_bedingung`.) -/
def restrictBedingung (B : Rumpf) (p : Wurzel) : Prop :=
  ∀ w, B.zugriffe w → B.ortVon w = B.ortVon p → w = p

/-- H1 -- the frame is COMPLETE. (Isabelle: `rahmen_vollstaendig`.) -/
def rahmenVollstaendig (B : Rumpf) (W : Wurzel → Prop) : Prop :=
  ∀ w, B.zugriffe w → W w

/-- H2 -- the other roots lie elsewhere. (Isabelle: `wurzeln_getrennt`.) -/
def wurzelnGetrennt (B : Rumpf) (W : Wurzel → Prop) (p : Wurzel) : Prop :=
  ∀ w, W w → w ≠ p → B.ortVon w ≠ B.ortVon p

/-! ## The theorem -/

/-- THE theorem: a complete frame plus separated roots justify `restrict`.
    H3 -- `p` accesses its own place -- is NOT needed: the theorem also holds
    when `p` stays unused; then no access hits its place and the condition is
    vacuously true. (Isabelle: `restrict_gerechtfertigt`.) -/
theorem restrict_gerechtfertigt (B : Rumpf) (W : Wurzel → Prop) (p : Wurzel)
    (voll : rahmenVollstaendig B W)
    (getrennt : wurzelnGetrennt B W p) :
    restrictBedingung B p := by
  intro w hzug hgleich
  have hW : W w := voll w hzug
  rcases Decidable.em (w = p) with heq | hne
  · exact heq
  · exact absurd hgleich (getrennt w hW hne)

/-! ## The converse -- and it is the more important one -/

/-- If either hypothesis falls, so does the theorem: the checker must
    discharge BOTH, and may not "mostly" assume one of them.
    (Isabelle: `ohne_trennung_kein_restrict`.) -/
theorem ohne_trennung_kein_restrict (B : Rumpf) (p q : Wurzel)
    (hort : B.ortVon q = B.ortVon p) (hne : q ≠ p) (hzug : B.zugriffe q) :
    ¬ restrictBedingung B p := by
  intro hcond
  exact hne (hcond q hzug hort)

/-- An incomplete frame carries nothing either: an access outside `W` can hit
    `p`'s place without `wurzeln_getrennt` saying anything about it.
    (Isabelle: `unvollstaendiger_rahmen_traegt_nichts`.) -/
theorem unvollstaendiger_rahmen_traegt_nichts (B : Rumpf) (W : Wurzel → Prop)
    (p q : Wurzel)
    (_hgetrennt : wurzelnGetrennt B W p)
    (_haussen : ¬ W q) (hne : q ≠ p)
    (hzug : B.zugriffe q) (hort : B.ortVon q = B.ortVon p) :
    ¬ restrictBedingung B p := by
  intro hcond
  exact hne (hcond q hzug hort)

/-! ## Witness: justification on a concrete body -/

/-- Witness: the body accessing only `p` at place `7`, with frame `{p}`,
    satisfies the `restrict` condition -- and adding an aliased `q` breaks
    it. No lemma above quantifies over syntax, so the inhabitation obligation
    is vacuous; this is a data-level witness. -/
theorem restrict_zeuge :
    restrictBedingung ⟨fun w => w = "p", fun _ => 7⟩ "p" := by
  intro w hzug _
  exact hzug

/-- The converse witness, cleanly: with `q` accessing place `7` alongside
    `p`, the condition fails. -/
theorem restrict_gegenzeuge :
    ¬ restrictBedingung ⟨fun w => w = "p" ∨ w = "q", fun _ => 7⟩ "p" := by
  intro hcond
  have hq : ("q" : Wurzel) ≠ "p" := by decide
  have hqq : (fun w : Wurzel => w = "p" ∨ w = "q") "q" := Or.inr rfl
  exact hq (hcond "q" hqq rfl)

/-! ## Bridge

  The Lean model has no C-level `restrict` annotation: neither `Deklaration`
  nor any `Stmt` carries an alias promise, and `World` has no addressable
  roots through which two names could denote one place. The theorem therefore
  stands as pure mathematics over an abstract body -- exactly as the Isabelle
  theory leaves the `own`-means-exclusive step as a language decision. The
  checker-side duties (H1 via `E008`/`E010`, H2 via at most one pointer
  parameter per carrier type) have no Lean-grammar counterpart to tie to:
  the grammar names no frames and no roots. Named, not faked. -/

#print axioms Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff.restrict_gerechtfertigt
#print axioms Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff.ohne_trennung_kein_restrict
#print axioms Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff.unvollstaendiger_rahmen_traegt_nichts
#print axioms Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff.restrict_zeuge
#print axioms Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff.restrict_gegenzeuge

end Gabbro.Grammatik.Isabelle.RestrictAlleinzugriff
