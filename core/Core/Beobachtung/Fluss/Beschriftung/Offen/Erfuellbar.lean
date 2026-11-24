module

public import Core.Beobachtung.Fluss.Beschriftung.Aufgaben
public import Core.Beobachtung.Fluss.Beschriftung.Leck

@[expose] public section

/-! Joint satisfiability of the pinned premise bundles in `Aufgaben`. Every witness uses a
    declaration with a secret temporary slot the instruction does not read, so the bundles are
    not shown satisfiable only by the all-public declaration. -/

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

/-- A declaration whose temporary `q` is secret at every cut; all other temporaries, all locals
    and the result are public. -/
def niGeheimTempBeschriftung (q : Nat) : Beschriftung :=
  { temp := fun _ s => if s = q then geheim else ∅ }

theorem niGeheimTemp_temp (q pc s : Nat) :
    oeffentlich ((niGeheimTempBeschriftung q).temp pc s) = true ↔ s ≠ q := by
  simp only [niGeheimTempBeschriftung]
  split
  · simp only [geheim_verborgen, Bool.false_eq_true, false_iff, ne_eq, not_not]
    assumption
  · rename_i h
    simp only [oeffentlich_leer, true_iff]
    exact h

theorem niGeheimTemp_lokal (q pc i : Nat) :
    oeffentlich ((niGeheimTempBeschriftung q).lokal pc i) = true := by
  simp only [niGeheimTempBeschriftung, oeffentlich_leer]

/-- The `zuweisen` premises hold jointly. `zuweisen` reads only `temp quelle`; the secret
    temporary `quelle + 1` is never read by the instruction. -/
theorem zuweisenSicht_erfuellbar (quelle index : Nat) (zieltyp : Ty .value) :
    ∃ (β : Beschriftung) (pc : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, i ≠ index → oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (oeffentlich (β.lokal (pc + 1) index) = true →
        oeffentlich (β.temp pc quelle) = true) :=
  ⟨niGeheimTempBeschriftung (quelle + 1), 0,
    (fun s hs => by
      rw [niGeheimTemp_temp] at hs ⊢
      exact hs),
    (fun i _ hpub => hpub),
    (fun _ => (niGeheimTemp_temp (quelle + 1) 0 quelle).2 (by omega))⟩

/-- The `binden` premises hold jointly. `binden` reads only `temp quelle`; the secret temporary
    `quelle + 1` is never read by the instruction. -/
theorem bindenSicht_erfuellbar (name : Identifier) (quelle : Nat) :
    ∃ (β : Beschriftung) (pc : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (oeffentlich (β.lokal (pc + 1) 0) = true →
        oeffentlich (β.temp pc quelle) = true) :=
  ⟨niGeheimTempBeschriftung (quelle + 1), 0,
    (fun s hs => by
      rw [niGeheimTemp_temp] at hs ⊢
      exact hs),
    (fun i hpub => hpub),
    (fun _ => (niGeheimTemp_temp (quelle + 1) 0 quelle).2 (by omega))⟩

/-- The `bindeWert` premises hold jointly. `bindeWert` reads only `temp quelle` (which stays
    public, also for `global = true`); the secret temporary `quelle + 1` is never read. -/
theorem bindeWertSicht_erfuellbar (quelle : Nat) (ziel : Ty .value) (global : Bool) :
    ∃ (β : Beschriftung) (pc : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) (i + 1)) = true →
        oeffentlich (β.lokal pc i) = true) ∧
      (oeffentlich (β.lokal (pc + 1) 0) = true →
        oeffentlich (β.temp pc quelle) = true) ∧
      (global = true → oeffentlich (β.temp pc quelle) = true) :=
  ⟨niGeheimTempBeschriftung (quelle + 1), 0,
    (fun s hs => by
      rw [niGeheimTemp_temp] at hs ⊢
      exact hs),
    (fun i hpub => hpub),
    (fun _ => (niGeheimTemp_temp (quelle + 1) 0 quelle).2 (by omega)),
    (fun _ => (niGeheimTemp_temp (quelle + 1) 0 quelle).2 (by omega))⟩

/-- The `blockEnde` premises hold jointly. `blockEnde` drops locals and reads no temporary at
    all, so temporary `0` may be secret at every cut. -/
theorem blockEndeSicht_erfuellbar (count : Nat) :
    ∃ (β : Beschriftung) (pc : Nat),
      (∀ s, oeffentlich (β.temp (pc + 1) s) = true →
        oeffentlich (β.temp pc s) = true) ∧
      (∀ i, oeffentlich (β.lokal (pc + 1) i) = true →
        oeffentlich (β.lokal pc (i + count)) = true) :=
  ⟨niGeheimTempBeschriftung 0, 0,
    (fun s hs => by
      rw [niGeheimTemp_temp] at hs ⊢
      exact hs),
    (fun i hpub => hpub)⟩

end Gabbro.Core.Ast.Semantik
