/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Beweise/Update.lean
  Subject:   THE UPDATE SEMANTICS OF THE ATOMIC INSTRUCTIONS, proved over the change of `Form.lean` and the frame
             transfer of `Schritt.lean`. Three statements, pinned under ONE root `AtomUpdateAussage`:
             * `VergleicheTauscheAussage`: a compare-and-swap reports success exactly when the value read is the
               expected value; success writes the new value and records an update, failure records a read and writes
               back the value read. The model carries the success report as the boolean `vergleicheErfolg` of the
               value read and the expected value; the value bound into the frame is the value read in both cases.
             * `HoleUndAddiereAussage`: a fetch-and-add writes the sum of the value read and the operand and records
               an update; the frame binds the value read at the declared type, and a value outside that type's range
               halts the frame with `ungueltigerWert` (an overflow written by an earlier update is caught here).
             * `TauscheAussage`: an exchange writes the operand and binds the value read -- the old value -- into the
               frame.
             Each statement has a satisfiability lemma (the antecedents hold jointly in a represented instruction)
             and a non-triviality lemma (the other changes of the model violate the analogous statement, so the
             guarantee is tied to the change the instruction names and the checker has something to refuse).
             The statements are light: they are decided by the definitions of `Aenderung`, `Zugriffsform.uebertrag`
             and `Rahmen.bindeGelesen`, not by the graph-level duties `ZugriffBestimmtAussage` /
             `ZugriffKomponierbarAussage` of `Aussagen.lean`, which stay open. Nothing in `Aussagen.lean` changes.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Form

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Speicher (Art Modus)

/-- **The success report of a compare-and-swap.** It is `true` exactly when the value read equals the value the
    instruction expected. The model carries no separate success temporary: the report is a boolean over the value
    the memory returned and the operand of the instruction. -/
def vergleicheErfolg (erwartet gelesen : Int) : Bool := decide (gelesen = erwartet)

/-- **Success and failure of a compare-and-swap.** On success the update writes the operand and records an update
    event; on failure it records a read event and writes back the value read, so nothing changes. -/
def VergleicheTauscheAussage : Prop :=
  ∀ (erwartet neu gelesen : Int),
    (gelesen = erwartet →
      vergleicheErfolg erwartet gelesen = true ∧
        Aenderung.schreibt (.vergleiche erwartet) gelesen neu = neu ∧
        Aenderung.art (.vergleiche erwartet) gelesen = .rmw) ∧
    (gelesen ≠ erwartet →
      vergleicheErfolg erwartet gelesen = false ∧
        Aenderung.schreibt (.vergleiche erwartet) gelesen neu = gelesen ∧
        Aenderung.art (.vergleiche erwartet) gelesen = .lesen)

/-- The compare-and-swap statement holds by the two branches of `Aenderung.schreibt` and `Aenderung.art`. -/
theorem vergleicheTausche : VergleicheTauscheAussage := by
  intro erwartet neu gelesen
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simp only [vergleicheErfolg, decide_eq_true_eq, h]
    · simp only [Aenderung.schreibt, h, ↓reduceIte]
    · simp only [Aenderung.art, h, ↓reduceIte]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simp only [vergleicheErfolg, decide_eq_false_iff_not]
      exact h
    · simp only [Aenderung.schreibt, h, ↓reduceIte]
    · simp only [Aenderung.art, h, ↓reduceIte]

/-- **The premises of the compare-and-swap statement hold jointly**: the model represents both a success and a
    failure, with the success report in each case. -/
theorem vergleicheTausche_erfuellbar :
    (∃ (erwartet neu gelesen : Int), gelesen = erwartet ∧ vergleicheErfolg erwartet gelesen = true) ∧
      (∃ (erwartet neu gelesen : Int), gelesen ≠ erwartet ∧ vergleicheErfolg erwartet gelesen = false) := by
  refine ⟨⟨1, 2, 1, rfl, rfl⟩, ⟨1, 2, 3, ?_, rfl⟩⟩
  omega

/-- **The compare-and-swap statement is not trivial.** The plain exchange is a change the model represents and it
    writes the operand even when the value read differs from the expected value: on a failure it would behave like
    a success. The change named by the instruction is what makes the guarantee hold. -/
theorem vergleicheTausche_nichtTrivial :
    ∃ (erwartet neu gelesen : Int), gelesen ≠ erwartet ∧
      Aenderung.schreibt .tausche gelesen neu = neu ∧ Aenderung.art .tausche gelesen = .rmw := by
  refine ⟨1, 2, 3, ?_, rfl, rfl⟩
  omega

/-- **Fetch-and-add writes the sum and keeps the declared type range.** The update writes `gelesen + betrag` and
    records an update event. The frame binds the value read at the declared integer type: inside the type's range
    the frame continues, outside it the frame halts with `ungueltigerWert` -- this is where an overflow written by an
    earlier update is caught. -/
def HoleUndAddiereAussage : Prop :=
  ∀ (gelesen betrag lo hi : Int) (r : Rahmen) (ziel : Nat),
    Aenderung.schreibt .addiere gelesen betrag = gelesen + betrag ∧
      Aenderung.art .addiere gelesen = .rmw ∧
        (lo ≤ gelesen ∧ gelesen ≤ hi →
          ((.holeUndAddiere ziel 0 0 0 (.int lo hi) .sc : Zugriffsform).uebertrag r gelesen).stopp = r.stopp) ∧
        (¬ (lo ≤ gelesen ∧ gelesen ≤ hi) →
          ((.holeUndAddiere ziel 0 0 0 (.int lo hi) .sc : Zugriffsform).uebertrag r gelesen).stopp =
            some (Abschluss.ungueltigerWert))

/-- The fetch-and-add statement holds by the sum of `Aenderung.schreibt` and the bound check of `wertIn`. -/
theorem holeUndAddiere : HoleUndAddiereAussage := by
  intro gelesen betrag lo hi r ziel
  refine ⟨rfl, rfl, ?_⟩
  simp only [Zugriffsform.uebertrag]
  constructor
  · intro h
    have h' : lo ≤ (Zahl.literal gelesen).wert ∧ (Zahl.literal gelesen).wert ≤ hi := by
      simpa only [Zahl.literal] using h
    simp only [Rahmen.bindeGelesen, wertIn, wertAls, dif_pos h', Option.map_some, Rahmen.schreibe]
    rfl
  · intro h
    have h' : ¬ (lo ≤ (Zahl.literal gelesen).wert ∧ (Zahl.literal gelesen).wert ≤ hi) := by
      simpa only [Zahl.literal] using h
    simp only [Rahmen.bindeGelesen, wertIn, wertAls, dif_neg h', Option.map_none, Rahmen.halt]

/-- **The premises of the fetch-and-add statement hold jointly**: the model represents a read inside the declared
    type and a read outside it. -/
theorem holeUndAddiere_erfuellbar :
    (∃ (gelesen lo hi : Int), lo ≤ gelesen ∧ gelesen ≤ hi) ∧
      (∃ (gelesen lo hi : Int), ¬ (lo ≤ gelesen ∧ gelesen ≤ hi)) := by
  refine ⟨⟨1, 0, 2, ?_⟩, ⟨3, 0, 2, ?_⟩⟩ <;> omega

/-- **The fetch-and-add statement is not trivial.** The plain exchange is a change the model represents and it
    writes its operand instead of the sum; a fetch-and-add lowered to an exchange would lose the addition. -/
theorem holeUndAddiere_nichtTrivial :
    ∃ (gelesen betrag : Int), Aenderung.schreibt .tausche gelesen betrag ≠ gelesen + betrag := by
  refine ⟨1, 2, ?_⟩
  simp only [Aenderung.schreibt]
  omega

/-- **Exchange delivers the old value.** The update writes the operand and records an update event; the frame
    transfer is the binding of the value read, which is the value the cell held before the step. -/
def TauscheAussage : Prop :=
  ∀ (gelesen neu : Int) (ziel : Nat) (typ : Ty .value) (r : Rahmen),
    Aenderung.schreibt .tausche gelesen neu = neu ∧
      Aenderung.art .tausche gelesen = .rmw ∧
        ((.tausche ziel 0 0 0 typ .sc : Zugriffsform).uebertrag r gelesen) = r.bindeGelesen ziel typ gelesen

/-- The exchange statement holds by the definitions of the change and of the frame transfer. -/
theorem tausche : TauscheAussage := by
  intro gelesen neu ziel typ r
  exact ⟨rfl, rfl, rfl⟩

/-- **The premises of the exchange statement hold jointly**: the model represents a frame and an operand whose
    value differs from the value read, so the frame receives the read value and not the operand. -/
theorem tausche_erfuellbar :
    ∃ (gelesen neu : Int) (r : Rahmen) (ziel : Nat) (typ : Ty .value),
      gelesen ≠ neu ∧ ((.tausche ziel 0 0 0 typ .sc : Zugriffsform).uebertrag r gelesen) =
        r.bindeGelesen ziel typ gelesen := by
  refine ⟨1, 2, Rahmen.start [], 0, .int 0 2, ?_, rfl⟩
  omega

/-- **The exchange statement is not trivial.** The addition is a change the model represents and it writes the sum,
    so an exchange lowered to a fetch-and-add would write a value different from its operand. -/
theorem tausche_nichtTrivial :
    ∃ (gelesen betrag : Int), Aenderung.schreibt .addiere gelesen betrag ≠ betrag := by
  refine ⟨1, 2, ?_⟩
  simp only [Aenderung.schreibt]
  omega

/-- **The update statements of the access instructions**, pinned together under one root. -/
def AtomUpdateAussage : Prop :=
  VergleicheTauscheAussage ∧ HoleUndAddiereAussage ∧ TauscheAussage

/-- The update statements hold together. -/
theorem atomUpdateAussagen : AtomUpdateAussage :=
  ⟨vergleicheTausche, ⟨holeUndAddiere, tausche⟩⟩

end Gabbro.Core.Ast.Semantik
