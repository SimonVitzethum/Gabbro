module

public import Core.Beobachtung.Fluss.Beschriftung.Flussregel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Beobachtung

/-- Finite rows for the temporary slots and local stack at each program counter.
    Positions outside a row are public. An omitted row is empty. -/
structure EndlicheBeschriftung where
  temp : Nat → List Etikett
  lokal : Nat → List Etikett
  ergebnis : Etikett := ∅

def etikettAn (row : List Etikett) (i : Nat) : Etikett :=
  row[i]?.getD ∅

def EndlicheBeschriftung.deutung (t : EndlicheBeschriftung) : Beschriftung where
  temp pc := etikettAn (t.temp pc)
  lokal pc := etikettAn (t.lokal pc)
  ergebnis := t.ergebnis

theorem etikettAn_ausserhalb {row : List Etikett} {i : Nat} (h : row.length ≤ i) :
    etikettAn row i = ∅ := by
  simp only [etikettAn, List.getElem?_eq_none h, Option.getD_none]

/-- A requirement of publicity can only fail inside the row of its conclusion.
    The offset accommodates local stack shifts at block and binding boundaries. -/
theorem endlich_oeffentlich_versetzt (row : List Etikett) (offset : Nat) (P : Nat → Prop) :
    (∀ i, P i → oeffentlich (etikettAn row (i + offset)) = true) ↔
      (∀ i ∈ List.range row.length, P i → oeffentlich (etikettAn row (i + offset)) = true) := by
  refine ⟨fun h i _ => h i, fun h i req => ?_⟩
  by_cases inside : i < row.length
  · exact h i (List.mem_range.mpr inside) req
  · rw [etikettAn_ausserhalb ((Nat.le_of_not_gt inside).trans (Nat.le_add_right i offset))]
    exact oeffentlich_leer

theorem endlich_oeffentlich_wenn (row : List Etikett) (P : Nat → Prop) :
    (∀ i, P i → oeffentlich (etikettAn row i) = true) ↔
      (∀ i ∈ List.range row.length, P i → oeffentlich (etikettAn row i) = true) :=
  endlich_oeffentlich_versetzt row 0 P

theorem endlich_oeffentlich_ausser (row : List Etikett) (dst : Nat) (P : Nat → Prop) :
    (∀ i, i ≠ dst → P i → oeffentlich (etikettAn row i) = true) ↔
      (∀ i ∈ List.range row.length, i ≠ dst → P i → oeffentlich (etikettAn row i) = true) := by
  simpa only [and_imp] using endlich_oeffentlich_wenn row (fun i => i ≠ dst ∧ P i)

theorem endlich_oeffentlich (row : List Etikett) :
    (∀ i, oeffentlich (etikettAn row i) = true) ↔
      (∀ i ∈ List.range row.length, oeffentlich (etikettAn row i) = true) := by
  simpa only [true_implies] using endlich_oeffentlich_wenn row (fun _ => True)

theorem fluss_zwei_ziele (a b : Nat) (P : Nat → Prop) :
    (∀ q, q = a ∨ q = b → P q) ↔ P a ∧ P b := by
  refine ⟨fun h => ⟨h a (.inl rfl), h b (.inr rfl)⟩, ?_⟩
  rintro ⟨ha, hb⟩ q (rfl | rfl)
  · exact ha
  · exact hb

/-- Use the existing per-form flow propositions. Their quantifiers range only over
    a finite row, a list of dependencies, or the two successors of a branch. -/
instance EndlicheBeschriftung.entscheidetBefehl (t : EndlicheBeschriftung) (pc : Nat) (f : Befehl) :
    Decidable (f.FlussRegel t.deutung pc) := by
  cases f <;>
    (conv =>
      arg 1
      simp only [Befehl.FlussRegel, Beschriftung.SchreibRegel, EndlicheBeschriftung.deutung,
        endlich_oeffentlich_ausser, endlich_oeffentlich_versetzt, endlich_oeffentlich_wenn,
        endlich_oeffentlich, fluss_zwei_ziele]) <;>
    infer_instance

theorem fragmentFluss_iff_beschraenkt (p : Fragment) (t : EndlicheBeschriftung) :
    p.FlussAkzeptiert t.deutung ↔
      ∀ pc ∈ List.range p.code.length,
        ∀ f ∈ p.code[pc]?, f.FlussRegel t.deutung pc := by
  constructor
  · intro h pc _ f hf
    exact h pc f (Option.mem_def.mp hf)
  · intro h pc f hf
    exact h pc (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hf).choose) f
      (Option.mem_def.mpr hf)

instance EndlicheBeschriftung.entscheidetFragment (t : EndlicheBeschriftung) (p : Fragment) :
    Decidable (p.FlussAkzeptiert t.deutung) :=
  decidable_of_iff _ (fragmentFluss_iff_beschraenkt p t).symm

def Fragment.pruefeFluss (p : Fragment) (t : EndlicheBeschriftung) : Bool :=
  decide (p.FlussAkzeptiert t.deutung)

def EndlicheFlussAussage : Prop :=
  ∀ (p : Fragment) (t : EndlicheBeschriftung),
    p.pruefeFluss t = true ↔ p.FlussAkzeptiert t.deutung

theorem endlicheFlussAussage_beweis : EndlicheFlussAussage :=
  fun _ _ => decide_eq_true_iff

theorem Fragment.pruefeFluss_lokal (p : Fragment) (platform : Katalog.Plattform)
    (t : EndlicheBeschriftung) (h : p.pruefeFluss t = true) :
    FlussLokal (p.beschriftet platform t.deutung) :=
  p.flussAkzeptiert_lokal platform t.deutung ((endlicheFlussAussage_beweis p t).mp h)

end Gabbro.Core.Ast.Semantik
