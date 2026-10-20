/-
  File:      Grammatik/Gen/Abdeckung/Satz/ErzeugtVoll.lean
  Subject:   M AND N ARE COMPLETE, a theorem and not a test: the space of the generator (`RaumGut`, `RaumSchlecht`),
             every valid program of the space is in M (`raumGut_mGen`), every isolated single-fault program in N
             (`raumSchlecht_nGen`), and the cell table `Tafel` with Theorem 5 over every program of the source
             (`tafel_erzeugt`, `erzeugt_hinreichend`) from one fact per cell.
-/
import Grammatik.Gen.Abdeckung.Satz.ErzeugtMN

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Adaequanz

/-! ## The space of the generator, and its completeness -/

/-- The cell `x` occurs in a VALID program of member `z`'s space: bodies from its tables, size at most `kmax`. -/
def RaumGutIn (z : Spez) (nb kmax nc : Nat) (x : Zelle) : Prop :=
  ∃ k ≤ kmax, ∃ h ∈ @hautT z.deklaration z.aufz (z.tabellenD nb) k,
    ∃ P ∈ z.vertragsL nc h, ∃ ws ∈ z.parameter, ∃ hax : z.axs = [], ∃ hb : z.bodenOk P = true,
      z.gutB P z.sperreMax (z.wurzelnVon P ws) = true ∧ (z.einsatz P ws hax hb).Hat x

/-- Every cell of `zs` is in `B` or is a good cell of `er`. -/
def gedeckt (er B zs : List Zelle) : Bool := zs.all fun w => B.contains w || (!w.schlecht && er.contains w)

/-- A refused program of member `z`'s space each of whose cells is in `B` or a good cell of `er`. -/
def RaumSchlechtIn (z : Spez) (nb kmax nc : Nat) (er B : List Zelle) : Prop :=
  ∃ k ≤ kmax, ∃ h ∈ @hautT z.deklaration z.aufz (z.tabellenD nb) k,
    ∃ P ∈ z.vertragsL nc h, ∃ ws ∈ z.parameter, ∃ hax : z.axs = [], ∃ hb : z.bodenOk P = true,
      z.gutB P z.sperreMax (z.wurzelnVon P ws) = false ∧ gedeckt er B (z.einsatz P ws hax hb).zellen = true

/-- The cell `x` occurs in a VALID program of the generator's space (some member at its bounds). -/
def RaumGut (nc : Nat) (x : Zelle) : Prop :=
  ∃ i < mitglieder.length, RaumGutIn (mitglieder.getD i {}) (grenzenVon i).1 (grenzenVon i).2 nc x

/-- A refused program of the generator's space each of whose cells is in `B` or a good cell of `er`. -/
def RaumSchlecht (nc : Nat) (er B : List Zelle) : Prop :=
  ∃ i < mitglieder.length, RaumSchlechtIn (mitglieder.getD i {}) (grenzenVon i).1 (grenzenVon i).2 nc er B

/-- **Completeness for M**: a good cell of a valid program of the space has a witness in M. -/
theorem raumGut_mGen {nc : Nat} {x : Zelle} (h : RaumGut nc x) : ∃ m ∈ mGen nc, m.Hat x := by
  obtain ⟨i, hi, k, hk, sk, hsk, P, hP, ws, hws, hax, hb, hv, hx⟩ := h
  refine ⟨_, ?_, hx⟩
  simp only [mGen, Spez.mVon, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨i, hi, k, by omega, .gut ⟨P, ws, hax, hb, hv⟩, ?_, rfl⟩
  exact mem_erzeugtL.2 ⟨sk, hsk, P, hP, ws, hws, erzeugeAus_gut hax hb hv⟩

/-- **Completeness for N**: such a refused program of the space is in N. -/
theorem raumSchlecht_nGen {nc : Nat} {er B : List Zelle} (h : RaumSchlecht nc er B) :
    ∃ n ∈ nGen nc, ∀ w, n.Hat w → w ∈ B ∨ (w.schlecht = false ∧ w ∈ er) := by
  obtain ⟨i, hi, k, hk, sk, hsk, P, hP, ws, hws, hax, hb, hv, hg⟩ := h
  refine ⟨(mitglieder.getD i {}).einsatz P ws hax hb, ?_, fun w hw => ?_⟩
  · simp only [nGen, Spez.nVon, List.mem_flatMap, List.mem_filterMap, List.mem_range]
    exact ⟨i, hi, k, by omega, .abgelehnt ⟨P, ws, hax, hb, hv⟩,
      mem_erzeugtL.2 ⟨sk, hsk, P, hP, ws, hws, erzeugeAus_abgelehnt hax hb hv⟩, rfl⟩
  · have := (List.all_eq_true.1 hg) w hw
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
    exact this

/-! ## The table, and Theorem 5 for the generated M and N -/

/-- Every good cell of the universe occurs in a valid program of the space, or in no valid program. -/
def GutGedeckt (nc : Nat) : Prop :=
  ∀ x ∈ zellAlle, x.schlecht = false → RaumGut nc x ∨ ∀ e : Einsatz, e.Hat x → e.gueltig = false

/-- Every program with a bad cell of the universe has, among its own cells, the bad cells of a refused program of the
    space whose good cells are in `er`. -/
def SchlechtGedeckt (nc : Nat) (er : List Zelle) : Prop :=
  ∀ x ∈ zellAlle, x.schlecht = true → ∀ e : Einsatz, e.Hat x →
    ∃ B : List Zelle, (∀ w ∈ B, e.Hat w) ∧ RaumSchlecht nc er B

/-- **The generated M and N are complete** when the good cells and the bad cells are covered and every good cell N
    may contain (`er`) is in the space. -/
theorem tafel_erzeugt (nc : Nat) (er : List Zelle) (hG : GutGedeckt nc) (hB : SchlechtGedeckt nc er)
    (hE : ∀ w ∈ er, RaumGut nc w) : Tafel (mGen nc) (nGen nc) where
  gut_m := mGen_gueltig nc
  gut x hx hs := (hG x hx hs).imp raumGut_mGen id
  n_schlecht := nGen_abgelehnt nc
  schlecht x hx hs e he := by
    obtain ⟨B, hBe, hR⟩ := hB x hx hs e he
    obtain ⟨n, hn, hnB⟩ := raumSchlecht_nGen hR
    refine ⟨n, hn, fun w hw => ?_⟩
    rcases hnB w hw with h | ⟨_, h⟩
    · exact Or.inl (hBe w h)
    · exact Or.inr (raumGut_mGen (hE w h))

/-- **Theorem 5 for the generated test sets, over every program of the model.** -/
theorem erzeugt_hinreichend (nc : Nat) (er : List Zelle) (hG : GutGedeckt nc) (hB : SchlechtGedeckt nc er)
    (hE : ∀ w ∈ er, RaumGut nc w)
    (φ : Zelle → Bool) (hM : ∀ m ∈ mGen nc, akzeptiert Einsatz.Hat φ m ↔ m.gueltig = true)
    (hN : ∀ n ∈ nGen nc, akzeptiert Einsatz.Hat φ n ↔ n.gueltig = true) (e : Einsatz) :
    akzeptiert Einsatz.Hat φ e ↔ e.gueltig = true :=
  einsatz_hinreichend (tafel_erzeugt nc er hG hB hE) φ hM hN e

end Gabbro.Grammatik.Gen
