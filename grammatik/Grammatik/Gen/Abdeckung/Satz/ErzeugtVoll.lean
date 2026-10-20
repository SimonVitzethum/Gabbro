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

/-- The cell `x` is the only bad cell of a program of member `z`'s space that exactly one component refuses, and every
    good cell of that program is in `er`. -/
def RaumSchlechtIn (z : Spez) (nb kmax nc : Nat) (er : List Zelle) (x : Zelle) : Prop :=
  ∃ k ≤ kmax, ∃ h ∈ @hautT z.deklaration z.aufz (z.tabellenD nb) k,
    ∃ P ∈ z.vertragsL nc h, ∃ ws ∈ z.parameter, ∃ hax : z.axs = [], ∃ hb : z.bodenOk P = true, ∃ c : Fin 10,
      z.nurB c P z.sperreMax (z.wurzelnVon P ws) = true ∧ einzigSchlecht (z.einsatz P ws hax hb).zellen = some x ∧
      nurErreicht er (z.einsatz P ws hax hb).zellen = true

/-- The cell `x` occurs in a VALID program of the generator's space (some member at its bounds). -/
def RaumGut (nc : Nat) (x : Zelle) : Prop :=
  ∃ i < mitglieder.length, RaumGutIn (mitglieder.getD i {}) (grenzenVon i).1 (grenzenVon i).2 nc x

/-- The cell `x` is the only bad cell of a single-fault program of the generator's space. -/
def RaumSchlecht (nc : Nat) (er : List Zelle) (x : Zelle) : Prop :=
  ∃ i < mitglieder.length, RaumSchlechtIn (mitglieder.getD i {}) (grenzenVon i).1 (grenzenVon i).2 nc er x

/-- **Completeness for M**: a good cell of a valid program of the space has a witness in M. -/
theorem raumGut_mGen {nc : Nat} {x : Zelle} (h : RaumGut nc x) : ∃ m ∈ mGen nc, m.Hat x := by
  obtain ⟨i, hi, k, hk, sk, hsk, P, hP, ws, hws, hax, hb, hv, hx⟩ := h
  refine ⟨_, ?_, hx⟩
  simp only [mGen, Spez.mVon, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨i, hi, k, by omega, .gut ⟨P, ws, hax, hb, hv⟩, ?_, rfl⟩
  exact mem_erzeugtL.2 ⟨sk, hsk, P, hP, ws, hws, erzeugeAus_gut hax hb hv⟩

/-- **Completeness for N**: an isolated bad cell of the space has a witness in N. -/
theorem raumSchlecht_nGen {nc : Nat} {er : List Zelle} {x : Zelle} (h : RaumSchlecht nc er x) :
    ∃ n ∈ nGen nc er, NurSchlecht Einsatz.Hat gutTafel n x := by
  obtain ⟨i, hi, k, hk, sk, hsk, P, hP, ws, hws, hax, hb, c, hn, hx, he⟩ := h
  refine ⟨_, ?_, einzigSchlecht_nur hx⟩
  simp only [nGen, Spez.nVon, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨i, hi, k, by omega, .schlecht c ⟨P, ws, hax, hb, hn⟩, ?_, ?_⟩
  · exact mem_erzeugtL.2 ⟨sk, hsk, P, hP, ws, hws, erzeugeAus_schlecht hax hb hn⟩
  · simp only [hx, he, Option.isSome_some, Bool.and_self, ite_true]

/-! ## The table, and Theorem 5 for the generated M and N -/

/-- **The generated M and N are complete** when every cell of the universe occurs in the space or cannot be needed:
    a good cell occurs in a valid program of the space or in no valid program at all; a bad cell is isolated in the
    space or always comes with another bad cell that is; and every good cell N may contain (`er`) is in the space. -/
theorem tafel_erzeugt (nc : Nat) (er : List Zelle)
    (hG : ∀ x ∈ zellAlle, x.schlecht = false → RaumGut nc x ∨ ∀ e : Einsatz, e.Hat x → e.gueltig = false)
    (hB : ∀ x ∈ zellAlle, x.schlecht = true → RaumSchlecht nc er x ∨
      ∀ e : Einsatz, e.Hat x → ∃ x', e.Hat x' ∧ x'.schlecht = true ∧ RaumSchlecht nc er x')
    (hE : ∀ w ∈ er, RaumGut nc w) :
    Tafel (mGen nc) (nGen nc er) where
  gut_m := mGen_gueltig nc
  gut x hx hs := (hG x hx hs).imp raumGut_mGen id
  schlecht x hx hs := (hB x hx hs).imp raumSchlecht_nGen fun h e he => by
    obtain ⟨x', h1, h2, h3⟩ := h e he
    obtain ⟨n, hn, hnx⟩ := raumSchlecht_nGen h3
    exact ⟨x', h1, h2, n, hn, hnx⟩
  gut_in_n n hn w hw hs := raumGut_mGen (hE w (nGen_erreicht nc er n hn w hw hs))

/-- **Theorem 5 for the generated test sets, over every program of the model.** -/
theorem erzeugt_hinreichend (nc : Nat) (er : List Zelle)
    (hG : ∀ x ∈ zellAlle, x.schlecht = false → RaumGut nc x ∨ ∀ e : Einsatz, e.Hat x → e.gueltig = false)
    (hB : ∀ x ∈ zellAlle, x.schlecht = true → RaumSchlecht nc er x ∨
      ∀ e : Einsatz, e.Hat x → ∃ x', e.Hat x' ∧ x'.schlecht = true ∧ RaumSchlecht nc er x')
    (hE : ∀ w ∈ er, RaumGut nc w)
    (φ : Zelle → Bool) (hM : ∀ m ∈ mGen nc, akzeptiert Einsatz.Hat φ m ↔ m.gueltig = true)
    (hN : ∀ n ∈ nGen nc er, akzeptiert Einsatz.Hat φ n ↔ n.gueltig = true) (e : Einsatz) :
    akzeptiert Einsatz.Hat φ e ↔ e.gueltig = true :=
  einsatz_hinreichend (tafel_erzeugt nc er hG hB hE) φ hM hN e

end Gabbro.Grammatik.Gen
