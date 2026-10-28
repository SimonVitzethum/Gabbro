/-
  File:      Grammatik/Gen/Abdeckung/Satz/ErzeugtMN.lean
  Subject:   M AND N ARE WHAT THE GENERATOR EMITS (their completeness: `ErzeugtVoll.lean`). `mGen` is every
             `Gutes` the generator emits over all members at their bounds (`grenzenVon`), `nGen` every `Abgelehntes`; both
             are definitions the run evaluates and the proofs only reason
             about.

    * `mGen_gueltig`   every program of M is valid -- from the proof each `Gutes` carries, nothing is evaluated;
    * `nGen_abgelehnt` every program of N is refused -- from the proof each `Abgelehntes` carries;
    * `raumGut_mGen`   every valid program of the generator's space is in M (completeness of the stream and of
                       `erzeugeAus`), so a good cell that a valid program of the space has is witnessed in M;
    * `raumSchlecht_nGen` the same for the single-fault programs and N;
    * `tafel_erzeugt`  the cell table `Tafel` of `ZellenVoll.lean` for M and N, and with it Theorem 5 over every
                       program of the model (`erzeugt_hinreichend`), from one fact per cell: it occurs in the space
                       (`RaumGut`/`RaumSchlecht`) or no program can need it (`ZellenUnmoeglich.lean`).
-/
import Grammatik.Gen.Abdeckung.Satz.ErzeugtListe
import Grammatik.Gen.Abdeckung.Satz.ZellenVoll

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Adaequanz

/-- A program of a member that derives its floors, under the source lock family and starts `ws`, as a program of the
    source. -/
def Spez.einsatz (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn) (hax : z.axs = [])
    (hb : z.bodenOk P = true) : Einsatz where
  D := z.deklaration
  aufz := z.aufz
  zahlen := z.zahlen
  P := P
  S := z.sperreMax
  fs := z.fnListe
  ls := z.lockListe
  cs := z.traegerListe
  ws := z.wurzelnVon P ws
  hvoll := List.mem_finRange
  hls := List.mem_finRange
  hcs := fun
    | .inl t => List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_finRange _, rfl⟩)
    | .inr g => List.mem_append_right _ (List.mem_map.2 ⟨g, List.mem_finRange _, rfl⟩)
  hS L c := by
    simp only [Spez.sperreMax, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    intro _
    cases c with
    | inl t => exact List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_finRange _, rfl⟩)
    | inr g => exact List.mem_append_right _ (List.mem_map.2 ⟨g, List.mem_finRange _, rfl⟩)
  hBoden f := by
    have := (List.all_eq_true.1 hb) f (List.mem_finRange f)
    simpa using this
  keinAx a := by
    have := (show Fin z.axs.length from a).isLt
    simp only [hax, List.length_nil, Nat.not_lt_zero] at this

theorem Spez.einsatz_gueltig (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn)
    (hax : z.axs = []) (hb : z.bodenOk P = true) : (z.einsatz P ws hax hb).gueltig = z.gutB P z.sperreMax (z.wurzelnVon P ws) := rfl

/-! ## M and N: the generator's output -/

/-- The valid programs a member emits up to size `kmax`. -/
def Spez.mVon (z : Spez) (nb kmax nc : Nat) : List Einsatz :=
  (List.range (kmax + 1)).flatMap fun k => (z.erzeugtL (z.tabellenD nb) nc k).filterMap fun
    | .gut g => some (z.einsatz g.prog g.ws g.ohneAx g.boden)
    | .abgelehnt _ => none

/-- The refused programs a member emits up to size `kmax`. -/
def Spez.nVon (z : Spez) (nb kmax nc : Nat) : List Einsatz :=
  (List.range (kmax + 1)).flatMap fun k => (z.erzeugtL (z.tabellenD nb) nc k).filterMap fun
    | .gut _ => none
    | .abgelehnt a => some (z.einsatz a.prog a.ws a.ohneAx a.boden)

/-- **M**: every valid program the generator emits, over all members. -/
def mGen (nc : Nat) : List Einsatz :=
  (List.range mitglieder.length).flatMap fun i =>
    (mitglieder.getD i {}).mVon (grenzenVon i).1 (grenzenVon i).2 nc

/-- **N**: every refused program the generator emits, over all members. -/
def nGen (nc : Nat) : List Einsatz :=
  (List.range mitglieder.length).flatMap fun i =>
    (mitglieder.getD i {}).nVon (grenzenVon i).1 (grenzenVon i).2 nc

/-- **Every program of M is valid**: the proof is the field of the `Gutes` it came from. -/
theorem mGen_gueltig (nc : Nat) : ∀ m ∈ mGen nc, m.gueltig = true := by
  intro m hm
  simp only [mGen, Spez.mVon, List.mem_flatMap, List.mem_filterMap] at hm
  obtain ⟨_, _, _, _, e, _, he⟩ := hm
  cases e with
  | gut g => cases he; exact g.gueltig
  | abgelehnt _ => cases he

/-- **Every program of N is refused**: the proof is the field of the `Abgelehntes` it came from. -/
theorem nGen_abgelehnt (nc : Nat) : ∀ n ∈ nGen nc, n.gueltig = false := by
  intro n hn
  simp only [nGen, Spez.nVon, List.mem_flatMap, List.mem_filterMap] at hn
  obtain ⟨_, _, _, _, e, _, he⟩ := hn
  cases e with
  | gut _ => cases he
  | abgelehnt a => cases he; exact a.abgelehnt

end Gabbro.Grammatik.Gen
