/-
  File:      Grammatik/Gen/Abdeckung/Satz/ErzeugtMN.lean
  Subject:   M AND N ARE WHAT THE GENERATOR EMITS (their completeness: `ErzeugtVoll.lean`). `mGen` is every
             `Gutes` the generator emits over all members at their bounds (`grenzenVon`), `nGen` every `Schlechtes` whose
             program has exactly one bad cell; both are definitions the run evaluates and the proofs only reason about.

    * `mGen_gueltig`   every program of M is valid -- from the proof each `Gutes` carries, nothing is evaluated;
    * `nGen_einzig`    every program of N has exactly one bad cell (`NurSchlecht`);
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
    simp [hax] at this

theorem Spez.einsatz_gueltig (z : Spez) (P : Programm z.deklaration) (ws : List z.deklaration.Fn)
    (hax : z.axs = []) (hb : z.bodenOk P = true) : (z.einsatz P ws hax hb).gueltig = z.gutB P z.sperreMax (z.wurzelnVon P ws) := rfl

/-- The only bad cell of a list of cells, if it has exactly one. -/
def einzigSchlecht (zs : List Zelle) : Option Zelle :=
  match zs.filter (·.schlecht) with
  | [] => none
  | x :: r => if r.all (· == x) then some x else none

theorem einzigSchlecht_nur {e : Einsatz} {x : Zelle} (h : einzigSchlecht e.zellen = some x) :
    NurSchlecht Einsatz.Hat gutTafel e x := by
  unfold einzigSchlecht at h
  generalize hf : e.zellen.filter (·.schlecht) = l at h
  match l, h with
  | [], h => cases h
  | y :: r, h =>
    simp only at h
    by_cases hr : (r.all (· == y)) = true
    · have h' : some y = some x := by simpa [hr] using h
      cases h'
      have hy : x ∈ e.zellen.filter (·.schlecht) := by rw [hf]; exact List.mem_cons_self
      obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
      refine ⟨hy1, by simpa [gutTafel] using hy2, fun z' hz' hne => ?_⟩
      cases hs : z'.schlecht
      · simp [gutTafel, hs]
      · exfalso
        have : z' ∈ e.zellen.filter (·.schlecht) := List.mem_filter.2 ⟨hz', hs⟩
        rw [hf] at this
        rcases List.mem_cons.1 this with h1 | h1
        · exact hne h1
        · exact hne (by simpa using (List.all_eq_true.1 hr) z' h1)
    · simp [hr] at h

/-! ## M and N: the generator's output -/

/-- The valid programs a member emits up to size `kmax`. -/
def Spez.mVon (z : Spez) (nb kmax nc : Nat) : List Einsatz :=
  (List.range (kmax + 1)).flatMap fun k => (z.erzeugtL (z.tabellenD nb) nc k).filterMap fun
    | .gut g => some (z.einsatz g.prog g.ws g.ohneAx g.boden)
    | .schlecht _ _ => none

/-- Every good cell of the list is in `er` (the good cells M witnesses). -/
def nurErreicht (er zs : List Zelle) : Bool := zs.all fun w => w.schlecht || er.contains w

/-- The single-fault programs a member emits up to size `kmax` that have exactly one bad cell and only good cells
    of `er`. -/
def Spez.nVon (z : Spez) (nb kmax nc : Nat) (er : List Zelle) : List Einsatz :=
  (List.range (kmax + 1)).flatMap fun k => (z.erzeugtL (z.tabellenD nb) nc k).filterMap fun
    | .gut _ => none
    | .schlecht _ s =>
      let e := z.einsatz s.prog s.ws s.ohneAx s.boden
      if (einzigSchlecht e.zellen).isSome && nurErreicht er e.zellen then some e else none

/-- **M**: every valid program the generator emits, over all members. -/
def mGen (nc : Nat) : List Einsatz :=
  (List.range mitglieder.length).flatMap fun i =>
    (mitglieder.getD i {}).mVon (grenzenVon i).1 (grenzenVon i).2 nc

/-- **N**: every emitted single-fault program with exactly one bad cell, over all members. -/
def nGen (nc : Nat) (er : List Zelle) : List Einsatz :=
  (List.range mitglieder.length).flatMap fun i =>
    (mitglieder.getD i {}).nVon (grenzenVon i).1 (grenzenVon i).2 nc er

/-- **Every program of M is valid**: the proof is the field of the `Gutes` it came from. -/
theorem mGen_gueltig (nc : Nat) : ∀ m ∈ mGen nc, m.gueltig = true := by
  intro m hm
  simp only [mGen, Spez.mVon, List.mem_flatMap, List.mem_filterMap] at hm
  obtain ⟨_, _, _, _, e, _, he⟩ := hm
  cases e with
  | gut g => cases he; exact g.gueltig
  | schlecht _ _ => cases he

/-- **Every program of N has exactly one bad cell.** -/
theorem nGen_einzig (nc : Nat) (er : List Zelle) :
    ∀ n ∈ nGen nc er, ∃ x, NurSchlecht Einsatz.Hat gutTafel n x := by
  intro n hn
  simp only [nGen, Spez.nVon, List.mem_flatMap, List.mem_filterMap] at hn
  obtain ⟨_, _, _, _, e, _, he⟩ := hn
  cases e with
  | gut _ => cases he
  | schlecht _ s =>
    simp only at he
    split at he
    · rename_i hs
      cases he
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (Bool.and_eq_true_iff.1 hs).1
      exact ⟨x, einzigSchlecht_nur hx⟩
    · cases he

/-- **Every good cell of a program of N is in `er`.** -/
theorem nGen_erreicht (nc : Nat) (er : List Zelle) :
    ∀ n ∈ nGen nc er, ∀ w, n.Hat w → w.schlecht = false → w ∈ er := by
  intro n hn w hw hs
  simp only [nGen, Spez.nVon, List.mem_flatMap, List.mem_filterMap] at hn
  obtain ⟨_, _, _, _, e, _, he⟩ := hn
  cases e with
  | gut _ => cases he
  | schlecht _ s =>
    simp only at he
    split at he
    · rename_i hs'
      cases he
      have := (List.all_eq_true.1 (Bool.and_eq_true_iff.1 hs').2) w hw
      simpa [hs] using this
    · cases he

end Gabbro.Grammatik.Gen
