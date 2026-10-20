/-
  File:      Grammatik/Gen/Abdeckung/Satz/ErzeugtVoll.lean
  Subject:   M AND N ARE WHAT THE GENERATOR EMITS, and that they are complete is a theorem, not a test. `mGen` is every
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

/-- A program of a member, under a named lock family and starts, as a program of the model. -/
def Spez.einsatz (z : Spez) (P : Programm z.deklaration) (S : Sperrart) (ws : List z.deklaration.Fn) : Einsatz where
  D := z.deklaration
  aufz := z.aufz
  zahlen := z.zahlen
  P := P
  S := z.familie S
  fs := z.fnListe
  ls := z.lockListe
  cs := z.traegerListe
  ws := z.wurzelnVon P ws
  hvoll := List.mem_finRange
  hls := List.mem_finRange
  hcs := fun
    | .inl t => List.mem_append_left _ (List.mem_map.2 ⟨t, List.mem_finRange _, rfl⟩)
    | .inr g => List.mem_append_right _ (List.mem_map.2 ⟨g, List.mem_finRange _, rfl⟩)

theorem Spez.einsatz_gueltig (z : Spez) (P : Programm z.deklaration) (S : Sperrart) (ws : List z.deklaration.Fn) :
    (z.einsatz P S ws).gueltig = z.gutB P (z.familie S) (z.wurzelnVon P ws) := rfl

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
def Spez.mVon (z : Spez) (nb kmax nc : Nat) (treu : Bool) : List Einsatz :=
  (List.range (kmax + 1)).flatMap fun k => (z.erzeugtL (z.tabellenD nb treu) nc k).filterMap fun
    | .gut g => some (z.einsatz g.prog g.art g.ws)
    | .schlecht _ _ => none

/-- Every good cell of the list is in `er` (the good cells M witnesses). -/
def nurErreicht (er zs : List Zelle) : Bool := zs.all fun w => w.schlecht || er.contains w

/-- The single-fault programs a member emits up to size `kmax` that have exactly one bad cell and only good cells
    of `er`. -/
def Spez.nVon (z : Spez) (nb kmax nc : Nat) (treu : Bool) (er : List Zelle) : List Einsatz :=
  (List.range (kmax + 1)).flatMap fun k => (z.erzeugtL (z.tabellenD nb treu) nc k).filterMap fun
    | .gut _ => none
    | .schlecht _ s =>
      let e := z.einsatz s.prog s.art s.ws
      if (einzigSchlecht e.zellen).isSome && nurErreicht er e.zellen then some e else none

/-- **M**: every valid program the generator emits, over all members. -/
def mGen (nc : Nat) (treu : Bool) : List Einsatz :=
  (List.range mitglieder.length).flatMap fun i =>
    (mitglieder.getD i {}).mVon (grenzenVon i).1 (grenzenVon i).2 nc treu

/-- **N**: every emitted single-fault program with exactly one bad cell, over all members. -/
def nGen (nc : Nat) (treu : Bool) (er : List Zelle) : List Einsatz :=
  (List.range mitglieder.length).flatMap fun i =>
    (mitglieder.getD i {}).nVon (grenzenVon i).1 (grenzenVon i).2 nc treu er

/-- **Every program of M is valid**: the proof is the field of the `Gutes` it came from. -/
theorem mGen_gueltig (nc : Nat) (treu : Bool) : ∀ m ∈ mGen nc treu, m.gueltig = true := by
  intro m hm
  simp only [mGen, Spez.mVon, List.mem_flatMap, List.mem_filterMap] at hm
  obtain ⟨_, _, _, _, e, _, he⟩ := hm
  cases e with
  | gut g => cases he; exact g.gueltig
  | schlecht _ _ => cases he

/-- **Every program of N has exactly one bad cell.** -/
theorem nGen_einzig (nc : Nat) (treu : Bool) (er : List Zelle) :
    ∀ n ∈ nGen nc treu er, ∃ x, NurSchlecht Einsatz.Hat gutTafel n x := by
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
theorem nGen_erreicht (nc : Nat) (treu : Bool) (er : List Zelle) :
    ∀ n ∈ nGen nc treu er, ∀ w, n.Hat w → w.schlecht = false → w ∈ er := by
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

/-! ## The space of the generator, and its completeness -/

/-- The cell `x` occurs in a VALID program of member `z`'s space: bodies from its tables, size at most `kmax`. -/
def RaumGutIn (z : Spez) (nb kmax nc : Nat) (treu : Bool) (x : Zelle) : Prop :=
  ∃ k ≤ kmax, ∃ h ∈ @hautT z.deklaration z.aufz (z.tabellenD nb treu) k,
    ∃ P ∈ z.vertragsL nc h, ∃ p ∈ z.parameter,
      z.gutB P (z.familie p.1) (z.wurzelnVon P p.2) = true ∧ (z.einsatz P p.1 p.2).Hat x

/-- The cell `x` is the only bad cell of a program of member `z`'s space that exactly one component refuses. -/
def RaumSchlechtIn (z : Spez) (nb kmax nc : Nat) (treu : Bool) (er : List Zelle) (x : Zelle) : Prop :=
  ∃ k ≤ kmax, ∃ h ∈ @hautT z.deklaration z.aufz (z.tabellenD nb treu) k,
    ∃ P ∈ z.vertragsL nc h, ∃ p ∈ z.parameter, ∃ c : Fin 10,
      z.nurB c P (z.familie p.1) (z.wurzelnVon P p.2) = true ∧ einzigSchlecht (z.einsatz P p.1 p.2).zellen = some x ∧
      nurErreicht er (z.einsatz P p.1 p.2).zellen = true

/-- The cell `x` occurs in a VALID program of the generator's space (some member at its bounds). -/
def RaumGut (nc : Nat) (treu : Bool) (x : Zelle) : Prop :=
  ∃ i < mitglieder.length, RaumGutIn (mitglieder.getD i {}) (grenzenVon i).1 (grenzenVon i).2 nc treu x

/-- The cell `x` is the only bad cell of a single-fault program of the generator's space. -/
def RaumSchlecht (nc : Nat) (treu : Bool) (er : List Zelle) (x : Zelle) : Prop :=
  ∃ i < mitglieder.length, RaumSchlechtIn (mitglieder.getD i {}) (grenzenVon i).1 (grenzenVon i).2 nc treu er x

/-- **Completeness for M**: a good cell of a valid program of the space has a witness in M. -/
theorem raumGut_mGen {nc : Nat} {treu : Bool} {x : Zelle} (h : RaumGut nc treu x) : ∃ m ∈ mGen nc treu, m.Hat x := by
  obtain ⟨i, hi, k, hk, sk, hsk, P, hP, p, hp, hv, hx⟩ := h
  refine ⟨_, ?_, hx⟩
  simp only [mGen, Spez.mVon, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨i, hi, k, by omega, .gut ⟨P, p.1, p.2, hv⟩, ?_, rfl⟩
  exact mem_erzeugtL.2 ⟨sk, hsk, P, hP, p, hp, erzeugeAus_gut hv⟩

/-- **Completeness for N**: an isolated bad cell of the space has a witness in N. -/
theorem raumSchlecht_nGen {nc : Nat} {treu : Bool} {er : List Zelle} {x : Zelle} (h : RaumSchlecht nc treu er x) :
    ∃ n ∈ nGen nc treu er, NurSchlecht Einsatz.Hat gutTafel n x := by
  obtain ⟨i, hi, k, hk, sk, hsk, P, hP, p, hp, c, hn, hx, he⟩ := h
  refine ⟨_, ?_, einzigSchlecht_nur hx⟩
  simp only [nGen, Spez.nVon, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  refine ⟨i, hi, k, by omega, .schlecht c ⟨P, p.1, p.2, hn⟩, ?_, ?_⟩
  · exact mem_erzeugtL.2 ⟨sk, hsk, P, hP, p, hp, erzeugeAus_schlecht hn⟩
  · simp only [hx, he, Option.isSome_some, Bool.and_self, ite_true]

/-! ## The table, and Theorem 5 for the generated M and N -/

/-- **The generated M and N are complete** when every cell of the universe occurs in the space or cannot be needed:
    a good cell occurs in a valid program of the space or in no valid program at all; a bad cell is isolated in the
    space or always comes with another bad cell that is; and every good cell N may contain (`er`) is in the space. -/
theorem tafel_erzeugt (nc : Nat) (treu : Bool) (er : List Zelle)
    (hG : ∀ x ∈ zellAlle, x.schlecht = false → RaumGut nc treu x ∨ ∀ e : Einsatz, e.Hat x → e.gueltig = false)
    (hB : ∀ x ∈ zellAlle, x.schlecht = true → RaumSchlecht nc treu er x ∨
      ∀ e : Einsatz, e.Hat x → ∃ x', e.Hat x' ∧ x'.schlecht = true ∧ RaumSchlecht nc treu er x')
    (hE : ∀ w ∈ er, RaumGut nc treu w) :
    Tafel (mGen nc treu) (nGen nc treu er) where
  gut_m := mGen_gueltig nc treu
  gut x hx hs := (hG x hx hs).imp raumGut_mGen id
  schlecht x hx hs := (hB x hx hs).imp raumSchlecht_nGen fun h e he => by
    obtain ⟨x', h1, h2, h3⟩ := h e he
    obtain ⟨n, hn, hnx⟩ := raumSchlecht_nGen h3
    exact ⟨x', h1, h2, n, hn, hnx⟩
  gut_in_n n hn w hw hs := raumGut_mGen (hE w (nGen_erreicht nc treu er n hn w hw hs))

/-- **Theorem 5 for the generated test sets, over every program of the model.** -/
theorem erzeugt_hinreichend (nc : Nat) (treu : Bool) (er : List Zelle)
    (hG : ∀ x ∈ zellAlle, x.schlecht = false → RaumGut nc treu x ∨ ∀ e : Einsatz, e.Hat x → e.gueltig = false)
    (hB : ∀ x ∈ zellAlle, x.schlecht = true → RaumSchlecht nc treu er x ∨
      ∀ e : Einsatz, e.Hat x → ∃ x', e.Hat x' ∧ x'.schlecht = true ∧ RaumSchlecht nc treu er x')
    (hE : ∀ w ∈ er, RaumGut nc treu w)
    (φ : Zelle → Bool) (hM : ∀ m ∈ mGen nc treu, akzeptiert Einsatz.Hat φ m ↔ m.gueltig = true)
    (hN : ∀ n ∈ nGen nc treu er, akzeptiert Einsatz.Hat φ n ↔ n.gueltig = true) (e : Einsatz) :
    akzeptiert Einsatz.Hat φ e ↔ e.gueltig = true :=
  einsatz_hinreichend (tafel_erzeugt nc treu er hG hB hE) φ hM hN e

end Gabbro.Grammatik.Gen
