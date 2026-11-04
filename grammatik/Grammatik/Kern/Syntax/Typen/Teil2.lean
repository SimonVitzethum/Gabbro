module

public import Grammatik.Kern.Syntax.Typen.Teil1
public import Grammatik.Kern.Syntax.Typen.Produkt

@[expose] public section

namespace Gabbro.Grammatik

theorem bytesZuZahl_bereich (bs : List Byte) :
    0 ≤ bytesZuZahl bs ∧ bytesZuZahl bs ≤ 256 ^ bs.length - 1 := by
  induction bs with
  | nil => simp only [bytesZuZahl, Std.le_refl, List.length_nil, Int.pow_zero, Int.sub_self, and_self]
  | cons b bs ih =>
      simp only [bytesZuZahl, List.length_cons]
      have h1 := b.lo_le; have h2 := b.le_hi
      have e : (256 : Int) ^ (bs.length + 1) = 256 ^ bs.length * 256 := Int.pow_succ _ _
      omega

/-- Eine Zahl in ihre `n` Bytes, kleinstes zuerst. -/
def zahlZuBytes : Nat → Int → List Byte
  | 0, _ => []
  | k + 1, z => ⟨z % 256, Int.emod_nonneg _ (by decide), by
                  have := Int.emod_lt_of_pos z (show (0:Int) < 256 by decide); omega⟩
                :: zahlZuBytes k (z / 256)

theorem zahlZuBytes_length (k : Nat) (z : Int) : (zahlZuBytes k z).length = k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp only [zahlZuBytes, List.length_cons, ih, Nat.add_left_cancel_iff]

/-! ## 5. Owner marks on the producer path -- the value-level application

    `Syntax.lean:149` carries `eigner_nie_erzeugt` -- no signature produces an
    owner mark -- and `SYNTAX.md:1625` books it as true but unapplied. This
    section applies it where the gap is (`D026`): the call step. `nachSig`
    (`Syntax.lean:226`) erases the consumed marks and appends the produced
    ones; mirrored here standalone (no imports) over plain marks, the theorem
    is: an owner mark held after the call was already held before it. The
    producer contributes nothing -- and from empty holdings, no call sequence
    ever holds one. That is the formal reason the checker refuses `owner`
    tables by name until the initial-holdings story stands.
-/

/-- An owner mark, as a number. Mirrors `D.Marke` cut down to identity. -/
abbrev OwnerMarke := Nat

/-- The producer side of one signature: what it consumes and what it claims
    to produce. Mirrors `S.konsumiert` / `S.produziert` (`Syntax.lean:88`). -/
structure OwnerSig where
  /-- Consumed marks `(mark, stage)`. -/
  konsumiert : List (OwnerMarke × Nat)
  /-- Produced marks `(mark, stage)`. -/
  erzeugt : List (OwnerMarke × Nat)
  /-- Which marks are owners (`∃ t, m ∈ D.eigner t`, folded). -/
  istEigner : OwnerMarke → Prop
  /-- The applied theorem: no signature produces an owner mark
      (`eigner_nie_erzeugt`, `Syntax.lean:149`). A premise here, as `Bau`
      fields are premises in `Geteilt.lean` -- the wiring instantiates it. -/
  eigner_nie_erzeugt : ∀ m s, istEigner m → (m, s) ∉ erzeugt

/-- One call step: erase the consumed, append the produced.
    Mirrors `nachSig` (`Syntax.lean:226`). -/
def ownerNachRuf (S : OwnerSig) (Λ : List (OwnerMarke × Nat)) :
    List (OwnerMarke × Nat) :=
  (S.konsumiert.foldl List.erase Λ) ++ S.erzeugt

/-- Erasing keeps only what was there. -/
theorem ownerErase_mem {Λ : List (OwnerMarke × Nat)} {k : List (OwnerMarke × Nat)}
    {x : OwnerMarke × Nat} (h : x ∈ k.foldl List.erase Λ) : x ∈ Λ := by
  induction k generalizing Λ with
  | nil => simpa using h
  | cons b k ih =>
      have h2 : x ∈ k.foldl List.erase (List.erase Λ b) := h
      exact List.mem_of_mem_erase (ih h2)

/-- **Owner marks survive only from the initial holdings.** An owner mark in
    the holdings after the call was in the holdings before it: the produced
    half cannot carry it (`eigner_nie_erzeugt`), and the erased half only
    keeps what was there. -/
theorem eigner_nachRuf_aus_anfang (S : OwnerSig) (Λ : List (OwnerMarke × Nat))
    (m : OwnerMarke) (s : Nat) (hE : S.istEigner m)
    (hmem : (m, s) ∈ ownerNachRuf S Λ) : (m, s) ∈ Λ := by
  unfold ownerNachRuf at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact ownerErase_mem hmem
  · exact absurd hmem (S.eigner_nie_erzeugt m s hE)

/-- A call sequence: the fold of single steps. -/
def ownerNachLaeufen : List OwnerSig → List (OwnerMarke × Nat) →
    List (OwnerMarke × Nat)
  | [], Λ => Λ
  | S :: Ss, Λ => ownerNachLaeufen Ss (ownerNachRuf S Λ)

/-- **Owner marks along a run come from the start.** Whatever a call sequence
    holds of an owner mark, the initial holdings held it. -/
theorem eigner_lauf_aus_anfang (Ss : List OwnerSig) (Λ : List (OwnerMarke × Nat))
    (m : OwnerMarke) (s : Nat)
    (hE : ∀ S ∈ Ss, S.istEigner m)
    (hmem : (m, s) ∈ ownerNachLaeufen Ss Λ) : (m, s) ∈ Λ := by
  induction Ss generalizing Λ with
  | nil => simpa [ownerNachLaeufen] using hmem
  | cons S Ss ih =>
      have h3 := ih (ownerNachRuf S Λ)
        (fun T hT => hE T (List.mem_cons_of_mem _ hT)) hmem
      exact eigner_nachRuf_aus_anfang S _ m s (hE S (by simp only [List.mem_cons, true_or])) h3

/-- **From empty holdings, no call sequence ever holds an owner mark.**
    With no initial holder there is no first mark to produce -- the sentence
    form of the `D026` refusal. -/
theorem eigner_aus_leer_nie (Ss : List OwnerSig)
    (m : OwnerMarke) (s : Nat) (hE : ∀ S ∈ Ss, S.istEigner m) :
    (m, s) ∉ ownerNachLaeufen Ss [] := by
  intro hmem
  have h0 := eigner_lauf_aus_anfang Ss [] m s hE hmem
  simp only [List.not_mem_nil] at h0

#print axioms Gabbro.Grammatik.eigner_nachRuf_aus_anfang
#print axioms Gabbro.Grammatik.eigner_lauf_aus_anfang
#print axioms Gabbro.Grammatik.eigner_aus_leer_nie

end Gabbro.Grammatik
