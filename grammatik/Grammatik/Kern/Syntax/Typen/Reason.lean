module


@[expose] public section

namespace Gabbro.Grammatik

/-- Source reason codes occupy the complete unsigned 128-bit domain. -/
abbrev ReasonCode := Fin (2 ^ 128)

/-- A resolved reason declaration. Identity, code order and openness are all semantic. -/
structure ReasonSpec where
  name : Nat
  codes : List ReasonCode
  closed : Bool
  distinct : codes.Nodup
  deriving DecidableEq, Repr

/-- An open declaration admits unknown codes; a closed one admits only its declared codes. -/
def ReasonVal (r : ReasonSpec) := { c : ReasonCode // r.closed = true → c ∈ r.codes }

namespace ReasonVal

/-- Source construction uses a declared case, including for an open declaration. -/
def known (r : ReasonSpec) (i : Fin r.codes.length) : ReasonVal r :=
  ⟨r.codes[i.val], fun _ => List.getElem_mem i.isLt⟩

/-- Recover the case index only when the declaration is closed. -/
def index {r : ReasonSpec} (h : r.closed = true) (v : ReasonVal r) : Fin r.codes.length :=
  ⟨r.codes.idxOf v.1, List.idxOf_lt_length_of_mem (v.2 h)⟩

@[simp] theorem known_index {r : ReasonSpec} (h : r.closed = true) (v : ReasonVal r) :
    known r (index h v) = v := by
  apply Subtype.ext
  exact List.getElem_idxOf _

@[simp] theorem index_known {r : ReasonSpec} (h : r.closed = true) (i : Fin r.codes.length) :
    index h (known r i) = i := by
  apply Fin.ext
  have h1 := congrArg Subtype.val (known_index h (known r i))
  exact r.distinct.eq_of_getElem_eq _ _ h1

/-- The compact closed representation is a bijection with declared case indices. -/
theorem closed_bijektiv (r : ReasonSpec) (h : r.closed = true) :
    Function.LeftInverse (index h) (known r) ∧ Function.RightInverse (index h) (known r) :=
  ⟨index_known h, known_index h⟩

/-- The foreign boundary checks bounds before checking closed membership. -/
def decode (r : ReasonSpec) (n : Int) : Option (ReasonVal r) :=
  if hb : 0 ≤ n ∧ n < (2 ^ 128 : Nat) then
    let c : ReasonCode := ⟨n.toNat, by omega⟩
    if hc : r.closed = true → c ∈ r.codes then some ⟨c, hc⟩ else none
  else none

/-- Forwarding preserves the complete code, including unknown open codes. -/
theorem decode_complete {r : ReasonSpec} (v : ReasonVal r) :
    decode r (v.1.val : Int) = some v := by
  unfold decode
  rw [dif_pos ⟨Int.natCast_nonneg _, by have := v.1.isLt; omega⟩]
  simp only [Int.toNat_natCast]
  rw [dif_pos v.2]
  exact congrArg some (Subtype.ext (Fin.ext rfl))

theorem decode_bounded {r : ReasonSpec} {n : Int} {v : ReasonVal r}
    (h : decode r n = some v) : 0 ≤ n ∧ n < (2 ^ 128 : Nat) := by
  unfold decode at h
  split at h
  · assumption
  · cases h

/-- Same-declaration equality observes the opaque reason code. -/
def equal {r : ReasonSpec} (a b : ReasonVal r) : Bool := decide (a.1 = b.1)

theorem equal_iff {r : ReasonSpec} (a b : ReasonVal r) : equal a b = true ↔ a = b := by
  simp only [equal, decide_eq_true_eq]
  exact ⟨Subtype.ext, congrArg Subtype.val⟩

/-- Openness, rather than the number of declared cases, decides the empty-open boundary. -/
def inhabitedB (r : ReasonSpec) : Bool := !r.closed || !r.codes.isEmpty

theorem inhabitedB_iff (r : ReasonSpec) : inhabitedB r = true ↔ Nonempty (ReasonVal r) := by
  cases hc : r.closed with
  | false =>
    constructor
    · intro _
      exact ⟨⟨⟨0, by decide⟩, by intro h; rw [hc] at h; cases h⟩⟩
    · intro _
      simp only [inhabitedB, hc, Bool.not_false, Bool.true_or]
  | true =>
    cases hs : r.codes with
    | nil =>
      constructor
      · intro h
        simp only [inhabitedB, hc, hs, List.isEmpty_nil, Bool.not_true,
          Bool.false_or, Bool.false_eq_true] at h
      · rintro ⟨v⟩
        have hv : v.1 ∈ r.codes := v.2 hc
        generalize v.1 = x at hv
        rw [hs] at hv
        cases hv
    | cons c cs =>
      constructor
      · intro _
        exact ⟨⟨c, by intro _; rw [hs]; exact List.mem_cons_self⟩⟩
      · intro _
        simp only [inhabitedB, hc, hs, List.isEmpty_cons, Bool.not_false,
          Bool.not_true, Bool.false_or]

end ReasonVal

namespace ReasonSpec

/-- Widening the anonymous indices preserves their distinctness. -/
theorem ofCount_codes_distinct (n : Nat) (h : n ≤ 2 ^ 128) :
    ((List.finRange n).map (Fin.castLE h)).Nodup :=
  List.Pairwise.map (Fin.castLE h)
    (fun _ _ hne he => hne (Fin.ext (by simpa only [Fin.val_castLE] using congrArg Fin.val he)))
    (List.nodup_finRange n)

/-- The legacy count descriptor has anonymous codes `0 .. n-1` and identity `n`.
    The explicit bound is necessary: distinct u128 codes cannot represent every `Nat`.
    This identity is only a migration convention, not a source declaration's identity.
    In particular, `ofCount 0 h` is an empty closed descriptor, NOT `none` (no channel).
    How the legacy zero channel maps to that distinction remains an owner decision. -/
def ofCount (n : Nat) (h : n ≤ 2 ^ 128) : ReasonSpec :=
  { name := n
    codes := (List.finRange n).map (Fin.castLE h)
    closed := true
    distinct := (ofCount_codes_distinct n h) }

theorem ofCount_length (n : Nat) (h : n ≤ 2 ^ 128) :
    (ofCount n h).codes.length = n := by
  simp only [ofCount, List.length_map, List.length_finRange]

theorem ofCount_closed (n : Nat) (h : n ≤ 2 ^ 128) :
    (ofCount n h).closed = true := rfl

end ReasonSpec

namespace ReasonVal

/-- Embed an old case index as the corresponding anonymous reason code. -/
def ofCountVon {n : Nat} (h : n ≤ 2 ^ 128) (i : Fin n) :
    ReasonVal (ReasonSpec.ofCount n h) :=
  known _ (Fin.cast (ReasonSpec.ofCount_length n h).symm i)

/-- Recover the old index from an anonymous closed reason. -/
def ofCountNach {n : Nat} (h : n ≤ 2 ^ 128)
    (v : ReasonVal (ReasonSpec.ofCount n h)) : Fin n :=
  Fin.cast (ReasonSpec.ofCount_length n h) (index (ReasonSpec.ofCount_closed n h) v)

@[simp] theorem ofCountNach_ofCountVon {n : Nat} (h : n ≤ 2 ^ 128) (i : Fin n) :
    ofCountNach h (ofCountVon h i) = i := by
  apply Fin.ext
  have hv := congrArg Fin.val
    (index_known (ReasonSpec.ofCount_closed n h)
      (Fin.cast (ReasonSpec.ofCount_length n h).symm i))
  simpa only [ofCountNach, ofCountVon, Fin.val_cast] using hv

@[simp] theorem ofCountVon_ofCountNach {n : Nat} (h : n ≤ 2 ^ 128)
    (v : ReasonVal (ReasonSpec.ofCount n h)) :
    ofCountVon h (ofCountNach h v) = v := by
  unfold ofCountVon ofCountNach
  have hc : Fin.cast (ReasonSpec.ofCount_length n h).symm
      (Fin.cast (ReasonSpec.ofCount_length n h) (index (ReasonSpec.ofCount_closed n h) v)) =
        index (ReasonSpec.ofCount_closed n h) v := Fin.ext rfl
  rw [hc]
  exact known_index (ReasonSpec.ofCount_closed n h) v

/-- The future closed-match dispatcher recovers exactly the legacy arm index. -/
theorem ofCount_index {n : Nat} (h : n ≤ 2 ^ 128)
    (v : ReasonVal (ReasonSpec.ofCount n h)) :
    index (ReasonSpec.ofCount_closed n h) v =
      Fin.cast (ReasonSpec.ofCount_length n h).symm (ofCountNach h v) :=
  Fin.ext rfl

/-- Equality of anonymous reasons is exactly decidable equality of old indices. -/
theorem ofCountVon_eq_iff {n : Nat} (h : n ≤ 2 ^ 128) (i j : Fin n) :
    ofCountVon h i = ofCountVon h j ↔ i = j := by
  constructor
  · intro he
    have hi := congrArg (ofCountNach h) he
    rw [ofCountNach_ofCountVon, ofCountNach_ofCountVon] at hi
    exact hi
  · intro he
    exact congrArg (ofCountVon h) he

/-- An empty closed descriptor has no value; this does not identify it with no channel. -/
theorem ofCount_zero_elim (h : 0 ≤ (2 ^ 128 : Nat))
    (v : ReasonVal (ReasonSpec.ofCount 0 h)) : False :=
  Fin.elim0 (ofCountNach h v)

end ReasonVal

/-- The empty descriptor is closed and has no declared codes. -/
theorem reason_ofCount_zero_zeuge :
    (ReasonSpec.ofCount 0 (by decide)).codes = [] ∧
      (ReasonSpec.ofCount 0 (by decide)).closed = true := ⟨rfl, rfl⟩

/-- The singleton embeds its sole case as code zero and recovers index zero. -/
theorem reason_ofCount_one_zeuge :
    (ReasonVal.ofCountVon (n := 1) (by decide) ⟨0, by decide⟩).1.val = 0 ∧
      (ReasonVal.ofCountNach (n := 1) (by decide)
        (ReasonVal.ofCountVon (n := 1) (by decide) ⟨0, by decide⟩)).val = 0 := by decide

/-- Three anonymous cases preserve code order and the last case's index. -/
theorem reason_ofCount_three_zeuge :
    ((ReasonSpec.ofCount 3 (by decide)).codes.map Fin.val) = [0, 1, 2] ∧
      (ReasonVal.ofCountNach (n := 3) (by decide)
        (ReasonVal.ofCountVon (n := 3) (by decide) ⟨2, by decide⟩)).val = 2 := by decide

end Gabbro.Grammatik
