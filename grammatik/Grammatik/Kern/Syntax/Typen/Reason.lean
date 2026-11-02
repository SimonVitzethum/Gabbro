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
end Gabbro.Grammatik
