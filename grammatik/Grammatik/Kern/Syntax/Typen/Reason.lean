module

public import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

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
  ⟨r.codes.get i, fun _ => List.get_mem r.codes i⟩

/-- Recover the case index only when the declaration is closed. -/
def index {r : ReasonSpec} (h : r.closed = true) (v : ReasonVal r) : Fin r.codes.length :=
  ⟨r.codes.idxOf v.1, List.idxOf_lt_length_of_mem (v.2 h)⟩

@[simp] theorem known_index {r : ReasonSpec} (h : r.closed = true) (v : ReasonVal r) :
    known r (index h v) = v := by
  apply Subtype.ext
  exact List.idxOf_get _

@[simp] theorem index_known {r : ReasonSpec} (h : r.closed = true) (i : Fin r.codes.length) :
    index h (known r i) = i := by
  apply r.distinct.injective_get
  exact congrArg Subtype.val (known_index h (known r i))

/-- The compact closed representation is a bijection with declared case indices. -/
def closedEquiv (r : ReasonSpec) (h : r.closed = true) : Fin r.codes.length ≃ ReasonVal r where
  toFun := known r
  invFun := index h
  left_inv := index_known h
  right_inv := known_index h

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

end ReasonVal
end Gabbro.Grammatik
