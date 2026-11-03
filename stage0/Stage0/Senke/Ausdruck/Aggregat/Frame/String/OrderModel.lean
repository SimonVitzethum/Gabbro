/- Byte-list order and the descending presence/byte-key scan. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik

/-- Present bytes have positive keys; absent bytes have key zero. -/
def keys (bs : List Int) : List Nat := bs.map fun b => b.toNat + 1

def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (a == b && lexLt as bs)

/-- The exact bridge from canonical byte-list order to the scan's positive keys. -/
theorem bytesLt_keys : ∀ (as bs : List Int),
    (∀ a ∈ as, 0 ≤ a) → (∀ b ∈ bs, 0 ≤ b) → bytesLt as bs = lexLt (keys as) (keys bs) := by
  intro as
  induction as with
  | nil => intro bs _ _; cases bs <;> rfl
  | cons a as ih =>
    intro bs ha hb
    cases bs with
    | nil => rfl
    | cons b bs =>
      have a0 := ha a (by simp)
      have b0 := hb b (by simp)
      have lt : decide (a < b) = decide (a.toNat + 1 < b.toNat + 1) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        omega
      have eq : (a == b) = (a.toNat + 1 == b.toNat + 1) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        omega
      simp only [bytesLt, keys, List.map_cons, lexLt]
      rw [lt, eq, ih bs (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx]))]

def keyAt (bs : List Int) (i : Nat) : Nat := ((keys bs)[i]?).getD 0

def scanStep (a b : Nat) (suffix : Bool) : Bool := decide (a < b) || (a == b && suffix)

/-- The semantic counterpart of the emitted descending scan, including its suffix input. -/
def keyScan : Nat → List Int → List Int → Bool → Bool
  | 0, _, _, r => r
  | k + 1, as, bs, r => keyScan k as bs (scanStep (keyAt as k) (keyAt bs k) r)

@[simp] theorem keyAt_drop (as : List Int) (k : Nat) : keyAt (as.drop 1) k = keyAt as (k + 1) := by
  cases as <;> simp [keyAt, keys]

theorem keyScan_head (k : Nat) (as bs : List Int) (r : Bool) :
    keyScan (k + 1) as bs r =
      scanStep (keyAt as 0) (keyAt bs 0) (keyScan k (as.drop 1) (bs.drop 1) r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [keyScan, ih, keyScan, keyAt_drop, keyAt_drop]

theorem keyScan_empty (k : Nat) (r : Bool) : keyScan k [] [] r = r := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih => simpa [keyScan, keyAt, keys, scanStep] using ih r

theorem keyScan_lex : ∀ (k : Nat) (as bs : List Int), as.length ≤ k → bs.length ≤ k →
    keyScan k as bs false = lexLt (keys as) (keys bs) := by
  intro k
  induction k with
  | zero =>
    intro as bs ha hb
    have ea : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    have eb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst as; subst bs; rfl
  | succ k ih =>
    intro as bs ha hb
    rw [keyScan_head]
    cases as with
    | nil =>
      cases bs with
      | nil => simp [keyAt, keys, scanStep, lexLt, keyScan_empty]
      | cons b bs => simp [keyAt, keys, scanStep, lexLt]
    | cons a as =>
      cases bs with
      | nil => simp [keyAt, keys, scanStep, lexLt]
      | cons b bs =>
        simp only [List.drop_succ_cons, List.drop_zero]
        rw [ih as bs (by simp at ha; omega) (by simp at hb; omega)]
        rfl

theorem keyScan_bytes (k : Nat) (as bs : List (Zahl 0 255))
    (ha : as.length ≤ k) (hb : bs.length ≤ k) :
    keyScan k (as.map (·.n)) (bs.map (·.n)) false = bytesLt (as.map (·.n)) (bs.map (·.n)) := by
  rw [keyScan_lex k _ _ (by simpa using ha) (by simpa using hb), bytesLt_keys]
  · intro a h
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
    exact x.lo_le
  · intro b h
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
    exact x.lo_le

/-- Key lookup agrees with the length test and padded byte read in the IR kernel. -/
theorem keyAt_byte (bs : List (Zahl 0 255)) (i : Nat) :
    keyAt (bs.map (·.n)) i =
      if i < bs.length then ((bs[i]?).getD ⟨0, by omega, by omega⟩).n.toNat + 1 else 0 := by
  by_cases hi : i < bs.length
  · simp [keyAt, keys, hi, List.getElem?_eq_getElem hi]
  · simp [keyAt, keys, hi, List.getElem?_eq_none (by omega : bs.length ≤ i)]

end Gabbro.Stage0.Senke
