/- Shared loaded-byte primitives, below initial-data and image execution proofs. -/
import Runner.Prog.IRAsm
import Runner.IR.Rahmen
import Stage0.Senke.Welt.StartLayout
namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem
/-- The bytes `bs` lie from address `p` on, readable and writable. -/
def BytesAt (m : Runner.Mem) (p : Nat) (bs : List Runner.B) : Prop :=
  ∀ i (h : i < bs.length), m.rd (BitVec.ofNat 64 (p + i)) = true ∧ m.wr (BitVec.ofNat 64 (p + i)) = true ∧
    m.b (BitVec.ofNat 64 (p + i)) = bs[i]

theorem BytesAt.left {m : Runner.Mem} {p : Nat} {xs ys : List Runner.B} (h : BytesAt m p (xs ++ ys)) :
    BytesAt m p xs := fun i hi => by
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

theorem BytesAt.right {m : Runner.Mem} {p : Nat} {xs ys : List Runner.B} (h : BytesAt m p (xs ++ ys)) :
    BytesAt m (p + xs.length) ys := fun i hi => by
  have := h (xs.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rwa [Nat.add_assoc]

theorem ofNat_add64 (p k : Nat) : BitVec.ofNat 64 p + BitVec.ofNat 64 k = BitVec.ofNat 64 (p + k) :=
  (BitVec.ofNat_add p k).symm

/-- The header word: the first frame's address. -/
theorem rd64_leN {m : Runner.Mem} {p v : Nat} {bs : List Runner.B} (h : BytesAt m p (Runner.Prog.leN 8 v ++ bs))
    (hv : v < 2 ^ 64) : m.rd64 (BitVec.ofNat 64 p) = some (BitVec.ofNat 64 v) := by
  have g : ∀ i, i < 8 → m.rd (BitVec.ofNat 64 (p + i)) = true ∧
      m.b (BitVec.ofNat 64 (p + i)) = Runner.X86.byte (v / 256 ^ i) := fun i hi => by
    obtain ⟨hr, _, hb⟩ := h i (by simp [Runner.Prog.leN]; omega)
    refine ⟨hr, ?_⟩
    rw [hb, List.getElem_append_left (by simp [Runner.Prog.leN]; omega)]
    simp [Runner.Prog.leN]
  obtain ⟨r0, b0⟩ := g 0 (by omega)
  obtain ⟨r1, b1⟩ := g 1 (by omega)
  obtain ⟨r2, b2⟩ := g 2 (by omega)
  obtain ⟨r3, b3⟩ := g 3 (by omega)
  obtain ⟨r4, b4⟩ := g 4 (by omega)
  obtain ⟨r5, b5⟩ := g 5 (by omega)
  obtain ⟨r6, b6⟩ := g 6 (by omega)
  obtain ⟨r7, b7⟩ := g 7 (by omega)
  simp only [Nat.add_zero] at r0 b0
  simp only [Runner.Mem.rd64, Runner.Mem.all, Runner.Mem.le, ofNat_add64, Nat.add_zero, r0, r1, r2, r3, r4, r5, r6,
    r7, Bool.and_self, ↓reduceIte, b0, b1, b2, b3, b4, b5, b6, b7, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp only [Runner.X86.byte, BitVec.toNat_ofNat]
  omega

/-- Every serialized word reads back exactly, including all high bits and trailing words. -/
theorem startWordBytes_read {m : Runner.Mem} (words : List Runner.W) (p : Nat)
    (loaded : BytesAt m p (startWordBytes words)) :
    ∀ i (hi : i < words.length),
      m.rd64 (BitVec.ofNat 64 (p + 8 * i)) = some words[i] := by
  induction words generalizing p with
  | nil => intro i hi; simp at hi
  | cons word rest ih =>
    intro i hi
    have bytes : BytesAt m p (Runner.Prog.leN 8 word.toNat ++ startWordBytes rest) := loaded
    cases i with
    | zero =>
      simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        rd64_leN bytes word.isLt
    | succ i =>
      have tail := bytes.right
      simp only [Runner.Prog.leN, List.length_map, List.length_range] at tail
      have result := ih (p + 8) tail i (by simpa using hi)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using result

/-- Select one serialized block without forgetting its exact prefix displacement. -/
theorem BytesAt.flatMap_piece {α : Type} {m : Runner.Mem} {f : α → List Runner.B} :
    ∀ (xs : List α) (p i : Nat) (hi : i < xs.length), BytesAt m p (xs.flatMap f) →
      BytesAt m (p + ((xs.take i).flatMap f).length) (f xs[i]) := by
  intro xs
  induction xs with
  | nil => intro p i hi loaded; simp at hi
  | cons x xs ih =>
    intro p i hi loaded
    have bytes : BytesAt m p (f x ++ xs.flatMap f) := loaded
    cases i with
    | zero => simpa using bytes.left
    | succ i =>
      have h := ih (p + (f x).length) i (by simp at hi; omega) bytes.right
      simpa [List.take_succ_cons, List.length_append, Nat.add_assoc] using h

/-- Every represented static cell occupies a complete repeated serialized block. -/
theorem BytesAt.replicate_piece {m : Runner.Mem} (bytes : List Runner.B) :
    ∀ (count p i : Nat), i < count → BytesAt m p (List.replicate count bytes).flatten →
      BytesAt m (p + i * bytes.length) bytes := by
  intro count
  induction count with
  | zero => intro p i hi loaded; omega
  | succ count ih =>
    intro p i hi loaded
    have blocks : BytesAt m p (bytes ++ (List.replicate count bytes).flatten) := loaded
    cases i with
    | zero => simpa using blocks.left
    | succ i =>
      have h := ih (p + bytes.length) i (by omega) blocks.right
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end Gabbro.Stage0.Senke
