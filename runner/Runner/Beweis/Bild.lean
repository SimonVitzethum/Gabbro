import Runner.Prog.Elf
import Runner.Beweis.Sim

/-! # The runner's file establishes `ImgInv`

`FileInv m`: the memory holds the file `image` at `BASE`, readable and not writable -- what Linux's ELF loader
makes of the one `PT_LOAD` segment (read and execute, the loader assumption). `image_ok`: then `ImgInv` holds for
the layout `L0` of the assembled runner: every handler's instructions at its label, the 256 table words at the
table. The placement facts are checked by the kernel on the concrete bytes (`decide +kernel`, no extra axiom). -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

def FileInv (m : Mem) : Prop :=
  ∀ j (h : j < image.length), m.b (BitVec.ofNat 64 (BASE + j)) = image[j] ∧
    m.rd (BitVec.ofNat 64 (BASE + j)) = true ∧ m.wr (BitVec.ofNat 64 (BASE + j)) = false

/-- The layout of the assembled runner. -/
def L0 : Lay where
  H k := BitVec.ofNat 64 (target k)
  T := BitVec.ofNat 64 (BASE + tblOff)

theorem bytes_of_file {m : Mem} (hf : FileInv m) {o : Nat} {l : List B}
    (hp : l.isPrefixOf (image.drop o) = true) : Bytes m (BitVec.ofNat 64 (BASE + o)) l := by
  obtain ⟨r, hr⟩ := List.isPrefixOf_iff_prefix.mp hp
  intro j hj
  have hlen : o + j < image.length := by
    have := congrArg List.length hr
    simp only [List.length_append, List.length_drop] at this
    omega
  have hidx : image[o + j] = l[j] := by
    have h1 : (image.drop o)[j]'(by simp; omega) = image[o + j] := List.getElem_drop ..
    rw [← h1]
    simp only [← hr, List.getElem_append_left hj]
  have ha : BitVec.ofNat 64 (BASE + o) + BitVec.ofNat 64 j = BitVec.ofNat 64 (BASE + (o + j)) := by
    rw [← BitVec.ofNat_add, Nat.add_assoc]
  rw [ha, ← hidx]
  exact hf (o + j) hlen

theorem code_of_file {m : Mem} (hf : FileInv m) : ∀ {o : Nat} {is : List Ins},
    is.all Ins.ok = true → (is.flatMap enc).isPrefixOf (image.drop o) = true →
    Code m (BitVec.ofNat 64 (BASE + o)) is
  | _, [], _, _ => trivial
  | o, i :: is, hok, hp => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.flatMap_cons] at hp
    obtain ⟨r, hr⟩ := List.isPrefixOf_iff_prefix.mp hp
    have h1 : (enc i).isPrefixOf (image.drop o) = true :=
      List.isPrefixOf_iff_prefix.mpr ⟨is.flatMap enc ++ r, by rw [← hr, List.append_assoc]⟩
    have h2 : (is.flatMap enc).isPrefixOf (image.drop (o + (enc i).length)) = true := by
      apply List.isPrefixOf_iff_prefix.mpr
      refine ⟨r, ?_⟩
      rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]
    refine ⟨hok.1, bytes_of_file hf h1, ?_⟩
    have := code_of_file hf (o := o + (enc i).length) hok.2 h2
    rwa [← Nat.add_assoc, BitVec.ofNat_add] at this

/-! ## The placement facts, on the concrete bytes -/

/-- The label of opcode `k`'s handler. -/
def lbl (k : Nat) : Nat := if 1 ≤ k ∧ k ≤ 23 then k else BAD

theorem handler_lbl : ∀ k, handler k = handler (lbl k)
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | 17 => rfl
  | 18 => rfl
  | 19 => rfl
  | 20 => rfl
  | 21 => rfl
  | 22 => rfl
  | 23 => rfl
  | k + 24 => by
    have : ¬(1 ≤ k + 24 ∧ k + 24 ≤ 23) := by omega
    simp only [lbl, this, ↓reduceIte]
    rfl

set_option maxRecDepth 100000 in
theorem placed : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, BAD].all
    fun j => (handler j).all Ins.ok && ((handler j).flatMap enc).isPrefixOf (image.drop (find tab j))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tabled : (List.range 256).all
    (fun k => (wbytes (BitVec.ofNat 64 (target k))).isPrefixOf (image.drop (tblOff + 8 * k))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tbl_addr (op : B) :
    BitVec.ofNat 64 (BASE + tblOff) + op.setWidth 64 * BitVec.ofNat 64 (2 ^ 3) + sx32 0 =
      BitVec.ofNat 64 (BASE + (tblOff + 8 * op.toNat)) := by
  have := op.isLt
  have ht : tblOff = 2088 := by decide +kernel
  apply BitVec.eq_of_toNat_eq
  simp only [sx32, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    BitVec.toNat_signExtend, ht, BASE]
  simp
  omega

theorem image_ok {m : Mem} (hf : FileInv m) : ImgInv L0 m := by
  refine ⟨fun op => ?_, fun k => ?_⟩
  · show Bytes m (BitVec.ofNat 64 (BASE + tblOff) + op.setWidth 64 * BitVec.ofNat 64 (2 ^ 3) + sx32 0)
      (wbytes (BitVec.ofNat 64 (target op.toNat)))
    rw [tbl_addr]
    have := List.all_eq_true.mp tabled op.toNat (List.mem_range.mpr op.isLt)
    exact bytes_of_file hf this
  · have hk := handler_lbl k
    have hmem : lbl k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, BAD] := by
      unfold lbl
      split
      · next h => obtain ⟨h1, h2⟩ := h; simp only [List.mem_cons]; omega
      · simp
    have := List.all_eq_true.mp placed (lbl k) hmem
    simp only [Bool.and_eq_true] at this
    rw [hk]
    have hH : L0.H k = BitVec.ofNat 64 (BASE + find tab (lbl k)) := rfl
    rw [hH]
    exact code_of_file hf this.1 this.2

end Runner.Beweis
