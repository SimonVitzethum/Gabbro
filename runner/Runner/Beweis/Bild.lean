import Runner.Prog.Elf
import Runner.Mach.TSO

/-! # The runner's file: its code is `C`, it places every handler, and loaded it holds the table

* `L0`: the layout of the assembled runner; its code `Cimg` is the file at `BASE`.
* `cinv_L0`: every handler lies at its label (`CInv`), checked by the kernel on the concrete bytes.
* `tab_of_file`: a memory that holds the file at `BASE`, readable and not writable (`FileInv`, what the ELF loader
  makes of the one `PT_LOAD` segment: the loader assumption) holds the dispatch table (`TabInv`), so it is a state
  of both memory models. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog Runner.Mach

def inRun (a : W) : Bool := BASE ≤ a.toNat && a.toNat < BASE + image.length

def Cimg (a : W) : B := if inRun a then image.getD (a.toNat - BASE) 0 else 0

def L0 : Lay where
  C := Cimg
  H k := BitVec.ofNat 64 (target k)
  T := BitVec.ofNat 64 (BASE + tblOff)

set_option maxRecDepth 100000 in
theorem image_len : image.length = 4536 := by decide +kernel

theorem cimg_at {j : Nat} (hj : j < image.length) : Cimg (BitVec.ofNat 64 (BASE + j)) = image[j] := by
  have hl := image_len
  have ht : (BitVec.ofNat 64 (BASE + j)).toNat = BASE + j := by
    simp only [BitVec.toNat_ofNat, BASE]; omega
  have hr : inRun (BitVec.ofNat 64 (BASE + j)) = true := by
    simp only [inRun, ht, Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [Cimg, hr, ↓reduceIte, ht, Nat.add_sub_cancel_left, List.getD, List.getElem?_eq_getElem hj,
    Option.getD_some]

theorem bytes_of_image {o : Nat} {l : List B} (hp : l.isPrefixOf (image.drop o) = true) :
    Bytes Cimg (BitVec.ofNat 64 (BASE + o)) l := by
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
  rw [← BitVec.ofNat_add, Nat.add_assoc, cimg_at hlen, hidx]

theorem code_of_image : ∀ {o : Nat} {is : List Ins},
    is.all Ins.ok = true → (is.flatMap enc).isPrefixOf (image.drop o) = true →
    Code Cimg (BitVec.ofNat 64 (BASE + o)) is
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
    refine ⟨hok.1, bytes_of_image h1, ?_⟩
    have := code_of_image (o := o + (enc i).length) hok.2 h2
    rwa [← Nat.add_assoc, BitVec.ofNat_add] at this

/-- The label of opcode `k`'s handler. -/
def lbl (k : Nat) : Nat := if 1 ≤ k ∧ k ≤ 27 then k else BAD

theorem handler_lbl : ∀ k, handler k = handler (lbl k)
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl
  | 9 => rfl | 10 => rfl | 11 => rfl | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl
  | 18 => rfl | 19 => rfl | 20 => rfl | 21 => rfl | 22 => rfl | 23 => rfl | 24 => rfl
  | 25 => rfl | 26 => rfl
  | 27 => rfl
  | k + 28 => by
    have : ¬(1 ≤ k + 28 ∧ k + 28 ≤ 27) := by omega
    simp only [lbl, this, ↓reduceIte]
    rfl

def labelsAll : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, BAD]

set_option maxRecDepth 100000 in
theorem placed : (labelsAll.all fun j =>
    (handler j).all Ins.ok && ((handler j).flatMap enc).isPrefixOf (image.drop (find tab j))) = true := by
  decide +kernel

theorem cinv_L0 : CInv L0 := by
  intro k
  have hmem : lbl k ∈ labelsAll := by
    unfold lbl labelsAll
    split
    · next h => obtain ⟨h1, h2⟩ := h; simp only [List.mem_cons]; omega
    · simp
  have := List.all_eq_true.mp placed (lbl k) hmem
  simp only [Bool.and_eq_true] at this
  rw [handler_lbl k]
  exact code_of_image this.1 this.2

/-! ## The loaded file holds the table -/

def FileInv (m : Mem) : Prop :=
  ∀ j (h : j < image.length), m.b (BitVec.ofNat 64 (BASE + j)) = image[j] ∧
    m.rd (BitVec.ofNat 64 (BASE + j)) = true ∧ m.wr (BitVec.ofNat 64 (BASE + j)) = false

theorem mbytes_of_file {m : Mem} (hf : FileInv m) {o : Nat} {l : List B}
    (hp : l.isPrefixOf (image.drop o) = true) : MBytes m (BitVec.ofNat 64 (BASE + o)) l := by
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
  rw [← BitVec.ofNat_add, Nat.add_assoc, ← hidx]
  exact hf (o + j) hlen

/-- Check the concrete table in bounded pieces to keep kernel reduction within
    the per-check memory limit; the final theorem still covers all 256 entries. -/
def tableEntryCorrect (k : Nat) : Bool :=
  (wbytes (BitVec.ofNat 64 (target k))).isPrefixOf (image.drop (tblOff + 8 * k))

set_option maxRecDepth 100000 in
private theorem tabled_0 : ((List.range 32).map (· + 0)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_1 : ((List.range 32).map (· + 32)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_2 : ((List.range 32).map (· + 64)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_3 : ((List.range 32).map (· + 96)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_4 : ((List.range 32).map (· + 128)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_5 : ((List.range 32).map (· + 160)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_6 : ((List.range 32).map (· + 192)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem tabled_7 : ((List.range 32).map (· + 224)).all tableEntryCorrect = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tabled : (List.range 256).all
    (fun k => (wbytes (BitVec.ofNat 64 (target k))).isPrefixOf (image.drop (tblOff + 8 * k))) = true := by
  change (List.range 256).all tableEntryCorrect = true
  have ranges : List.range 256 = ((List.range 32).map (· + 0)) ++ ((List.range 32).map (· + 32)) ++ ((List.range 32).map (· + 64)) ++ ((List.range 32).map (· + 96)) ++ ((List.range 32).map (· + 128)) ++ ((List.range 32).map (· + 160)) ++ ((List.range 32).map (· + 192)) ++ ((List.range 32).map (· + 224)) := by decide +kernel
  rw [ranges]
  simp only [List.all_append, tabled_0, tabled_1, tabled_2, tabled_3, tabled_4, tabled_5, tabled_6, tabled_7, Bool.and_self]

set_option maxRecDepth 100000 in
theorem tbl_addr (op : Nat) (_hop : op < 256) :
    taddr L0 (BitVec.ofNat 64 op) = BitVec.ofNat 64 (BASE + (tblOff + 8 * op)) := by
  have ht : tblOff = 2488 := by decide +kernel
  apply BitVec.eq_of_toNat_eq
  simp only [taddr, L0, sx32, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_signExtend, ht,
    BASE]
  simp
  omega

theorem tab_of_file {m : Mem} (hf : FileInv m) : TabInv L0 m := by
  intro op hop
  rw [tbl_addr op hop]
  exact mbytes_of_file hf (List.all_eq_true.mp tabled op (List.mem_range.mpr hop))

end Runner.Beweis
