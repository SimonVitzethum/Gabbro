/-
  File:      stage0/Stage0/Senke/BildLese.lean
  Subject:   Bytes in memory as code and frames: an image's bytes at their address are the instructions they encode
             (`codeAt_bytes`) and the frame their zeros give room for (`frameOK_bytes`).
-/
import Stage0.Senke.Bild

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

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

theorem rd8_bytes {m : Runner.Mem} {p : Nat} {v : Runner.B} {bs : List Runner.B} (h : BytesAt m p (v :: bs)) :
    m.rd8 (BitVec.ofNat 64 p) = some v := by
  obtain ⟨hr, _, hb⟩ := h 0 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at hr hb
  simp only [Runner.Mem.rd8, hr, ↓reduceIte, hb]

theorem rd32_bytes {m : Runner.Mem} {p : Nat} {v : BitVec 32} (h : BytesAt m p (Runner.X86.le32 v)) :
    m.rd32 (BitVec.ofNat 64 p) = some v := by
  have g := fun i hi => h i hi
  obtain ⟨r0, _, b0⟩ := g 0 (by simp [Runner.X86.le32])
  obtain ⟨r1, _, b1⟩ := g 1 (by simp [Runner.X86.le32])
  obtain ⟨r2, _, b2⟩ := g 2 (by simp [Runner.X86.le32])
  obtain ⟨r3, _, b3⟩ := g 3 (by simp [Runner.X86.le32])
  simp only [Runner.X86.le32, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at r0 r1 r2 r3 b0 b1 b2 b3
  simp only [Runner.Mem.rd32, Runner.Mem.all, Runner.Mem.le, ofNat_add64, Nat.add_zero, r0, r1, r2, r3,
    Bool.and_self, ↓reduceIte, b0, b1, b2, b3, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [Runner.X86.byte, BitVec.toNat_ofNat]
  omega

/-- One instruction from its 16 bytes. -/
theorem insAt_bytes {m : Runner.Mem} {p : Nat} {i : II} (ho : i.o < 256)
    (h : BytesAt m p (Runner.Prog.insB i.o i.a i.b i.c)) :
    InsAt m (BitVec.ofNat 64 p) i.o (II.f i.a) (II.f i.b) (II.f i.c) := by
  simp only [Runner.Prog.insB, Runner.Prog.i32] at h
  have h1 := h.left.left.left
  have h2 := h.left.left.right
  have h3 := h.left.right
  have h4 := h.right
  simp only [List.length_append, List.length_cons, List.length_nil, Runner.X86.le32] at h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rd8_bytes h1]; rfl
  · rw [show BitVec.ofNat 64 p + 4 = BitVec.ofNat 64 (p + 4) from ofNat_add64 p 4]; exact rd32_bytes h2
  · rw [show BitVec.ofNat 64 p + 8 = BitVec.ofNat 64 (p + 8) from ofNat_add64 p 8]; exact rd32_bytes h3
  · rw [show BitVec.ofNat 64 p + 12 = BitVec.ofNat 64 (p + 12) from ofNat_add64 p 12]; exact rd32_bytes h4

theorem encII_len (i : II) : (encII i).length = 16 := by
  simp [encII, Runner.Prog.insB, Runner.Prog.i32, Runner.X86.le32]

theorem flatMap_enc_len : (is : List II) → (is.flatMap encII).length = 16 * is.length
  | [] => rfl
  | i :: is => by
    simp only [List.flatMap_cons, List.length_append, encII_len, flatMap_enc_len is, List.length_cons]
    omega

/-- A list of instructions from its bytes. -/
theorem codeAt_bytes {m : Runner.Mem} : (is : List II) → (p : Nat) → is.all (fun i => decide (i.o < 256)) = true →
    BytesAt m p (is.flatMap encII) → CodeAt m (BitVec.ofNat 64 p) is
  | [], _, _, _ => fun k hk => absurd hk (by simp)
  | i :: is, p, ho, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ho
    simp only [List.flatMap_cons] at h
    have hi := insAt_bytes ho.1 h.left
    have hr := codeAt_bytes is (p + 16) ho.2 (by have := h.right; rwa [encII_len] at this)
    intro k hk
    cases k with
    | zero => simpa using hi
    | succ k =>
      have := hr k (by simpa using hk)
      simp only [List.getElem_cons_succ]
      simp only [ofNat_add64] at this ⊢
      rwa [show p + 16 * (k + 1) = p + 16 + 16 * k by omega]

/-- A frame of `K` slots from the bytes at `p`. -/
theorem frameOK_bytes {m : Runner.Mem} {p K : Nat} {bs : List Runner.B} (h : BytesAt m p bs) (hl : 8 * K ≤ bs.length)
    (hp : p + 8 * K < 2 ^ 64) : FrameOK m (BitVec.ofNat 64 p) K := by
  have hs : ∀ i j, i < K → j < 8 → slot (BitVec.ofNat 64 p) (BitVec.ofNat 64 i) + BitVec.ofNat 64 j =
      BitVec.ofNat 64 (p + (8 * i + j)) := by
    intro i j _ _
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    omega
  refine ⟨by simp only [BitVec.toNat_ofNat]; omega, fun i hi => all_of fun j hj => ?_, fun i hi => all_of fun j hj => ?_⟩
  · rw [hs i j hi hj]; exact (h _ (by omega)).1
  · rw [hs i j hi hj]; exact (h _ (by omega)).2.1

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

variable {D : Deklaration}

theorem lowAll_ok {P : Programm D} {name : D.Fn → String} {A : D.Fn → Nat} :
    (fs : List D.Fn) → (cs : List (List II × Nat)) → lowAll P Y name A fs = .ok cs →
    cs.length = fs.length ∧ ∀ i (hi : i < fs.length) (hc : i < cs.length), lowFun P A Y fs[i] = some cs[i]
  | [], cs, h => by
    simp only [lowAll, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | g :: gs, cs, h => by
    simp only [lowAll, bind, Except.bind] at h
    cases hf : lowFunE P Y name A g with
    | error e => simp [hf] at h
    | ok c =>
      cases hr : lowAll P Y name A gs with
      | error e => simp [hf, hr] at h
      | ok r =>
        simp only [hf, hr, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hall⟩ := lowAll_ok gs r hr
        have hg : lowFun P A Y g = some c := by
          simp only [lowFunE] at hf
          split at hf
          · next ct hct => simp only [Except.ok.injEq] at hf; rw [hct, hf]
          · cases hf
        refine ⟨by simp [hl], fun i hi hc => ?_⟩
        cases i with
        | zero => simpa using hg
        | succ i => simpa using hall i (by simpa using hi) (by simpa using hc)

theorem foldl_max_ge : (cs : List (List II × Nat)) → ∀ a, a ≤ cs.foldl (fun a c => max a c.2) a ∧
    ∀ c ∈ cs, c.2 ≤ cs.foldl (fun a c => max a c.2) a
  | [], a => by simp
  | c :: cs, a => by
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2⟩ := foldl_max_ge cs (max a c.2)
    refine ⟨by omega, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · omega
    · exact h2 x hx

theorem maxTop_ge {cs : List (List II × Nat)} {i : Nat} (hi : i < cs.length) : cs[i].2 ≤ maxTop cs :=
  (foldl_max_ge cs 1).2 _ (List.getElem_mem hi)

theorem maxTop_pos (cs : List (List II × Nat)) : 1 ≤ maxTop cs := (foldl_max_ge cs 1).1

theorem addrs_getD : (ls : List Nat) → (b i : Nat) → i < ls.length →
    (addrs b ls).getD i 0 = b + 16 * (ls.take i).sum
  | [], _, _, h => absurd h (by simp)
  | l :: ls, b, 0, _ => by simp [addrs]
  | l :: ls, b, i + 1, h => by
    simp only [addrs, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [addrs_getD ls (b + 16 * l) i (by simpa using h)]
    omega

theorem flat_split : (cs : List (List II × Nat)) → (i : Nat) → (hi : i < cs.length) →
    cs.flatMap (·.1) = (cs.take i).flatMap (·.1) ++ (cs[i].1 ++ (cs.drop (i + 1)).flatMap (·.1))
  | [], _, hi => absurd hi (by simp)
  | c :: cs, 0, _ => by simp
  | c :: cs, i + 1, hi => by
    simp only [List.flatMap_cons, List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons]
    rw [flat_split cs i (by simpa using hi), List.append_assoc]

theorem flat_take_len (cs : List (List II × Nat)) (i : Nat) :
    ((cs.take i).flatMap (·.1)).length = ((cs.map (·.1.length)).take i).sum := by
  simp [List.length_flatMap, List.map_take]

end Gabbro.Stage0.Senke
