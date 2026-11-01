/- Subject: Execution of the branch-free span comparison: the accumulated word folds every XOR pair. -/
import Stage0.Senke.Ausdruck.Aggregat.Frame.CompareCode
import Stage0.Senke.Ausdruck.Eng
import Stage0.Senke.Ausdruck.Aggregat.Scalar

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem xorOrSpan_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {fp : Runner.W} {K acc tmp : Nat} :
    ∀ (as bs : List Runner.W), as.length = bs.length →
    ∀ {m : Runner.Mem} {pc : Runner.W} {a b : Nat} {w0 : Runner.W},
    Pre L m pc fp K acc (xorOrSpan as.length a b acc tmp) ρ W reserved →
    a + as.length ≤ acc → b + as.length ≤ acc → acc < tmp → tmp < K →
    WordsAt m fp a as → WordsAt m fp b bs →
    m.rd64 (slot fp (BitVec.ofNat 64 acc)) = some w0 →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (xorOrSpan as.length a b acc tmp).length), fp⟩ m' ∧
      Agree fp acc K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 acc)) =
        some ((as.zip bs).foldl (fun x p => x ||| (p.1 ^^^ p.2)) w0) := by
  intro as
  induction as with
  | nil =>
    intro bs _ m pc a b w0 pre _ _ _ _ _ _ read
    exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _, by simpa using read⟩
  | cons x xs ih =>
    intro bs hlen m pc a b w0 pre ha hb pt ht wa wb read
    cases bs with
    | nil => simp at hlen
    | cons y ys =>
      have hl : xs.length = ys.length := by simpa using hlen
      have hp : Pre L m pc fp K acc
          ([ci 10 tmp a b] ++ ([ci 9 acc acc tmp] ++ xorOrSpan xs.length (a + 1) (b + 1) acc tmp)) ρ W reserved := by
        exact pre
      have xa : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some x := by
        have h := wa 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using h
      have yb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some y := by
        have h := wb 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using h
      obtain ⟨m1, s1, a1, r1, read1, hr1⟩ := eng_bin_ok
        ({ hp.left with ctx := by have := pre.ctx; omega } : Pre L m pc fp K tmp [ci 10 tmp a b] ρ W reserved)
        (by omega) (by simp at ha; omega) (by simp at hb; omega) xa yb
        (g := fun p q => some (p ^^^ q)) rfl (by decide) rfl
      subst hr1
      have a1' : Agree fp acc K m m1 := a1.mono (by omega)
      have p1 := hp.next a1' (Nat.le_refl _) (by omega)
      have acc1 : m1.rd64 (slot fp (BitVec.ofNat 64 acc)) = some w0 := by
        rw [agree_rd_low a1 pre.frame.room pt (by omega)]; exact read
      obtain ⟨m2, s2, a2, r2, read2, hr2⟩ := eng_bin_ok p1.left (by omega) (by omega) ht acc1 read1
        (g := fun p q => some (p ||| q)) rfl (by decide) rfl
      subst hr2
      have p2 := p1.next a2 (Nat.le_refl _) (by omega)
      have a12 : Agree fp acc K m m2 := a1'.trans a2
      have wa2 : WordsAt m2 fp (a + 1) xs := by
        intro i hi
        rw [show a + 1 + i = a + (i + 1) by omega, agree_rd_low a12 pre.frame.room (by simp at ha; omega) (by omega)]
        have h := wa (i + 1) (by simp; omega)
        simpa only [List.getElem_cons_succ] using h
      have wb2 : WordsAt m2 fp (b + 1) ys := by
        intro i hi
        rw [show b + 1 + i = b + (i + 1) by omega, agree_rd_low a12 pre.frame.room (by simp at hb; omega) (by omega)]
        have h := wb (i + 1) (by simp; omega)
        simpa only [List.getElem_cons_succ] using h
      obtain ⟨m3, s3, a3, r3⟩ := ih ys hl p2 (by simp at ha; omega) (by simp at hb; omega) pt ht wa2 wb2 read2
      refine ⟨m3, ?_, a12.trans a3, by simpa [List.zip_cons_cons, List.foldl_cons] using r3⟩
      have steps := s1.trans (s2.trans s3)
      have key : ∀ p q : Runner.W, p = q → Star ⟨pc, fp⟩ m ⟨p, fp⟩ m3 → Star ⟨pc, fp⟩ m ⟨q, fp⟩ m3 :=
        fun p q h s => h ▸ s
      refine key _ _ ?_ steps
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, xorOrSpan_length, List.length_cons, List.length_nil]
      omega

theorem foldl_or_xor_zero :
    ∀ (as bs : List (BitVec 64)) (w0 : BitVec 64), as.length = bs.length →
      ((as.zip bs).foldl (fun x p => x ||| (p.1 ^^^ p.2)) w0 = 0 ↔ w0 = 0 ∧ as = bs) := by
  intro as
  induction as with
  | nil =>
    intro bs w0 h
    cases bs with
    | nil => simp
    | cons => simp at h
  | cons x xs ih =>
    intro bs w0 h
    cases bs with
    | nil => simp at h
    | cons y ys =>
      have hl : xs.length = ys.length := by simpa using h
      have step := ih ys (w0 ||| (x ^^^ y)) hl
      simp only [List.zip_cons_cons, List.foldl_cons]
      have or0 : ∀ a b : BitVec 64, (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := fun a b => BitVec.or_eq_zero_iff
      have xor0 : ∀ a b : BitVec 64, (a ^^^ b = 0) ↔ a = b := fun a b => BitVec.xor_eq_zero_iff
      rw [step, or0, xor0]
      constructor
      · rintro ⟨⟨h0, hxy⟩, hxs⟩
        exact ⟨h0, by rw [hxy, hxs]⟩
      · rintro ⟨h0, hh⟩
        obtain ⟨hxy, hxs⟩ := List.cons.inj hh
        exact ⟨⟨h0, hxy⟩, hxs⟩

end Gabbro.Stage0.Senke
