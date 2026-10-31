/- Compositional execution of contiguous value copies on the actual IR machine. -/
import Stage0.Senke.Ausdruck.Sim

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Copy arbitrary represented values from the preserved prefix to fresh consecutive slots.
    This proves child execution, exact output words and frame preservation together. -/
theorem copyWords_ok {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {fp : Runner.W} {K : Nat} (words : List Runner.W) :
    ∀ {m : Runner.Mem} {pc : Runner.W} {d s : Nat},
    s + words.length ≤ d → d + words.length ≤ K →
    Pre L m pc fp K d (copyWords words.length d s) ρ W reserved →
    WordsAt m fp s words →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * words.length), fp⟩ m' ∧
      Agree fp d K m m' ∧ WordsAt m' fp d words := by
  induction words with
  | nil =>
    intro m pc d s _ _ hp hw
    exact ⟨m, by simpa using (Star.refl (t := ⟨pc, fp⟩) (m := m)), Agree.refl _ _ _ _,
      by intro i hi; simp at hi⟩
  | cons w ws ih =>
    intro m pc d s hs hd hp hw
    have hp' : Pre L m pc fp K d
        ([ci 2 d s 0] ++ copyWords ws.length (d + 1) (s + 1)) ρ W reserved := hp
    have hread : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w := by
      exact hw 0 (by simp)
    obtain ⟨m1, run1, agree1, v, read1, hv⟩ := mov_ok hp'.left (by simp at hs; omega)
      (by simp at hd; omega) hread
    subst v
    have hp1 := hp'.next agree1 (Nat.le_succ d) (by simp at hd; omega)
    have tail : WordsAt m1 fp (s + 1) ws := by
      intro i hi
      rw [agree_rd_low agree1 hp.frame.room (by simp at hs; omega) (by simp at hd; omega)]
      have ht := hw (i + 1) (by simp; omega)
      change m.rd64 (slot fp (BitVec.ofNat 64 (s + (i + 1)))) = some ws[i] at ht
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
    obtain ⟨m2, run2, agree2, result⟩ := ih (by simp at hs; omega) (by simp at hd; omega) hp1 tail
    refine ⟨m2, ?_, agree1.trans (agree2.mono (Nat.le_succ d)), ?_⟩
    · have hr := run1.trans run2
      simpa [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm] using hr
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, agree_rd_low agree2 (hp.frame.agree agree1).room (by omega) (by simp at hd; omega)]
        exact read1
      | succ i =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result i (by simp at hi; omega)

end Gabbro.Stage0.Senke
