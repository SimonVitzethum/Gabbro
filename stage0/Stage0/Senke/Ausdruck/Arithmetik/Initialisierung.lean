/- Executed slot initialization, retaining each earlier result across temporaries. -/
import Stage0.Senke.Ausdruck.Arithmetik.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- Evaluate producers at successive state slots. Later producers may use arbitrary
    higher temporaries; their results cannot overwrite earlier state words. -/
def floatStateSlotsL (base : Nat)
    (producers : List (Nat → Option (List II × Nat))) : Option (List II × Nat) := do
  match producers with
  | [] => pure ([], base)
  | p :: ps =>
    let a ← p base
    let b ← floatStateSlotsL (base+1) ps
    pure (a.1 ++ b.1, max a.2 b.2)

variable [Kern] {D : Deklaration} {L : Lay D}

/-- This is execution, including all producer writes, rather than a premise
    asserting that the state slots already contain the desired words.
    The producer contract explicitly carries the reserved environment prefix. -/
theorem floatStateSlotsL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {fp : Runner.W} {K reserved base top : Nat} {code : List II}
    (ps : List (Nat → Option (List II × Nat))) (values : Nat → Runner.W)
    (compiled : floatStateSlotsL base ps = some (code, top)) (room : top ≤ K)
    (slots : base + ps.length ≤ K)
    (producers : ∀ i, (hi : i < ps.length) → ∀ c t,
      ps[i] (base+i) = some (c,t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K (base+i) c ρ W reserved →
      Ok m pc fp K (base+i) c (· = values i))
    (m : Runner.Mem) (pc : Runner.W)
    (pre : Pre L m pc fp K base code ρ W reserved) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16*code.length), fp⟩ m' ∧
      Agree fp base K m m' ∧
      ∀ i, i < ps.length →
        m'.rd64 (slot fp (BitVec.ofNat 64 (base+i))) = some (values i) := by
  induction ps generalizing base top code values m pc with
  | nil =>
    simp [floatStateSlotsL] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    exact ⟨m, by simpa using Star.refl ⟨pc,fp⟩ m,
      Agree.refl _ _ _ _, by simp⟩
  | cons p ps ih =>
    simp only [floatStateSlotsL] at compiled
    cases ha : p base with
    | none => simp [ha] at compiled
    | some a =>
      cases hb : floatStateSlotsL (base+1) ps with
      | none => simp [ha, hb] at compiled
      | some b =>
        simp [ha, hb] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        obtain ⟨m1, run1, agree1, w, read1, result1⟩ :=
          producers 0 (by simp) a.1 a.2 (by simpa using ha)
            (by omega) m pc pre.left
        subst w
        have next := pre.next agree1 (Nat.le_succ base) (by simp at slots; omega)
        obtain ⟨m2, run2, agree2, reads⟩ := ih (fun i => values (i+1)) hb
          (by omega) (by simp at slots; omega) (by
            intro i hi c t hc ht m pc hp
            have h := producers (i+1) (by simp; omega) c t
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              h (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc)
                ht m pc (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp)) m1 _ next
        refine ⟨m2, ?_, agree1.trans (agree2.mono (Nat.le_succ base)), ?_⟩
        · have endPc : pc + BitVec.ofNat 64 (16*(a.1 ++ b.1).length) =
              pc + BitVec.ofNat 64 (16*a.1.length) + BitVec.ofNat 64 (16*b.1.length) := by
            rw [List.length_append, pc_add]
          rw [endPc]
          exact run1.trans run2
        · intro i hi
          cases i with
          | zero =>
            simpa using slotRead_agree next.frame agree2 (Nat.lt_succ_self base)
              (by simp at slots; omega) (by simpa using read1)
          | succ i =>
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              reads i (by simpa using hi)

/-- Two distinct writes execute jointly without assuming either initial slot. -/
theorem floatStateSlotsL_ok_zeuge {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc fp : Runner.W}
    {base K reserved : Nat} (room : base+2 ≤ K)
    (pre : Pre L m pc fp K base
      [ci 1 base 7 0, ci 1 (base+1) 11 0] ρ W reserved) :
    ∃ m', Star ⟨pc,fp⟩ m ⟨pc + BitVec.ofNat 64 32,fp⟩ m' ∧
      Agree fp base K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 base)) = some 7 ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (base+1))) = some 11 := by
  let ps : List (Nat → Option (List II × Nat)) :=
    [fun d => some ([ci 1 d 7 0], d+1),
     fun d => some ([ci 1 d 11 0], d+1)]
  have compiled : floatStateSlotsL base ps =
      some ([ci 1 base 7 0, ci 1 (base+1) 11 0], base+2) := by
    simp [floatStateSlotsL, ps]
  obtain ⟨m', run, agree, reads⟩ := floatStateSlotsL_ok ps
    (fun i => if i = 0 then 7 else 11) compiled room (by simpa [ps] using room)
    (by
      intro i hi c t hc ht m pc hp
      have bound : i < 2 := by simpa [ps] using hi
      interval_cases i <;> simp [ps] at hc <;>
        obtain ⟨rfl,rfl⟩ := hc
      · exact const_ok hp (by decide) (by omega)
      · exact const_ok hp (by decide) (by omega)) m pc pre
  exact ⟨m', run, agree, by simpa using reads 0 (by simp [ps]),
    by simpa using reads 1 (by simp [ps])⟩

#print axioms floatStateSlotsL_ok_zeuge
#print axioms floatStateSlotsL_ok
end Gabbro.Stage0.Senke
