/- Concrete saved-measure comparison and logical stop. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Code
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Stage0.Senke.Ausdruck.Arithmetik.Interval
public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem

variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Execute the actual comparison after the post-body range check. The saved
    measure is read from its reserved frame word, never reconstructed from the
    changed world. A nonfalling measure takes the emitted logical stop. -/
theorem strict_compare {Γ : Ctx} {ρ : Env D Γ} {m : Mem} {pc fp : W}
    {K d saved failure : Nat} {old new : Int}
    (hp : PreS L m pc fp K d
      ([ci 2 (d + 1) saved 0] ++ [ci 13 d d (d + 1)] ++ guardC d failure d) ρ reserved)
    (room : d + 8 ≤ K) (savedBound : saved < d) (failureBound : failure < 2 ^ 31)
    (oldBound : -2 ^ 63 ≤ old ∧ old < 2 ^ 63)
    (newBound : -2 ^ 63 ≤ new ∧ new < 2 ^ 63)
    (oldRead : m.rd64 (slot fp (BitVec.ofNat 64 saved)) = some (BitVec.ofInt 64 old))
    (newRead : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 new)) :
    if new < old then
      Ok m pc fp K d
        ([ci 2 (d + 1) saved 0] ++ [ci 13 d d (d + 1)] ++ guardC d failure d) (· = 1)
    else Stops ⟨pc, fp⟩ m failure := by
  have pre : PreS L m pc fp K d
      ([ci 2 (d + 1) saved 0] ++ ([ci 13 d d (d + 1)] ++ guardC d failure d)) ρ reserved := hp
  obtain ⟨m1, move, a1, w1, read1, rfl⟩ := mov_ok
    { pre.left with ctx := by have := hp.ctx; omega }
    (by omega) (by omega) oldRead
  have tail := pre.next (a1.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  have newRead1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 new) := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]
    exact newRead
  obtain ⟨m2, compare, a2, w2, read2, rfl⟩ := eng_bin_ok tail.left
    (by omega) (by omega) (by omega) newRead1 read1
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) rfl
  have guardPre := tail.next a2 (Nat.le_refl _) (by omega)
  have comparison : (BitVec.ofInt 64 new).slt (BitVec.ofInt 64 old) = decide (new < old) :=
    slt_in newBound oldBound
  rw [comparison] at read2
  by_cases falls : new < old
  · simp only [falls, ↓reduceIte]
    have readTrue : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some 1 := by
      simpa only [falls, decide_true, Runner.IR.bool] using read2
    have pass := guard_pass guardPre.code (by have := hp.small; omega) readTrue (by decide)
    refine ⟨m2, ?_, (a1.mono (Nat.le_succ _)).trans a2, 1, readTrue, rfl⟩
    simpa only [List.length_append, List.length_singleton, pc_add] using move.trans (compare.trans pass)
  · simp only [falls, ↓reduceIte]
    have readFalse : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some 0 := by
      simpa only [falls, decide_false, Runner.IR.bool] using read2
    have stopped := guard_stop guardPre.code
      (by simpa only [guardC, stopC, sysC, List.length_append, List.length_cons,
        List.length_nil] using guardPre.far)
      guardPre.frame (by omega) room hp.small failureBound readFalse
    exact Stops.prefix (move.trans compare) stopped

/-- Both protected words really survive any body outcome that reaches one of
    the post-body checks. This uses the ordinary block simulation's Keeps,
    including bodies with calls or world writes. -/
theorem body_control_words {P : Programm D} {f : D.Fn} {Γ : Ctx}
    {σ : World D} {ρ : Env D Γ} {fp pc exit : W} {lo K : Nat} {pr : List Nat}
    {counter saved : Nat} {m : Mem} {fuel : W} {old : Int}
    (body : Reach L fp lo K (counter :: saved :: pr) ⟨pc, fp⟩ m exit σ ρ reserved)
    (fuelRead : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some fuel)
    (measureRead : m.rd64 (slot fp (BitVec.ofNat 64 saved)) = some (BitVec.ofInt 64 old)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨exit, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧
      Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some fuel ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 saved)) = some (BitVec.ofInt 64 old) := by
  obtain ⟨m', run, frame, env, world, kept⟩ := body
  exact ⟨m', run, frame, env, world,
    (fun j hj => kept j (by simp only [List.mem_cons]; exact Or.inr (Or.inr hj))),
    (kept counter (by simp)).trans fuelRead,
    (kept saved (by simp)).trans measureRead⟩

end Gabbro.Stage0.Senke.Consuming
