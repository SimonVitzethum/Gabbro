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
  obtain ⟨m1, move, a1, w1, read1, rfl⟩ := mov_ok (d := d + 1) (s := saved)
    { pre.left with ctx := by have := hp.ctx; omega }
    (by omega) (by omega) oldRead
  have tail := pre.next (a1.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  have newRead1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 new) := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]
    exact newRead
  obtain ⟨m2, compare, a2, w2, read2, rfl⟩ :=
    eng_bin_ok (d := d) (a := d) (b := d + 1) (o := 13) tail.left
    (by omega) (by omega) (by omega) newRead1 read1
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) rfl
  have guardPre := tail.next a2 (Nat.le_refl _) (by omega)
  have comparison : (BitVec.ofInt 64 new).slt (BitVec.ofInt 64 old) = decide (new < old) :=
    slt_in newBound oldBound
  rw [comparison] at read2
  by_cases falls : new < old
  · simp only [falls, ↓reduceIte]
    have readTrue : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some 1 := by
      simpa only [falls, decide_true, Runner.IR.bool, ↓reduceIte] using read2
    have pass := guard_pass (a := d) (c := failure) (s := d)
      guardPre.code (by have := hp.small; omega) readTrue (by decide)
    refine ⟨m2, ?_, (a1.mono (Nat.le_succ _)).trans a2, 1, readTrue, rfl⟩
    simpa only [List.length_append, List.length_singleton, pc_add, Nat.add_assoc]
      using move.trans (compare.trans pass)
  · simp only [falls, ↓reduceIte]
    have readFalse : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some 0 := by
      simpa only [falls, decide_false, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] using read2
    have stopped := guard_stop (a := d) (c := failure) (s := d) guardPre.code
      (by simpa only [guardC, stopC, sysC, List.length_append, List.length_cons,
        List.length_nil] using guardPre.far)
      guardPre.frame (by omega) room hp.small failureBound readFalse
    exact Stops.prefix (move.trans compare) stopped

/-- Full post-body check against the actual lowered measure. The range test
    remains in the IR; its success follows from the represented typed value.
    The final strict comparison is still a runtime check against the saved
    pre-body value and stops on equality or increase. -/
theorem decrease_ok {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {bound old : Int} {mass : Expr D Γ Λ (.int 0 bound)}
    {m : Mem} {pc fp : W} {K Ks d saved failure te : Nat} {ce : List II}
    {σ : World D}
    (lowered : lowE (reserved := reserved) L mass d = some (ce, te))
    (top : te ≤ Ks) (room : d + 8 ≤ Ks) (layout : WIn L fp Ks K)
    (hp : PreS L m pc fp K d (decrease d saved failure bound ce) ρ reserved)
    (world : WeltAt m L σ) (savedBound : saved < d)
    (failureBound : failure < 2 ^ 31) (bounds : inW 0 bound = true)
    (oldBound : -2 ^ 63 ≤ old ∧ old < 2 ^ 63)
    (oldRead : m.rd64 (slot fp (BitVec.ofNat 64 saved)) = some (BitVec.ofInt 64 old)) :
    let σm := σ.lese Λ mass.orte
    let new := (eval σm mass σm ρ).n
    if new < old then Ok m pc fp K d (decrease d saved failure bound ce) (· = 1)
    else Stops ⟨pc, fp⟩ m failure := by
  let σm := σ.lese Λ mass.orte
  let new := (eval σm mass σm ρ).n
  let test := (engTest 13 d 0 bound).1
  let post := [ci 2 (d + 1) saved 0] ++ [ci 13 d d (d + 1)] ++ guardC d failure d
  let skip := [ci 19 (d + 1) 80 0] ++ stopC failure d ++ [ci 18 (16 * (post.length + 1)) 0 0]
  have smallRoom : d + 8 ≤ K := by have := layout.ks; omega
  have pre : PreS L m pc fp K d (ce ++ (test ++ (skip ++ post))) ρ reserved := by
    simpa only [decrease, test, post, skip, stopC, sysC,
      List.length_cons, List.length_nil, List.length_append, List.length_singleton,
      List.append_assoc] using hp
  have preWorld := PreS.welt pre.left layout.ks world layout.lay
    (by have := layout.lo; omega)
  obtain ⟨m1, measureRun, measureFrame, value, valueRead, valueEncoding⟩ :=
    lowE_ok (same := by intro _; rfl) σm σm (fun _ h => h) layout.lay mass d ce te
      lowered top m pc ρ preWorld |>.word trivial
  have encoding : value = BitVec.ofInt 64 new := valueEncoding
  subst value
  have measureFrameK := Agree.widen measureFrame layout.ks
  have preTest := pre.next measureFrameK (Nat.le_refl _) (by omega)
  obtain ⟨m2, testRun, testFrame, outside, outsideRead, outsideEncoding⟩ :=
    eng_test_ok (o := 13) (d := d) (lo := 0) (hi := bound)
    { preTest.left with ctx := by have := hp.ctx; omega }
    (by have := (engTest_top 13 d 0 bound).2; omega) rfl (by decide) valueRead
  have newLow : 0 ≤ new := (eval σm mass σm ρ).lo_le
  have newHigh : new ≤ bound := (eval σm mass σm ρ).le_hi
  have newBound : -2 ^ 63 ≤ new ∧ new < 2 ^ 63 := inW_spec bounds newLow newHigh
  have boundWord : -2 ^ 63 ≤ bound ∧ bound < 2 ^ 63 := by
    have raw := bounds
    simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at raw
    omega
  have outsideZero : outside = 0 := by
    rw [outsideEncoding]
    simp only [scalarCmp, ↓reduceIte]
    rw [slt_in newBound (by decide), slt_in boundWord newBound]
    simp only [show ¬ new < 0 by omega, show ¬ bound < new by omega,
      decide_false, Bool.false_or, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte]
  subst outside
  have testFrameD := testFrame.mono (Nat.le_succ d)
  have preSkip := preTest.next testFrameD (Nat.le_refl _) (by omega)
  have skipPre : PreS L m2
      (pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * test.length)) fp K d
      ([ci 19 (d + 1) 80 0] ++ (stopC failure d ++
        ([ci 18 (16 * (post.length + 1)) 0 0] ++ post))) ρ reserved := by
    simpa only [skip, List.append_assoc] using preSkip
  have rangeJump := brz_go (j := d + 1) (J := 80)
    skipPre.left.code (by omega) hp.small (by decide) outsideRead
  have skipLength : skip.length = 5 := by simp [skip, stopC, sysC]
  have prePost := preSkip.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have oldRead2 : m2.rd64 (slot fp (BitVec.ofNat 64 saved)) = some (BitVec.ofInt 64 old) := by
    rw [agree_rd_low (measureFrameK.trans testFrameD) hp.frame.room savedBound (by omega)]
    exact oldRead
  have newRead2 : m2.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 new) := by
    rw [agree_rd_low testFrame preTest.frame.room (by omega) (by omega)]
    exact valueRead
  have checked := strict_compare prePost smallRoom savedBound failureBound oldBound newBound oldRead2 newRead2
  have enter : Star ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * test.length) +
        BitVec.ofNat 64 (16 * skip.length), fp⟩ m2 := by
    have jump := rangeJump
    rw [skipLength]
    change Star ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * test.length) + 80, fp⟩ m2
    exact measureRun.trans (testRun.trans jump)
  dsimp only
  by_cases falls : new < old
  · simp only [falls, ↓reduceIte] at checked ⊢
    obtain ⟨m3, strictRun, strictFrame, result, resultRead, resultOne⟩ := checked
    refine ⟨m3, ?_, (measureFrameK.trans testFrameD).trans strictFrame,
      result, resultRead, resultOne⟩
    simpa only [decrease, test, post, skip, stopC, sysC,
      List.length_append, List.length_cons, List.length_nil, List.length_singleton,
      pc_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using enter.trans strictRun
  · simp only [falls, ↓reduceIte] at checked ⊢
    exact Stops.prefix enter checked

/-- Both protected words really survive any body outcome that reaches one of
    the post-body checks. This uses the ordinary block simulation's Keeps,
    including bodies with calls or world writes. -/
theorem body_control_words {Γ : Ctx}
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
