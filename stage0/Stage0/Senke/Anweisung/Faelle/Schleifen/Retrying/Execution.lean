/- Execute the condition, reserved counter and one actual retry body. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Test
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Retrying.Runtime
@[expose] public section

namespace Gabbro.Stage0.Senke.Retrying.Image
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {Γ : Ctx} {reserved : Nat} (x : Image L P f Γ reserved)

/-- Runtime fuel is always the exact natural number represented by the counter. -/
def Entry (n : Nat) (m : Mem) (σ : World D) (ρ : Env D Γ) : Prop :=
  x.Ready m σ ρ ∧ x.read m x.counter (BitVec.ofNat 64 n) ∧
    x.read m x.one 1 ∧ n < 2 ^ 64

/-- Reconstruct the single header after the positive counter test/decrement. -/
theorem decrement {n : Nat} {m : Mem} {σ : World D} {ρ : Env D Γ}
    (entry : x.Entry (n + 1) m σ ρ) :
    ∃ m', Star ⟨x.addr x.controlIndex, x.fp⟩ m ⟨x.addr x.bodyIndex, x.fp⟩ m' ∧
      AgreeW L x.fp x.lo x.K m m' ∧ Keeps x.fp (x.one :: x.pr) m m' ∧
      x.Entry n m' σ ρ := by
  obtain ⟨ready, read, unit, fits⟩ := entry
  have controls := x.controls
  have room : frei Γ reserved ≤ x.K := by have := x.room; have := x.layout.ks; omega
  obtain ⟨m1, run, frame, pre, surround, head, world, kept, count⟩ :=
    counter_header (pr := x.one :: x.pr) x.layout ready.control ready.surround ready.head
      ready.world (by rw [x.abi]) controls.1 (by omega) room
      (by unfold frei at room; omega) read unit fits (by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨by unfold frei at room; omega, by omega⟩
        · have := x.kept j hj; exact ⟨by omega, this.2.1⟩)
  have atBody : x.addr x.controlIndex + 32 = x.addr x.bodyIndex := by
    have h := adr_eq x.pc (x := x.controlIndex) (y := x.bodyIndex) (J := 32) (by
      dsimp only [controlIndex, bodyIndex]; omega)
    exact (congrArg (x.addr x.controlIndex + ·)
      (by decide : (32 : BitVec 64) = BitVec.ofInt 64 32)).trans h
  rw [atBody] at run
  have final := ready.after frame pre.env world
  refine ⟨m1, run, frame, kept, final, count, ?_, by omega⟩
  exact (kept x.one List.mem_cons_self).trans unit

/-- The generic induction is instantiated by real condition, branch, decrement,
    body and backedge paths. Overflow preserves the enclosing leave/next targets. -/
theorem correct {Λ : List (Res D)} {bis : Expr D Γ Λ .bool} {tc : Nat}
    (lowered : lowE (reserved := reserved) L bis (frei Γ reserved) = some (x.condition, tc))
    (top : tc ≤ x.Ks) {l : Bool} {sc : List D.Lock} {outerLeave outerNext : W}
    (body : World D → Env D Γ → Ausgang (vertragVon D f) true Γ)
    (overflow : World D → Env D Γ → Ausgang (vertragVon D f) l Γ)
    (bodyRun : ∀ m σ ρ, x.Ready m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K (x.counter :: x.one :: x.pr)
        ⟨x.addr x.bodyIndex, x.fp⟩ m (x.addr x.backIndex) (x.addr x.exitIndex) x.pc
        (body σ ρ) reserved sc)
    (overflowRun : ∀ m σ ρ, x.Ready m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K x.pr
        ⟨x.addr x.overflowIndex, x.fp⟩ m (x.addr x.exitIndex) outerLeave outerNext
        (overflow σ ρ) reserved sc) :
    ∀ n m σ ρ, x.Entry n m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K x.pr ⟨x.pc, x.fp⟩ m
        (x.addr x.exitIndex) outerLeave outerNext
        (retryLauf body (fun σ ρ => let σ := σ.lese Λ bis.orte;
          (σ, wahr? (eval σ bis σ ρ))) overflow n σ ρ) reserved sc := by
  refine retry_runtime body (fun σ ρ => let σ := σ.lese Λ bis.orte;
    (σ, wahr? (eval σ bis σ ρ))) overflow x.Entry x.low ?_ ?_ ?_
  · intro n m σ ρ entry done
    obtain ⟨m1, run, frame, kept, ready⟩ := x.test_run lowered top entry.1
    simp only [show wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true from done, ↓reduceIte] at run
    exact ⟨m1, run, frame, ready.pre.env, ready.world, fun j hj => kept j (by
      simp only [List.mem_cons]; exact Or.inr (Or.inr hj))⟩
  · intro m σ ρ entry falseCond
    obtain ⟨m1, run, frame, kept, ready⟩ := x.test_run lowered top entry.1
    simp only [show ¬ wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true from falseCond, ↓reduceIte] at run
    have zero : x.read m1 x.counter 0 := by
      exact (kept x.counter List.mem_cons_self).trans entry.2.1
    have atOverflow : x.addr x.controlIndex +
        BitVec.ofInt 64 (16 * ((x.body.length : Int) + 3)) = x.addr x.overflowIndex :=
      adr_eq x.pc (x := x.controlIndex) (y := x.overflowIndex) (by
        dsimp only [controlIndex, overflowIndex]; omega)
    have counterInside : x.counter < x.K := by
      have := x.controls; have := x.room; have := x.layout.ks; unfold frei at *; omega
    have branch := brz_go (codeAt_left ready.control.code) counterInside ready.pre.small
      (retry_displacements _ _ _ x.sized).2.1 zero
    rw [atOverflow] at branch
    exact Sim.prefix x.low (run.trans branch) frame
      (fun j hj => kept j (by simp only [List.mem_cons]; exact Or.inr (Or.inr hj)))
      (overflowRun m1 _ ρ ready)
  · intro n m σ ρ entry falseCond
    obtain ⟨m1, testRun, testFrame, testKept, ready1⟩ := x.test_run lowered top entry.1
    simp only [show ¬ wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true from falseCond, ↓reduceIte] at testRun
    have start : x.Entry (n + 1) m1 (σ.lese Λ bis.orte) ρ := by
      refine ⟨ready1, ?_, ?_, entry.2.2.2⟩
      · exact (testKept x.counter List.mem_cons_self).trans entry.2.1
      · exact (testKept x.one (List.mem_cons_of_mem _ List.mem_cons_self)).trans entry.2.2.1
    obtain ⟨m2, fuelRun, fuelFrame, fuelKept, ready2, count, unit, fits⟩ := x.decrement start
    have prefixRun := testRun.trans fuelRun
    have prefixFrame := testFrame.trans fuelFrame
    have prefixKept : Keeps x.fp x.pr m m2 :=
      fun j hj => (fuelKept j (List.mem_cons_of_mem _ hj)).trans
        (testKept j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)))
    have pass := bodyRun m2 _ ρ ready2
    have back := ready2.back 0 (by simp only [List.length_singleton]; omega)
    simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci] at back
    have far : CodeFar (x.addr x.backIndex) 1 x.fp x.K :=
      codeFar_at ready2.pre.far (by
        simp only [code, retryHeader_length, backIndex]; omega)
    have dispatch := pass.counter_dispatch x.layout (counter := x.counter)
      (Or.inr List.mem_cons_self)
      (by have := x.controls; have := x.room; have := x.layout.ks; unfold frei at *; omega)
      count back far x.back_target
    have again : ∀ σ' ρ',
        (∃ m', Star ⟨x.addr x.bodyIndex, x.fp⟩ m2 ⟨x.pc, x.fp⟩ m' ∧
          AgreeW L x.fp x.lo x.K m2 m' ∧ EnvAt L m' x.fp ρ' reserved ∧
          WeltAt m' L σ' ∧ Keeps x.fp (x.counter :: x.one :: x.pr) m2 m' ∧
          x.read m' x.counter (BitVec.ofNat 64 n)) →
        ∃ m', Star ⟨x.pc, x.fp⟩ m ⟨x.pc, x.fp⟩ m' ∧
          AgreeW L x.fp x.lo x.K m m' ∧ Keeps x.fp x.pr m m' ∧ x.Entry n m' σ' ρ' := by
      intro σ' ρ' next
      obtain ⟨m3, run, frame, env, world, kept, read⟩ := next
      refine ⟨m3, prefixRun.trans run, prefixFrame.trans frame,
        prefixKept.trans (fun j hj => kept j (by simp only [List.mem_cons]; exact Or.inr (Or.inr hj))),
        ready2.after frame env world, read, ?_, fits⟩
      exact (kept x.one (List.mem_cons_of_mem _ List.mem_cons_self)).trans unit
    generalize hb : body (σ.lese Λ bis.orte) ρ = outcome at pass dispatch ⊢
    cases outcome with
    | ok σ' ρ' => exact again σ' ρ' dispatch
    | next h σ' ρ' => exact again σ' ρ' dispatch
    | leave h σ' ρ' =>
      exact Reach.prefix prefixRun prefixFrame prefixKept (by
        obtain ⟨m3, run, frame, env, world, kept⟩ := dispatch
        exact ⟨m3, run, frame, env, world,
          fun j hj => kept j (by simp only [List.mem_cons]; exact Or.inr (Or.inr hj))⟩)
    | zurueck | why | logik | hardware =>
      exact Sim.prefix x.low prefixRun prefixFrame prefixKept dispatch

end Gabbro.Stage0.Senke.Retrying.Image
