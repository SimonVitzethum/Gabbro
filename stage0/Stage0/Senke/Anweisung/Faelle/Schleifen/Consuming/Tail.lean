/- Measure/body boundaries and the two post-body continuations. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Head
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming.Loop
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {reserved : Nat} {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)}
variable (q : Loop x Γ Λ) {n : Nat} {m : Mem} {σ : World D} {ρ : Env D Γ}

/-- Save the measured pre-body value, then install the selected body binder. -/
theorem before_body (k : Wert D (.index (D.count x.table)))
    (h : q.selector.CandResult σ ρ (some k) true m)
    (fuelRead : x.read m x.counter (BitVec.ofNat 64 n)) :
    let measured := q.massW σ ρ
    ∃ m', Star ⟨x.at 37, x.fp⟩ m ⟨x.at 39, x.fp⟩ m' ∧
      AgreeW L x.fp x.lo x.K m m' ∧ Keeps x.fp x.pr m m' ∧
      x.Ready m' measured.1 (.cons k ρ) ∧
      x.read m' x.counter (BitVec.ofNat 64 n) ∧
      x.read m' x.saved (BitVec.ofInt 64 measured.2) := by
  let measured := q.massW σ ρ
  have ready : x.Ready m measured.1 ρ := h.ready.lese
  obtain ⟨m1, measureRun, measureFrame, measureKept, ready1, localFrame, value, read, encoding⟩ :=
    ready.eval 37 (by rw [← q.selector.origin]; omega) q.massCode q.massTop rfl trivial
  have valueEq : value = BitVec.ofInt 64 measured.2 := encoding
  subst value
  have counterRead := (measureKept x.counter (by simp)).trans fuelRead
  have candidateRead := Image.read_agree localFrame h.ready.frame (by omega)
    (by have := x.scratch; have := x.layout.ks; omega) (h.candidateRead k rfl)
  obtain ⟨m2, saveRun, saveFrame, ready2, saveKept, savedRead, others⟩ :=
    ready1.save (i := 38) rfl (by have := x.scratch; have := x.layout.ks; omega) read
      (by have := x.controls; omega) x.controls.2.2 rfl
      (by rw [← q.selector.origin]; have := x.scratch; have := x.layout.ks; omega)
      (by consume_arith x)
  have binderRead : x.read m2 x.s (BitVec.ofInt 64 k.n) :=
    (others x.s (by have := x.scratch; have := x.layout.ks; omega)
      (by have := x.controls; have := x.scratch; omega)).trans candidateRead
  exact ⟨m2, measureRun.trans saveRun, measureFrame.trans saveFrame,
    (fun j hj => (saveKept j (by simp [hj])).trans (measureKept j (by simp [hj]))),
    { ready2 with env := envAt_cons ready2.env (ValueAt.of_enc q.selector.indexWidth binderRead rfl) },
    (saveKept x.counter (by simp)).trans counterRead, savedRead⟩

/-- The typed measure supplies both range conjuncts of verbrauchLauf. -/
theorem measure_bounds (σ : World D) (ρ : Env D Γ) :
    0 ≤ (q.massW σ ρ).2 ∧ (q.massW σ ρ).2 ≤ x.bound :=
  ⟨(eval (q.massW σ ρ).1 q.mass (q.massW σ ρ).1 ρ).lo_le,
    (eval (q.massW σ ρ).1 q.mass (q.massW σ ρ).1 ρ).le_hi⟩

/-- Execute either copy of the complete post-body measure check. -/
theorem after_body (i : Nat) (which : i = 41 ∨ i = 44) (old : Int)
    (oldBound : -2 ^ 63 ≤ old ∧ old < 2 ^ 63)
    (h : x.Ready m σ ρ) (fuelRead : x.read m x.counter (BitVec.ofNat 64 n))
    (savedRead : x.read m x.saved (BitVec.ofInt 64 old)) :
    let measured := q.massW σ ρ
    if 0 ≤ measured.2 ∧ measured.2 ≤ x.bound ∧ measured.2 < old then
      ScanRun L x.fp x.lo x.K x.pr (x.at i) (x.at (i + 1)) m
        (fun m' => x.Ready m' measured.1 ρ ∧ x.read m' x.counter (BitVec.ofNat 64 n))
    else Stops ⟨x.at i, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have bounds := q.measure_bounds σ ρ
  have found : x.fragment[i]? = some (.code (decrease (x.s + 4) x.saved
      (logikCode (D := D) .schleife) x.bound x.measure)) := by
    rcases which with rfl | rfl <;> rfl
  have pre := h.pre i (x.s + 4) _ (by rw [← q.selector.origin]; omega) found
  have checked := decrease_ok q.massCode q.massTop (by have := x.scratch; omega) x.layout
    pre h.world (by have := x.controls; have := x.scratch; omega) x.bounds.2.1
    x.bounds.2.2.2 oldBound savedRead
  have endAt : x.at i + BitVec.ofNat 64 (16 * (decrease (x.s + 4) x.saved
      (logikCode (D := D) .schleife) x.bound x.measure).length) = x.at (i + 1) := by
    rcases which with rfl | rfl <;> consume_arith x
  by_cases falls : (q.massW σ ρ).2 < old
  · simp only [bounds.1, bounds.2, falls, and_self, ↓reduceIte]
    simp only [show (eval (σ.lese Λ q.mass.orte) q.mass (σ.lese Λ q.mass.orte) ρ).n < old from falls,
      ↓reduceIte] at checked
    obtain ⟨mem, run, frame, kept, ready, localFrame, value, read, encoding⟩ := h.ok checked
      endAt (by rw [← q.selector.origin]; omega) (by omega)
      (by have := x.scratch; have := x.layout.ks; omega)
    exact ⟨mem, run, frame, (fun j hj => kept j (by simp [hj])), ready.lese,
      (kept x.counter (by simp)).trans fuelRead⟩
  · simp only [falls, and_false, ↓reduceIte]
    simpa only [show ¬ (eval (σ.lese Λ q.mass.orte) q.mass (σ.lese Λ q.mass.orte) ρ).n < old from falls,
      ↓reduceIte] using checked

/-- The leave continuation checks its invariant after the falling measure. -/
theorem leave_invariant (h : x.Ready m σ ρ) :
    if (q.invW σ ρ).2 = true then
      Reach L x.fp x.lo x.K x.pr ⟨x.at 45, x.fp⟩ m (x.at 50) (q.invW σ ρ).1 ρ reserved
    else Stops ⟨x.at 45, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have ready : x.Ready m (q.invW σ ρ).1 ρ := h.lese
  obtain ⟨mem, run, frame, kept, ready', localFrame, value, read, encoding⟩ := ready.eval 45
    (by rw [← q.selector.origin]; omega) q.invCode q.invTop rfl trivial
  have valueEq : value = Runner.IR.bool (q.invW σ ρ).2 := by
    simpa only [Enc, invW, bool_word] using encoding
  subst value
  have branch := ready'.branch 46 49 (x.s + 4) .stop _ rfl (by consume_arith x)
    (by consume_arith x) (by consume_arith x)
    (by have := x.scratch; have := x.layout.ks; omega) read (by consume_arith x)
  cases truth : (q.invW σ ρ).2 with
  | false =>
    simp only [truth, Bool.false_eq_true, ↓reduceIte]
    simp only [truth, Runner.IR.bool, ↓reduceIte] at branch
    exact Stops.prefix (run.trans branch) ready'.stop
  | true =>
    simp only [truth, ↓reduceIte]
    simp only [truth, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch
    have exit := ready'.jump 47 50 .done rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x)
    exact ⟨mem, run.trans (branch.trans exit), frame, ready'.env, ready'.world,
      fun j hj => kept j (by simp [hj])⟩

end Gabbro.Stage0.Senke.Consuming.Loop
