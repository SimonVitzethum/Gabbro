/- Fuel, invariant and current-state selection at a consuming round header. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Candidate
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {reserved : Nat}

structure Loop (x : Image L P f reserved) (Γ : Ctx) (Λ : List (Res D)) where
  selector : Selector x Γ Λ
  inv : Expr D Γ Λ .bool
  mass : Expr D Γ Λ (.int 0 x.bound)
  it mt : Nat
  invCode : lowE (reserved := reserved) L inv (x.s + 4) = some (x.invariant, it)
  massCode : lowE (reserved := reserved) L mass (x.s + 4) = some (x.measure, mt)
  invTop : it ≤ x.Ks
  massTop : mt ≤ x.Ks

namespace Loop
variable {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)} (q : Loop x Γ Λ)

def invW (σ : World D) (ρ : Env D Γ) : World D × Bool :=
  let σi := σ.lese Λ q.inv.orte
  (σi, wahr? (eval σi q.inv σi ρ))
def massW (σ : World D) (ρ : Env D Γ) : World D × Int :=
  let σm := σ.lese Λ q.mass.orte
  (σm, (eval σm q.mass σm ρ).n)
def sel (σ : World D) (ρ : Env D Γ) :=
  verbrauchSel x.table q.selector.member q.selector.edge σ ρ

def Entry (n : Nat) (m : Mem) (σ : World D) (ρ : Env D Γ) : Prop :=
  x.Ready m σ ρ ∧ x.read m x.counter (BitVec.ofNat 64 n) ∧ n ≤ x.fuel

variable {q} {n : Nat} {m : Mem} {σ : World D} {ρ : Env D Γ}

/-- Zero fuel jumps to the actual stop block before reading the invariant. -/
theorem zero (entry : q.Entry 0 m σ ρ) :
    Stops ⟨x.addr 2, x.fp⟩ m (logikCode (D := D) .schleife) := by
  obtain ⟨ready, read, bound⟩ := entry
  have jump := ready.branch 2 49 x.counter .stop 0 rfl (by consume_arith x)
    (by consume_arith x) (by consume_arith x)
    (by have := x.controls; have := x.scratch; have := x.layout.ks; omega)
    read (by consume_arith x)
  exact Stops.prefix (by simpa using jump) ready.stop

/-- Positive fuel is decremented in its reserved word, preserving all lexical
    variables and the surrounding protected words. -/
theorem fuel (entry : q.Entry (n + 1) m σ ρ) :
    ScanRun L x.fp x.lo x.K x.pr (x.addr 2) (x.addr 4) m (q.Entry n · σ ρ) := by
  obtain ⟨ready, read, bound⟩ := entry
  have room : x.s + 4 < x.K := by have := x.scratch; have := x.layout.ks; omega
  have controlRoom : x.counter < x.K := by have := x.controls; have := x.scratch; omega
  have fuelEq := counter_fuel_step n (by have := x.bounds.1; omega)
  have branch := ready.branch 2 49 x.counter .stop _ rfl (by consume_arith x)
    (by consume_arith x) (by consume_arith x) controlRoom read (by consume_arith x)
  simp only [fuelEq.1, ↓reduceIte] at branch
  have code := (ready.slice 3 (.code [ci 1 (x.s + 4) 1 0, ci 4 x.counter x.counter (x.s + 4)])
    _ rfl rfl).1
  obtain ⟨oneRun, oneFrame, oneReady, oneRead⟩ := ready.literal
    (codeAt_left (a := [ci 1 (x.s + 4) 1 0]) code)
    (by rw [← q.selector.origin]; omega) (by omega) room (by decide)
  have tail := (codeAt_right (a := [ci 1 (x.s + 4) 1 0]) code).agree oneFrame
    (by have := (ready.slice 3 (.code [ci 1 (x.s + 4) 1 0,
      ci 4 x.counter x.counter (x.s + 4)]) _ rfl rfl).2
        exact codeFar_right (n := 1) (k := 1) this)
  have counterRead := Image.read_agree oneFrame ready.frame (by have := x.controls;
    have := x.scratch; omega) (by omega) read
  have run := Image.binary_to tail oneReady.frame x.small controlRoom controlRoom room
    counterRead oneRead (g := fun a b => some (a - b)) rfl (by decide) rfl
  let m1 := write m (slot x.fp (BitVec.ofNat 64 (x.s + 4))) 8 1
  let value := BitVec.ofNat 64 (n + 1) - 1
  let m2 := write m1 (slot x.fp (BitVec.ofNat 64 x.counter)) 8 value.toNat
  have counterFrame : Agree x.fp x.counter x.K m1 m2 :=
    agree_write oneReady.frame.room (Nat.le_refl _) controlRoom value.toNat
  have frame := (oneFrame.mono (by have := x.controls; have := x.scratch; omega)).trans counterFrame
  have finalReady := oneReady.reserved value x.controls.1
    (by have := x.controls; omega) (by rw [← q.selector.origin]; have := x.scratch; omega)
  refine ⟨m2, ?_, agreeW_of (frame.mono x.controls.1), ?_, finalReady, ?_, by omega⟩
  · have total := branch.trans (oneRun.trans run)
    simpa only [show x.addr 3 + 16 + 16 = x.addr 4 by consume_arith x] using total
  · have k1 := keeps_of_agree oneFrame ready.frame.room
      (fun j hj => by have := x.protected j hj; omega) (by omega)
    have k2 := keeps_write oneReady.frame.room controlRoom
      (fun j hj => by have := x.protected j hj; have := x.scratch; omega)
      (fun hj => (x.protected _ hj).2.1 rfl) value.toNat
    exact k1.trans k2
  · have result := rd_same oneReady.frame controlRoom value
    simpa only [value, fuelEq.2] using result

/-- The head executes the invariant in exactly its canonical read world. -/
theorem head (entry : q.Entry (n + 1) m σ ρ) :
    if (q.invW σ ρ).2 = false then
      Stops ⟨x.addr 2, x.fp⟩ m (logikCode (D := D) .schleife)
    else ScanRun L x.fp x.lo x.K x.pr (x.addr 2) (x.addr 6) m
      (fun m' => q.Entry n m' (q.invW σ ρ).1 ρ) := by
  obtain ⟨m1, fuelRun, fuelFrame, fuelKept, ready1, counterRead, bound⟩ := fuel entry
  let σi := (q.invW σ ρ).1
  have invReady : x.Ready m1 σi ρ := ready1.lese
  obtain ⟨m2, invRun, invFrame, invKept, ready2, localFrame, value, read, encoding⟩ :=
    invReady.eval 4 (by rw [← q.selector.origin]; omega) q.invCode q.invTop rfl trivial
  have counterRead2 := (invKept x.counter (by simp)).trans counterRead
  have valueEq : value = Runner.IR.bool (q.invW σ ρ).2 := by simpa only [Enc, invW, bool_word] using encoding
  subst value
  have branch := ready2.branch 5 49 (x.s + 4) .stop _ rfl (by consume_arith x)
    (by consume_arith x) (by consume_arith x)
    (by have := x.scratch; have := x.layout.ks; omega) read (by consume_arith x)
  cases truth : (q.invW σ ρ).2 with
  | false =>
    simp only [truth, ↓reduceIte]
    simp only [truth, Runner.IR.bool, ↓reduceIte] at branch
    exact Stops.prefix (fuelRun.trans (invRun.trans branch)) ready2.stop
  | true =>
    simp only [truth, Bool.true_eq_false, ↓reduceIte]
    simp only [truth, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch
    exact ⟨m2, fuelRun.trans (invRun.trans branch), fuelFrame.trans invFrame,
      fuelKept.trans (fun j hj => invKept j (by simp [hj])), ready2, counterRead2, bound⟩

/-- Compose the invariant header and the complete current-world selector. -/
theorem round (entry : q.Entry (n + 1) m σ ρ) (valid : (q.invW σ ρ).2 ≠ false) :
    let answer := q.sel (q.invW σ ρ).1 ρ
    ScanRun L x.fp x.lo x.K x.pr (x.addr 2)
      (if answer.2.1.isSome then x.addr 37 else x.addr 34) m
      (fun m' => q.selector.CandResult answer.1 ρ answer.2.1 answer.2.2 m' ∧
        x.read m' x.counter (BitVec.ofNat 64 n)) := by
  have start := head entry
  simp only [valid, ↓reduceIte] at start
  apply start.bind
  intro m1 h
  obtain ⟨ready, read, bound⟩ := h
  let σr := ((q.invW σ ρ).1).lese Λ (q.selector.member.orte ++ q.selector.edge.orte)
  have readReady : x.Ready m1 σr ρ := ready.lese
  obtain ⟨m2, scan, frame, kept, result⟩ := q.selector.selection σr ρ readReady
  exact ⟨m2, scan, frame, (fun j hj => kept j (by simp [hj])), result,
    (kept x.counter (by simp)).trans read⟩

end Loop
end Gabbro.Stage0.Senke.Consuming
