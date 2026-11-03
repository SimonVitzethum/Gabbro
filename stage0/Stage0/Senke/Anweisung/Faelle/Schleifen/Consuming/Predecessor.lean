/- Concrete predecessor scan, including self edges and borrowed membership. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Operands
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}

structure Selector {reserved : Nat} (x : Image L P f reserved) (Γ : Ctx) (Λ : List (Res D)) where
  member : Expr D (.index (D.count x.table) :: Γ) Λ .bool
  edge : Expr D (.index (D.count x.table) :: .index (D.count x.table) :: Γ) Λ .bool
  mt et : Nat
  memberCode : lowE (reserved := reserved) L member (x.s + 4) = some (x.member, mt)
  edgeCode : lowE (reserved := reserved) L edge (x.s + 4) = some (x.edge, et)
  memberTop : mt ≤ x.Ks
  edgeTop : et ≤ x.Ks
  origin : x.s = frei Γ reserved
  indexWidth : valueWords (.index (D.count x.table)) = 1

namespace Selector
variable {reserved : Nat} {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)}
variable (q : Selector x Γ Λ) (σ : World D) (ρ : Env D Γ)

def memberAt (k : Wert D (.index (D.count x.table))) : Bool :=
  wahr? (eval σ q.member σ (.cons k ρ))
def edgeAt (a b : Wert D (.index (D.count x.table))) : Bool :=
  wahr? (eval σ q.edge σ (.cons a (.cons b ρ)))

structure PredDone (candidate : Wert D (.index (D.count x.table))) (live : Bool) (m : Mem) : Prop where
  ready : x.Ready m σ ρ
  candidateRead : x.read m x.s (BitVec.ofInt 64 candidate.n)
  liveRead : x.read m (x.s + 2) (Runner.IR.bool live)

structure PredState (candidate : Wert D (.index (D.count x.table))) (live : Bool)
    (j : Nat) (m : Mem) : Prop extends q.PredDone σ ρ candidate live m where
  predecessorRead : x.read m (x.s + 1) (BitVec.ofNat 64 j)

variable {q σ ρ} {candidate : Wert D (.index (D.count x.table))} {live : Bool}
variable {m m' : Mem} {j d : Nat}

theorem PredDone.agree (h : q.PredDone σ ρ candidate live m)
    (a : Agree x.fp d x.K m m') (above : x.s + 3 ≤ d) (room : d ≤ x.K) :
    q.PredDone σ ρ candidate live m' :=
  ⟨h.ready.agree a (by rw [← q.origin]; omega)
      (by rw [← x.abi]; have := x.controls; have := x.scratch; omega) room,
    Image.read_agree a h.ready.frame (by omega) room h.candidateRead,
    Image.read_agree a h.ready.frame (by omega) room h.liveRead⟩

theorem PredState.agree (h : q.PredState σ ρ candidate live j m)
    (a : Agree x.fp d x.K m m') (above : x.s + 3 ≤ d) (room : d ≤ x.K) :
    q.PredState σ ρ candidate live j m' :=
  ⟨h.toPredDone.agree a above room,
    Image.read_agree a h.ready.frame (by omega) room h.predecessorRead⟩

/-- Increment and backedge of the predecessor scan. -/
theorem predecessor_next (h : q.PredState σ ρ candidate live j m) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 28) (x.addr 14) m
      (q.PredState σ ρ candidate live (j + 1)) := by
  apply (h.ready.increment (i := 28) (j := 29)
    (by rw [← q.origin]; omega) (by omega) (by omega) h.predecessorRead rfl
    (by consume_arith x)).bind
  intro m' state
  obtain ⟨ready, frame, others, read⟩ := state
  have back := ready.jump 29 14 .predecessor rfl (by consume_arith x)
    (by consume_arith x) (by consume_arith x)
  exact ⟨m', back, AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _,
    ⟨⟨ready, (others x.s (by omega) (by omega)).trans h.candidateRead,
      (others (x.s + 2) (by omega) (by omega)).trans h.liveRead⟩, read⟩⟩

/-- Execute one nonexhausted predecessor. Its Boolean is the canonical
    member && edge && !same expression, with predecessor as the first binder. -/
theorem predecessor_test (a : Wert D (.index (D.count x.table))) (ha : a.n = j)
    (h : q.PredState σ ρ candidate live j m) :
    let hit := q.memberAt σ ρ a && q.edgeAt σ ρ a candidate && !decide (a.n = candidate.n)
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 16)
      (if hit then x.addr 31 else x.addr 14) m
      (fun m' => if hit then q.PredDone σ ρ candidate live m'
        else q.PredState σ ρ candidate live (j + 1) m') := by
  have room : x.s + 4 ≤ x.K := by have := x.scratch; have := x.layout.ks; omega
  have aRead : x.read m (x.s + 1) (BitVec.ofInt 64 a.n) := by
    rw [ha, BitVec.ofInt_natCast]; exact h.predecessorRead
  apply (h.ready.same (a := a) (b := candidate) (by rw [← q.origin]; omega)
    aRead h.candidateRead).bind
  intro m1 result
  obtain ⟨ready1, frame1, sameRead⟩ := result
  have state1 := h.agree frame1 (by omega) room
  have branch1 := ready1.branch 17 20 (x.s + 4) .different _ rfl
    (by consume_arith x) (by consume_arith x) (by consume_arith x)
    (by omega) sameRead (by consume_arith x)
  by_cases self : a.n = candidate.n
  · simp only [self, decide_true, Bool.not_true, Bool.and_false, ↓reduceIte]
    simp only [self, decide_true, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch1
    have skip := ready1.jump 18 28 .predecessorNext rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x)
    exact ScanRun.prefix (branch1.trans skip) (predecessor_next state1)
  · simp only [self, decide_false, Bool.not_false, Bool.and_true]
    simp only [self, decide_false, Runner.IR.bool, ↓reduceIte] at branch1
    apply ScanRun.prefix branch1
    apply (ready1.borrow q.origin q.indexWidth q.memberCode q.memberTop
      state1.candidateRead (by rw [ha, BitVec.ofInt_natCast]; exact state1.predecessorRead)).bind
    intro m2 result
    obtain ⟨ready2, frame2, memberRead⟩ := result
    have state2 := state1.agree frame2 (by omega) (by omega)
    have branch2 := ready2.branch 23 28 (x.s + 4) .predecessorNext _ rfl
      (by consume_arith x) (by consume_arith x) (by consume_arith x)
      (by omega) memberRead (by consume_arith x)
    cases membership : q.memberAt σ ρ a with
    | false =>
      simp only [memberAt] at membership
      simp only [membership, Runner.IR.bool, ↓reduceIte] at branch2
      simp only [memberAt, membership, Bool.false_and, ↓reduceIte]
      exact ScanRun.prefix branch2 (predecessor_next state2)
    | true =>
      have memberTrue : wahr? (eval σ q.member σ (.cons a ρ)) = true := membership
      simp only [memberTrue, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch2
      have predRead : x.read m2 (x.s + 1) (BitVec.ofInt 64 a.n) := by
        rw [ha, BitVec.ofInt_natCast]; exact state2.predecessorRead
      have edgeReady : x.Ready m2 σ (.cons a (.cons candidate ρ)) :=
        { ready2 with env := envAt_cons
            (envAt_cons ready2.env (ValueAt.of_enc q.indexWidth state2.candidateRead rfl))
            (ValueAt.of_enc q.indexWidth predRead rfl) }
      apply ScanRun.prefix branch2
      apply (edgeReady.eval 24 (by simp only [frei, contextWords_cons, q.indexWidth];
        rw [← q.origin]; omega) q.edgeCode q.edgeTop rfl trivial).bind
      intro m3 result
      obtain ⟨ready3, frame3, value, edgeRead, encoding⟩ := result
      have state3 := state2.agree frame3 (by omega) room
      have edgeWord : value = Runner.IR.bool (q.edgeAt σ ρ a candidate) := by
        simpa only [Enc, edgeAt, bool_word] using encoding
      subst value
      have branch3 := state3.ready.branch 25 28 (x.s + 4) .predecessorNext _ rfl
        (by consume_arith x) (by consume_arith x) (by consume_arith x)
        (by omega) edgeRead (by consume_arith x)
      cases edgeValue : q.edgeAt σ ρ a candidate with
      | false =>
        simp only [edgeValue, Runner.IR.bool, ↓reduceIte] at branch3
        simp only [membership, edgeValue, Bool.true_and, ↓reduceIte]
        exact ScanRun.prefix branch3 (predecessor_next state3)
      | true =>
        simp only [edgeValue, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch3
        simp only [membership, edgeValue, Bool.true_and, ↓reduceIte]
        have reject := state3.ready.jump 26 31 .candidateNext rfl (by consume_arith x)
          (by consume_arith x) (by consume_arith x)
        exact ⟨m3, branch3.trans reject, AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, state3.toPredDone⟩

/-- Instantiate the existing suffix induction with actual bound and scan edges. -/
theorem predecessor_path (candidate : Wert D (.index (D.count x.table))) (live : Bool) :
    ∀ remaining j, j + remaining = (D.count x.table).toNat → ∀ m,
      q.PredState σ ρ candidate live j m →
      let answer := keinVorgaenger (idxAb (D.count x.table) j remaining)
        (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) candidate
      ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 14)
        (if answer then x.addr 37 else x.addr 31) m (q.PredDone σ ρ candidate live) := by
  apply predecessor_scan (D.count x.table) candidate (q.memberAt σ ρ) (q.edgeAt σ ρ)
    (x.addr 14) (x.addr 37) (x.addr 31) (q.PredState σ ρ candidate live)
    (fun _ => q.PredDone σ ρ candidate live)
  · intro mem h
    apply (h.ready.bound (i := 14) (by rw [← q.origin]; omega) (by omega)
      (by have := x.bounds.2.2.1; simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.predecessorRead rfl (by consume_arith x)).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have notLess : decide (((D.count x.table).toNat : Int) < D.count x.table) = false := by simp; omega
    rw [notLess] at read
    have exit := ready.branch 15 37 (x.s + 4) .selected _ rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x) (by have := x.scratch; have := x.layout.ks; omega)
      read (by consume_arith x)
    exact ⟨mem', by simpa [Runner.IR.bool] using exit,
      AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, state.toPredDone⟩
  · intro j a ha hit mem h
    apply (h.ready.bound (i := 14) (by rw [← q.origin]; omega) (by omega)
      (by have := a.le_hi; have := a.lo_le; have := x.bounds.2.2.1;
          simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.predecessorRead rfl (by consume_arith x)).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have less : decide ((j : Int) < D.count x.table) = true := by have := a.le_hi; simp; omega
    rw [less] at read
    have pass := ready.branch 15 37 (x.s + 4) .selected _ rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x) (by have := x.scratch; have := x.layout.ks; omega)
      read (by consume_arith x)
    apply ScanRun.prefix (by simpa [Runner.IR.bool] using pass)
    simpa only [hit, ↓reduceIte] using predecessor_test a ha state
  · intro j a ha miss mem h
    apply (h.ready.bound (i := 14) (by rw [← q.origin]; omega) (by omega)
      (by have := a.le_hi; have := a.lo_le; have := x.bounds.2.2.1;
          simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.predecessorRead rfl (by consume_arith x)).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have less : decide ((j : Int) < D.count x.table) = true := by have := a.le_hi; simp; omega
    rw [less] at read
    have pass := ready.branch 15 37 (x.s + 4) .selected _ rfl (by consume_arith x)
      (by consume_arith x) (by consume_arith x) (by have := x.scratch; have := x.layout.ks; omega)
      read (by consume_arith x)
    apply ScanRun.prefix (by simpa [Runner.IR.bool] using pass)
    simpa only [miss, ↓reduceIte] using predecessor_test a ha state

end Selector
end Gabbro.Stage0.Senke.Consuming
