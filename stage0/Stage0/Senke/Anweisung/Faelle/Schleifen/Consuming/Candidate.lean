/- Candidate selection from the current represented world. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Predecessor
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming.Selector
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {reserved : Nat} {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)}
variable (q : Selector x Γ Λ) (σ : World D) (ρ : Env D Γ)

structure CandState (q : Selector x Γ Λ) (σ : World D) (ρ : Env D Γ) (j : Nat) (live : Bool) (m : Mem) : Prop where
  ready : x.Ready m σ ρ
  candidateRead : x.read m x.s (BitVec.ofNat 64 j)
  liveRead : x.read m (x.s + 2) (Runner.IR.bool live)

structure CandResult (q : Selector x Γ Λ) (σ : World D) (ρ : Env D Γ) (choice : Option (Wert D (.index (D.count x.table))))
    (live : Bool) (m : Mem) : Prop where
  ready : x.Ready m σ ρ
  candidateRead : ∀ k, choice = some k → x.read m x.s (BitVec.ofInt 64 k.n)
  liveRead : x.read m (x.s + 2) (Runner.IR.bool live)

variable {q σ ρ} {j : Nat} {live : Bool} {m m' : Mem}

theorem CandState.agree (h : q.CandState σ ρ j live m) {d : Nat}
    (a : Agree x.fp d x.K m m') (above : x.s + 3 ≤ d) (room : d ≤ x.K) :
    q.CandState σ ρ j live m' :=
  ⟨h.ready.agree a (by rw [← q.origin]; omega)
      (by rw [← x.abi]; have := x.controls; have := x.scratch; omega) room,
    Image.read_agree a h.ready.frame (by omega) room h.candidateRead,
    Image.read_agree a h.ready.frame (by omega) room h.liveRead⟩

/-- Rejected and absent candidates execute the same increment/backedge. -/
theorem candidate_next (h : q.CandState σ ρ j live m) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 31) (x.addr 8) m
      (q.CandState σ ρ (j + 1) live) := by
  apply (h.ready.increment (i := 31) (j := 32)
    (by rw [← q.origin]) (Nat.le_refl _) (by omega) h.candidateRead rfl
    (by consume_arith x)).bind
  intro mem result
  obtain ⟨ready, frame, other, read⟩ := result
  have back := ready.jump 32 8 .candidate rfl (by consume_arith x)
    (by consume_arith x) (by consume_arith x)
  exact ⟨mem, back, AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, ready, read,
    (other (x.s + 2) (by omega) (by omega)).trans h.liveRead⟩

/-- One candidate: evaluate membership, and if live scan all predecessors. -/
theorem candidate_test (k : Wert D (.index (D.count x.table))) (hk : k.n = j)
    (h : q.CandState σ ρ j live m) :
    let minimal := istMinimalVerbrauch (alleIndizes (D.count x.table))
      (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 10)
      (if minimal then x.addr 37 else x.addr 8) m
      (fun m' => if minimal then q.CandResult σ ρ (some k) true m'
        else q.CandState σ ρ (j + 1) (live || q.memberAt σ ρ k) m')
 := by
  have room : x.s + 4 ≤ x.K := by have := x.scratch; have := x.layout.ks; omega
  have index : x.read m x.s (BitVec.ofInt 64 k.n) := by
    rw [hk, BitVec.ofInt_natCast]; exact h.candidateRead
  have memberReady : x.Ready m σ (.cons k ρ) :=
    { h.ready with env := envAt_cons h.ready.env (ValueAt.of_enc q.indexWidth index rfl) }
  have evaluated := memberReady.eval 10 (by
    simp only [frei, contextWords_cons, q.indexWidth]; rw [← q.origin]; omega)
    q.memberCode q.memberTop rfl trivial
  by_cases memberTrue : q.memberAt σ ρ k = true
  · simp only [istMinimalVerbrauch, memberTrue, Bool.true_and]
    apply evaluated.bind
    intro m1 result
    obtain ⟨ready1, frame1, value, read, encoding⟩ := result
    have state1 := h.agree frame1 (by omega) room
    have valueOne : value = 1 := by simpa only [Enc, memberAt, memberTrue] using encoding
    subst value
    have pass := state1.ready.branch 11 31 (x.s + 4) .candidateNext 1 rfl
      (by consume_arith x) (by consume_arith x) (by consume_arith x)
      (by omega) read (by consume_arith x)
    have pass' : Star ⟨x.addr 11, x.fp⟩ m1 ⟨x.addr 12, x.fp⟩ m1 := by simpa using pass
    apply ScanRun.prefix pass'
    apply (state1.ready.literals (i := 12) (a := x.s + 2) (b := x.s + 1)
      rfl (by rw [← q.origin]; omega) (by omega) (by omega) (by omega)
      (by omega) (by decide) (by decide) (by consume_arith x)).bind
    intro m2 result
    obtain ⟨ready2, frame2, flag, predecessorRead⟩ := result
    have candidateRead : x.read m2 x.s (BitVec.ofInt 64 k.n) :=
      Image.read_agree frame2 state1.ready.frame (by omega) (by omega)
        (by rw [hk, BitVec.ofInt_natCast]; exact state1.candidateRead)
    have initial : q.PredState σ ρ k true 0 m2 :=
      ⟨⟨ready2, candidateRead, flag⟩, predecessorRead⟩
    have scan := q.predecessor_path σ ρ k true (D.count x.table).toNat 0
      (by omega) m2 initial
    rw [← alleIndizes_ab] at scan
    have entry : x.addr 13 = x.addr 14 := by consume_arith x
    rw [entry]
    generalize answerEq : keinVorgaenger (alleIndizes (D.count x.table))
      (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k = answer at scan ⊢
    cases answer with
    | true =>
      simp only [↓reduceIte] at scan ⊢
      exact scan.map (fun _ state => ⟨state.ready, by
        intro selected eq; cases eq; exact state.candidateRead, state.liveRead⟩)
    | false =>
      simp only [↓reduceIte] at scan ⊢
      apply scan.bind
      intro m3 state3
      have next := candidate_next (q := q) (σ := σ) (ρ := ρ)
        (j := j) (live := true) ⟨state3.ready, by
          rw [← BitVec.ofInt_natCast, ← hk]; exact state3.candidateRead, state3.liveRead⟩
      simpa only [memberTrue, Bool.or_true] using next
  · have memberFalse : q.memberAt σ ρ k = false := by
      cases value : q.memberAt σ ρ k <;> simp_all
    simp only [istMinimalVerbrauch, memberFalse, Bool.false_and, ↓reduceIte, Bool.or_false]
    apply evaluated.bind
    intro m1 result
    obtain ⟨ready1, frame1, value, read, encoding⟩ := result
    have state1 := h.agree frame1 (by omega) room
    have valueZero : value = 0 := by simpa only [Enc, memberAt, memberFalse] using encoding
    subst value
    have reject := state1.ready.branch 11 31 (x.s + 4) .candidateNext 0 rfl
      (by consume_arith x) (by consume_arith x) (by consume_arith x)
      (by omega) read (by consume_arith x)
    exact ScanRun.prefix (by simpa using reject) (candidate_next state1)

/-- The scan result is exactly verbrauchWahlAux on the current state. -/
theorem candidate_path : ∀ remaining j, j + remaining = (D.count x.table).toNat →
    ∀ live m, q.CandState σ ρ j live m →
    let choice := verbrauchWahlAux (alleIndizes (D.count x.table))
      (idxAb (D.count x.table) j remaining) (q.memberAt σ ρ) (q.edgeAt σ ρ)
      (fun a b => decide (a.n = b.n))
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 8)
      (if choice.isSome then x.addr 37 else x.addr 34) m
      (q.CandResult σ ρ choice (live || (idxAb (D.count x.table) j remaining).any (q.memberAt σ ρ))) := by
  apply candidate_scan (D.count x.table) (q.memberAt σ ρ) (q.edgeAt σ ρ)
    (x.addr 8) (x.addr 37) (x.addr 34) (q.CandState σ ρ) (q.CandResult σ ρ)
  · intro live mem h
    apply (h.ready.bound (i := 8) (by rw [← q.origin]; omega) (by omega)
      (by have := x.bounds.2.2.1; simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.candidateRead rfl (by consume_arith x)).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have notLess : decide (((D.count x.table).toNat : Int) < D.count x.table) = false := by simp; omega
    rw [notLess] at read
    have exit := ready.branch 9 34 (x.s + 4) .exhausted 0 rfl
      (by consume_arith x) (by consume_arith x) (by consume_arith x)
      (by have := x.scratch; have := x.layout.ks; omega) read (by consume_arith x)
    exact ⟨mem', by simpa [Runner.IR.bool] using exit,
      AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, ready, by intro _ impossible; cases impossible,
      state.liveRead⟩
  · intro j k hk live mem h
    have iteration :
        let minimal := istMinimalVerbrauch (alleIndizes (D.count x.table))
          (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k
        ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 8)
          (if minimal then x.addr 37 else x.addr 8) mem
          (fun m' => if minimal then q.CandResult σ ρ (some k) true m'
            else q.CandState σ ρ (j + 1) (live || q.memberAt σ ρ k) m') := by
      apply (h.ready.bound (i := 8) (by rw [← q.origin]; omega) (by omega)
      (by have := k.le_hi; have := k.lo_le; have := x.bounds.2.2.1;
          simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.candidateRead rfl (by consume_arith x)).bind
      intro mem' result
      obtain ⟨ready, frame, read⟩ := result
      have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
      have less : decide ((j : Int) < D.count x.table) = true := by have := k.le_hi; simp; omega
      rw [less] at read
      have pass := ready.branch 9 34 (x.s + 4) .exhausted 1 rfl
        (by consume_arith x) (by consume_arith x) (by consume_arith x)
        (by have := x.scratch; have := x.layout.ks; omega) read (by consume_arith x)
      have test := candidate_test k hk state
      exact ScanRun.prefix (by simpa [Runner.IR.bool] using pass) test
    split <;> simpa only [*, ↓reduceIte] using iteration

/-- Initialize both selector words, scan the entire index domain and retain
    the canonical empty/cyclic distinction in the live flag. -/
theorem selection (h : x.Ready m σ ρ) :
    let choice := verbrauchWahl (alleIndizes (D.count x.table))
      (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n))
    let live := !((alleIndizes (D.count x.table)).all fun k => !(q.memberAt σ ρ k))
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 6)
      (if choice.isSome then x.addr 37 else x.addr 34) m (q.CandResult σ ρ choice live) := by
  apply (h.literals (i := 6) (a := x.s) (b := x.s + 2) rfl
    (by rw [← q.origin]; omega) (by omega)
    (by have := x.scratch; have := x.layout.ks; omega)
    (by have := x.scratch; have := x.layout.ks; omega)
    (by omega) (by decide) (by decide) (by consume_arith x)).bind
  intro mem result
  obtain ⟨ready, frame, zero, flag⟩ := result
  have scan := q.candidate_path σ ρ (D.count x.table).toNat 0 (by omega) false mem ⟨ready, zero, flag⟩
  rw [← alleIndizes_ab] at scan
  simpa only [verbrauchWahl, Bool.false_or, List.any_eq_not_all_not,
    show x.addr 7 = x.addr 8 by consume_arith x] using scan

end Gabbro.Stage0.Senke.Consuming.Selector
