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

private theorem candidate_width_append (a b : List Piece) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp only [List.nil_append, width, Nat.zero_add]
  | cons a rest ih => simp only [List.cons_append, width, ih, Nat.add_assoc]

private theorem candidate_offset_step {i : Nat} {piece : Piece}
    (found : x.fragment[i]? = some piece) : x.offset (i + 1) = x.offset i + piece.width := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = piece := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  simp only [Image.offset, List.take_succ_eq_append_getElem inside, element,
    candidate_width_append, width, Nat.add_zero]

private theorem candidate_offset_bound (i : Nat) : x.offset i ≤ x.code.length := by
  have splitWidth := congrArg width (List.take_append_drop i x.fragment)
  rw [candidate_width_append] at splitWidth
  calc
    x.offset i ≤ x.offset i + width (x.fragment.drop i) := Nat.le_add_right _ _
    _ = width x.fragment := splitWidth
    _ = x.code.length := (assemble_length x.assembled).symm

private theorem candidate_zero_next {i cell : Nat} {target : Label}
    (found : x.fragment[i]? = some (.zero cell target)) : x.addr i + 16 = x.addr (i + 1) := by
  have step := candidate_offset_step found
  change x.pc + BitVec.ofNat 64 (16 * x.offset i) + BitVec.ofNat 64 (16 * 1) =
    x.pc + BitVec.ofNat 64 (16 * x.offset (i + 1))
  rw [pc_add, step, Piece.width]

private theorem candidate_label_next {i : Nat} {target : Label}
    (found : x.fragment[i]? = some (.label target)) : x.addr i = x.addr (i + 1) := by
  have step := candidate_offset_step found
  simp only [Piece.width, Nat.add_zero] at step
  simp only [Image.addr, step]

private theorem candidate_position_prefix (target : Label) (before after : List Piece) (pc : Nat) :
    before.all (fun piece => match piece with
      | .label name => decide (name ≠ target)
      | _ => true) = true →
    position target (before ++ after) pc = position target after (pc + width before) := by
  induction before generalizing pc with
  | nil => intro _; simp only [List.nil_append, width, Nat.add_zero]
  | cons piece rest ih =>
    intro absent
    simp only [List.all_cons, Bool.and_eq_true] at absent
    cases piece with
    | code instructions =>
      simpa only [List.cons_append, position, width, Piece.width, Nat.add_assoc] using
        ih (pc + instructions.length) absent.2
    | label name =>
      have different : name ≠ target := of_decide_eq_true absent.1
      simpa only [List.cons_append, position, different, ↓reduceIte, width,
        Piece.width, Nat.add_zero, Nat.zero_add] using ih pc absent.2
    | jump destination =>
      simpa only [List.cons_append, position, width, Piece.width, Nat.add_assoc] using
        ih (pc + 1) absent.2
    | zero cell destination =>
      simpa only [List.cons_append, position, width, Piece.width, Nat.add_assoc] using
        ih (pc + 1) absent.2

private theorem candidate_position_at_label {i : Nat} {target : Label}
    (found : x.fragment[i]? = some (.label target))
    (absent : (x.fragment.take i).all (fun piece => match piece with
      | .label name => decide (name ≠ target)
      | _ => true) = true) :
    position target x.fragment 0 = some (x.offset (i + 1)) := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = .label target := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  have splitImage : x.fragment =
      x.fragment.take i ++ .label target :: x.fragment.drop (i + 1) := by
    have split := List.take_append_drop i x.fragment
    rw [List.drop_eq_getElem_cons inside, element] at split
    exact split.symm
  have located := candidate_position_prefix target (x.fragment.take i)
    (.label target :: x.fragment.drop (i + 1)) 0 absent
  rw [← splitImage] at located
  have atLabel : position target (.label target :: x.fragment.drop (i + 1))
      (0 + width (x.fragment.take i)) = some (width (x.fragment.take i)) := by
    rw [position, ite_eq_left rfl, Nat.zero_add]
  calc
    position target x.fragment 0 = some (width (x.fragment.take i)) := located.trans atLabel
    _ = some (x.offset (i + 1)) := by
      congr 1
      simpa only [Image.offset, Piece.width, Nat.add_zero] using (candidate_offset_step found).symm

private theorem candidate_position : position .candidate x.fragment 0 = some (x.offset 8) := by
  exact candidate_position_at_label (i := 7) rfl rfl

private theorem candidate_next_position : position .candidateNext x.fragment 0 = some (x.offset 31) := by
  exact candidate_position_at_label (i := 30) rfl rfl

private theorem exhausted_position : position .exhausted x.fragment 0 = some (x.offset 34) := by
  exact candidate_position_at_label (i := 33) rfl rfl

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
  have incrementEnd := x.addr_next_code (i := 31)
    (block := [ci 1 (x.s + 4) 1 0, ci 3 x.s x.s (x.s + 4)]) rfl
  change x.addr 31 + 32 = x.addr 32 at incrementEnd
  apply (h.ready.increment (i := 31) (j := 32) (cell := x.s) (n := j)
    (by rw [← q.origin]) (Nat.le_refl _) (by omega) h.candidateRead rfl
    incrementEnd).bind
  intro mem result
  obtain ⟨ready, frame, other, read⟩ := result
  have back := ready.jump 32 8 .candidate rfl candidate_position
    (candidate_offset_bound 32) (candidate_offset_bound 8)
  exact ⟨mem, back, AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, ready, read,
    (other (x.s + 2) (by omega) (by omega)).trans h.liveRead⟩

private theorem candidate_member (k : Wert D (.index (D.count x.table))) (hk : k.n = j)
    (h : q.CandState σ ρ j live m) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 10) (x.addr 11) m
      (fun mem => q.CandState σ ρ j live mem ∧
        x.read mem (x.s + 4) (Runner.IR.bool (q.memberAt σ ρ k))) := by
  have room : x.s + 4 ≤ x.K := by have := x.scratch; have := x.layout.ks; omega
  have index : x.read m x.s (BitVec.ofInt 64 k.n) := by
    rw [hk, BitVec.ofInt_natCast]; exact h.candidateRead
  have valueAt : ValueAt L m x.fp x.s (.index (D.count x.table)) k :=
    ValueAt.of_enc q.indexWidth index rfl
  have memberEnv : EnvAt L m x.fp (.cons k ρ) reserved :=
    envAt_cons h.ready.env (by simpa only [← q.origin] using valueAt)
  have memberReady : x.Ready m σ (.cons k ρ) :=
    { h.ready with env := memberEnv }
  have memberCtx : frei (.index (D.count x.table) :: Γ) reserved ≤ x.s + 4 := by
    simp only [frei_cons, q.indexWidth, ← q.origin]
    omega
  apply (memberReady.eval 10 memberCtx q.memberCode q.memberTop rfl trivial).map
  intro mem result
  obtain ⟨ready, frame, value, read, encoding⟩ := result
  have word : value = Runner.IR.bool (q.memberAt σ ρ k) := by
    simpa only [Enc, memberAt, bool_word] using encoding
  refine ⟨h.agree frame (by omega) room, ?_⟩
  rw [← word]
  exact read

private theorem candidate_absent (h : q.CandState σ ρ j live m)
    (read : x.read m (x.s + 4) (Runner.IR.bool false)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 11) (x.addr 8) m
      (q.CandState σ ρ (j + 1) live) := by
  have branch := h.ready.branch 11 31 (x.s + 4) .candidateNext _ rfl
    candidate_next_position (candidate_offset_bound 11) (candidate_offset_bound 31)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (candidate_zero_next (i := 11) (cell := x.s + 4) (target := .candidateNext) rfl)
  have reject : Star ⟨x.addr 11, x.fp⟩ m ⟨x.addr 31, x.fp⟩ m := by
    simpa only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] using branch
  exact ScanRun.prefix reject (candidate_next h)

private theorem candidate_live (k : Wert D (.index (D.count x.table))) (hk : k.n = j)
    (h : q.CandState σ ρ j live m) (read : x.read m (x.s + 4) (Runner.IR.bool true)) :
    let answer := keinVorgaenger (alleIndizes (D.count x.table))
      (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 11)
      (if answer then x.addr 37 else x.addr 8) m
      (fun mem => if answer then q.CandResult σ ρ (some k) true mem
        else q.CandState σ ρ (j + 1) true mem) := by
  have branch := h.ready.branch 11 31 (x.s + 4) .candidateNext _ rfl
    candidate_next_position (candidate_offset_bound 11) (candidate_offset_bound 31)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (candidate_zero_next (i := 11) (cell := x.s + 4) (target := .candidateNext) rfl)
  have pass : Star ⟨x.addr 11, x.fp⟩ m ⟨x.addr 12, x.fp⟩ m := by
    simpa only [Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] using branch
  apply ScanRun.prefix pass
  have literalsEnd := x.addr_next_code (i := 12)
    (block := [ci 1 (x.s + 2) 1 0, ci 1 (x.s + 1) 0 0]) rfl
  change x.addr 12 + 32 = x.addr 13 at literalsEnd
  apply (h.ready.literals (i := 12) (a := x.s + 2) (b := x.s + 1)
    rfl (by rw [← q.origin]; omega) (by omega)
    (by have := x.scratch; have := x.layout.ks; omega)
    (by have := x.scratch; have := x.layout.ks; omega)
    (by omega) (by decide) (by decide) literalsEnd).bind
  intro mem result
  obtain ⟨ready, frame, flag, predecessorRead⟩ := result
  have candidateRead : x.read mem x.s (BitVec.ofInt 64 k.n) :=
    Image.read_agree frame h.ready.frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
      (by rw [hk, BitVec.ofInt_natCast]; exact h.candidateRead)
  have initial : q.PredState σ ρ k true 0 mem :=
    ⟨⟨ready, candidateRead, flag⟩, predecessorRead⟩
  have scan := q.predecessor_path (σ := σ) (ρ := ρ) k true (D.count x.table).toNat 0 (by omega) mem initial
  rw [← alleIndizes_ab] at scan
  rw [candidate_label_next (i := 13) (target := .predecessor) rfl]
  generalize answerEq : keinVorgaenger (alleIndizes (D.count x.table))
    (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k = answer at scan ⊢
  cases answer with
  | true =>
    simp only [↓reduceIte] at scan ⊢
    exact scan.map (fun _ state => ⟨state.ready,
      (by intro selected eq; cases eq; exact state.candidateRead), state.liveRead⟩)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at scan ⊢
    apply scan.bind
    intro mem' state
    exact candidate_next (q := q) (σ := σ) (ρ := ρ) (j := j) (live := true)
      ⟨state.ready, (by simpa only [Image.read, hk, BitVec.ofInt_natCast] using state.candidateRead),
        state.liveRead⟩

/-- One candidate: evaluate membership, and if live scan all predecessors. -/
theorem candidate_test (k : Wert D (.index (D.count x.table))) (hk : k.n = j)
    (h : q.CandState σ ρ j live m) :
    let minimal := istMinimalVerbrauch (alleIndizes (D.count x.table))
      (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 10)
      (if minimal then x.addr 37 else x.addr 8) m
      (fun m' => if minimal then q.CandResult σ ρ (some k) true m'
        else q.CandState σ ρ (j + 1) (live || q.memberAt σ ρ k) m') := by
  apply (candidate_member k hk h).bind
  intro mem result
  obtain ⟨state, read⟩ := result
  cases membership : q.memberAt σ ρ k with
  | false =>
    change x.read mem (x.s + 4) (Runner.IR.bool (q.memberAt σ ρ k)) at read
    rw [membership] at read
    simp only [istMinimalVerbrauch, membership, Bool.false_and, Bool.false_eq_true,
      Bool.or_false, ↓reduceIte]
    exact candidate_absent state read
  | true =>
    change x.read mem (x.s + 4) (Runner.IR.bool (q.memberAt σ ρ k)) at read
    rw [membership] at read
    simp only [istMinimalVerbrauch, membership, Bool.true_and, Bool.or_true]
    exact candidate_live k hk state read

/-- The scan result is exactly verbrauchWahlAux on the current state. -/
theorem candidate_path : ∀ remaining j, j + remaining = (D.count x.table).toNat →
    ∀ live m, q.CandState σ ρ j live m →
    let choice := verbrauchWahlAux (alleIndizes (D.count x.table))
      (idxAb (D.count x.table) j remaining) (q.memberAt σ ρ) (q.edgeAt σ ρ)
      (fun a b => decide (a.n = b.n))
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 8)
      (if choice.isSome then x.addr 37 else x.addr 34) m
      (q.CandResult σ ρ choice (live || (idxAb (D.count x.table) j remaining).any (q.memberAt σ ρ))) := by
  have boundEnd : x.addr 8 + BitVec.ofNat 64 (16 * (travCountSize (D.count x.table) + 1)) =
      x.addr 9 := by
    simpa only [List.length_append, travCountC_length, List.length_singleton] using
      x.addr_next_code (i := 8)
        (block := travCountC (x.s + 5) (D.count x.table) ++
          [ci 13 (x.s + 4) x.s (x.s + 5)]) rfl
  apply candidate_scan (D.count x.table) (q.memberAt σ ρ) (q.edgeAt σ ρ)
    (x.addr 8) (x.addr 37) (x.addr 34) (q.CandState σ ρ) (q.CandResult σ ρ)
  · intro live mem h
    apply (h.ready.bound (i := 8) (index := x.s) (j := (D.count x.table).toNat)
      (by rw [← q.origin]; omega) (by omega)
      (by have := x.bounds.2.2.1; simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.candidateRead rfl boundEnd).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have notLess : decide (((D.count x.table).toNat : Int) < D.count x.table) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [notLess] at read
    have exit := ready.branch 9 34 (x.s + 4) .exhausted _ rfl
      exhausted_position (candidate_offset_bound 9) (candidate_offset_bound 34)
      (by have := x.scratch; have := x.layout.ks; omega) read
      (candidate_zero_next (i := 9) (cell := x.s + 4) (target := .exhausted) rfl)
    refine ⟨mem', by simpa [Runner.IR.bool] using exit,
      AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, ?_⟩
    exact
      { ready := ready
        candidateRead := by
          intro _ impossible
          cases impossible
        liveRead := state.liveRead }
  · intro j k hk live mem h
    have iteration :
        let minimal := istMinimalVerbrauch (alleIndizes (D.count x.table))
          (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k
        ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 8)
          (if minimal then x.addr 37 else x.addr 8) mem
          (fun m' => if minimal then q.CandResult σ ρ (some k) true m'
            else q.CandState σ ρ (j + 1) (live || q.memberAt σ ρ k) m') := by
      apply (h.ready.bound (i := 8) (index := x.s) (j := j)
      (by rw [← q.origin]; omega) (by omega)
      (by have := k.le_hi; have := k.lo_le; have := x.bounds.2.2.1;
          simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.candidateRead rfl boundEnd).bind
      intro mem' result
      obtain ⟨ready, frame, read⟩ := result
      have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
      have less : decide ((j : Int) < D.count x.table) = true := by
        have := k.le_hi
        simp only [decide_eq_true_eq]
        omega
      rw [less] at read
      have pass := ready.branch 9 34 (x.s + 4) .exhausted _ rfl
        exhausted_position (candidate_offset_bound 9) (candidate_offset_bound 34)
        (by have := x.scratch; have := x.layout.ks; omega) read
        (candidate_zero_next (i := 9) (cell := x.s + 4) (target := .exhausted) rfl)
      have test := candidate_test k hk state
      exact ScanRun.prefix (by simpa [Runner.IR.bool] using pass) test
    cases minimal : istMinimalVerbrauch (alleIndizes (D.count x.table))
        (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) k <;>
      simp only [minimal, Bool.false_eq_true, ↓reduceIte] at iteration ⊢ <;>
      obtain ⟨result, steps, frame, kept, state⟩ := iteration <;>
      exact ⟨result, steps, frame, kept, state⟩

/-- Initialize both selector words, scan the entire index domain and retain
    the canonical empty/cyclic distinction in the live flag. -/
theorem selection (h : x.Ready m σ ρ) :
    let choice := verbrauchWahl (alleIndizes (D.count x.table))
      (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n))
    let live := !((alleIndizes (D.count x.table)).all fun k => !(q.memberAt σ ρ k))
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 6)
      (if choice.isSome then x.addr 37 else x.addr 34) m (q.CandResult σ ρ choice live) := by
  have literalsEnd := x.addr_next_code (i := 6)
    (block := [ci 1 x.s 0 0, ci 1 (x.s + 2) 0 0]) rfl
  change x.addr 6 + 32 = x.addr 7 at literalsEnd
  apply (h.literals (i := 6) (a := x.s) (b := x.s + 2) rfl
    (by rw [← q.origin]; omega) (by omega)
    (by have := x.scratch; have := x.layout.ks; omega)
    (by have := x.scratch; have := x.layout.ks; omega)
    (by omega) (by decide) (by decide) literalsEnd).bind
  intro mem result
  obtain ⟨ready, frame, zero, flag⟩ := result
  have scan := q.candidate_path (σ := σ) (ρ := ρ) (D.count x.table).toNat 0 (by omega) false mem ⟨ready, zero, flag⟩
  rw [← alleIndizes_ab] at scan
  erw [Bool.false_or, List.any_eq_not_all_not] at scan
  simp only [verbrauchWahl, candidate_label_next (i := 7) (target := .candidate) rfl]
  exact scan

end Gabbro.Stage0.Senke.Consuming.Selector
