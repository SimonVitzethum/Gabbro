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
  mt : Nat
  et : Nat
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
  wahr? (Gabbro.Grammatik.eval σ q.member σ (.cons k ρ))
def edgeAt (a b : Wert D (.index (D.count x.table))) : Bool :=
  wahr? (Gabbro.Grammatik.eval σ q.edge σ (.cons a (.cons b ρ)))

private theorem width_append (a b : List Piece) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp only [List.nil_append, width, Nat.zero_add]
  | cons a rest ih => simp only [List.cons_append, width, ih, Nat.add_assoc]

private theorem offset_step {i : Nat} {piece : Piece}
    (found : x.fragment[i]? = some piece) : x.offset (i + 1) = x.offset i + piece.width := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = piece := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  simp only [Image.offset, List.take_succ_eq_append_getElem inside, element,
    width_append, width, Nat.add_zero]

private theorem offset_bound (i : Nat) : x.offset i ≤ x.code.length := by
  have splitWidth := congrArg width (List.take_append_drop i x.fragment)
  rw [width_append] at splitWidth
  calc
    x.offset i ≤ x.offset i + width (x.fragment.drop i) := Nat.le_add_right _ _
    _ = width x.fragment := splitWidth
    _ = x.code.length := (assemble_length x.assembled).symm

private theorem zero_next {i cell : Nat} {target : Label}
    (found : x.fragment[i]? = some (.zero cell target)) : x.addr i + 16 = x.addr (i + 1) := by
  have step := offset_step found
  change x.pc + BitVec.ofNat 64 (16 * x.offset i) + BitVec.ofNat 64 (16 * 1) =
    x.pc + BitVec.ofNat 64 (16 * x.offset (i + 1))
  rw [pc_add, step, Piece.width]

private theorem position_prefix (target : Label) (before after : List Piece) (pc : Nat) :
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

private theorem position_at_label {i : Nat} {target : Label}
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
  have located := position_prefix target (x.fragment.take i)
    (.label target :: x.fragment.drop (i + 1)) 0 absent
  rw [← splitImage] at located
  have atLabel : position target (.label target :: x.fragment.drop (i + 1))
      (0 + width (x.fragment.take i)) = some (width (x.fragment.take i)) := by
    rw [position, if_pos rfl, Nat.zero_add]
  calc
    position target x.fragment 0 = some (width (x.fragment.take i)) := located.trans atLabel
    _ = some (x.offset (i + 1)) := by
      congr 1
      simpa only [Image.offset, Piece.width, Nat.add_zero] using (offset_step found).symm

private theorem predecessor_position : position .predecessor x.fragment 0 = some (x.offset 14) := by
  exact position_at_label (i := 13) rfl rfl

private theorem different_position : position .different x.fragment 0 = some (x.offset 20) := by
  exact position_at_label (i := 19) rfl rfl

private theorem predecessorNext_position :
    position .predecessorNext x.fragment 0 = some (x.offset 28) := by
  exact position_at_label (i := 27) rfl rfl

private theorem candidateNext_position : position .candidateNext x.fragment 0 = some (x.offset 31) := by
  exact position_at_label (i := 30) rfl rfl

private theorem selected_position : position .selected x.fragment 0 = some (x.offset 37) := by
  exact position_at_label (i := 36) rfl rfl

structure PredDone (q : Selector x Γ Λ) (σ : World D) (ρ : Env D Γ) (candidate : Wert D (.index (D.count x.table))) (live : Bool) (m : Mem) : Prop where
  ready : x.Ready m σ ρ
  candidateRead : x.read m x.s (BitVec.ofInt 64 candidate.n)
  liveRead : x.read m (x.s + 2) (Runner.IR.bool live)

structure PredState (q : Selector x Γ Λ) (σ : World D) (ρ : Env D Γ) (candidate : Wert D (.index (D.count x.table))) (live : Bool)
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
  have incrementEnd := x.addr_next_code (i := 28)
    (block := [ci 1 (x.s + 4) 1 0, ci 3 (x.s + 1) (x.s + 1) (x.s + 4)]) rfl
  change x.addr 28 + 32 = x.addr 29 at incrementEnd
  apply (h.ready.increment (i := 28) (j := 29) (cell := x.s + 1) (n := j)
    (by rw [← q.origin]; omega) (by omega) (by omega) h.predecessorRead rfl
    incrementEnd).bind
  intro m' state
  obtain ⟨ready, frame, others, read⟩ := state
  have back := ready.jump 29 14 .predecessor rfl predecessor_position
    (offset_bound 29) (offset_bound 14)
  exact ⟨m', back, AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _,
    ⟨⟨ready, (others x.s (by omega) (by omega)).trans h.candidateRead,
      (others (x.s + 2) (by omega) (by omega)).trans h.liveRead⟩, read⟩⟩

private theorem predecessor_edge_false (h : q.PredState σ ρ candidate live j m)
    (read : x.read m (x.s + 4) (Runner.IR.bool false)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 25) (x.addr 14) m
      (q.PredState σ ρ candidate live (j + 1)) := by
  have branch := h.ready.branch 25 28 (x.s + 4) .predecessorNext _ rfl
    predecessorNext_position (offset_bound 25) (offset_bound 28)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (zero_next (i := 25) (cell := x.s + 4) (target := .predecessorNext) rfl)
  have advance : Star ⟨x.addr 25, x.fp⟩ m ⟨x.addr 28, x.fp⟩ m := by
    simpa only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] using branch
  exact ScanRun.prefix (start := x.addr 25) (middle := x.addr 28) (finish := x.addr 14)
    advance (predecessor_next h)

private theorem predecessor_edge_true (h : q.PredState σ ρ candidate live j m)
    (read : x.read m (x.s + 4) (Runner.IR.bool true)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 25) (x.addr 31) m
      (q.PredDone σ ρ candidate live) := by
  have branch := h.ready.branch 25 28 (x.s + 4) .predecessorNext _ rfl
    predecessorNext_position (offset_bound 25) (offset_bound 28)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (zero_next (i := 25) (cell := x.s + 4) (target := .predecessorNext) rfl)
  have advance : Star ⟨x.addr 25, x.fp⟩ m ⟨x.addr 26, x.fp⟩ m := by
    simpa only [Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] using branch
  have reject := h.ready.jump 26 31 .candidateNext rfl candidateNext_position
    (offset_bound 26) (offset_bound 31)
  exact ⟨m, advance.trans reject, AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, h.toPredDone⟩

private theorem predecessor_edge (a : Wert D (.index (D.count x.table))) (ha : a.n = j)
    (h : q.PredState σ ρ candidate live j m) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 24)
      (if q.edgeAt σ ρ a candidate then x.addr 31 else x.addr 14) m
      (fun m' => if q.edgeAt σ ρ a candidate then q.PredDone σ ρ candidate live m'
        else q.PredState σ ρ candidate live (j + 1) m') := by
  have room : x.s + 4 ≤ x.K := by have := x.scratch; have := x.layout.ks; omega
  have predRead : x.read m (x.s + 1) (BitVec.ofInt 64 a.n) := by
    rw [ha, BitVec.ofInt_natCast]
    exact h.predecessorRead
  have candidateValue : ValueAt L m x.fp x.s (.index (D.count x.table)) candidate :=
    ValueAt.of_enc q.indexWidth h.candidateRead rfl
  have predecessorValue : ValueAt L m x.fp (x.s + 1) (.index (D.count x.table)) a :=
    ValueAt.of_enc q.indexWidth predRead rfl
  have candidateEnv : EnvAt L m x.fp (.cons candidate ρ) reserved :=
    envAt_cons h.ready.env (by simpa only [← q.origin] using candidateValue)
  have edgeEnv : EnvAt L m x.fp (.cons a (.cons candidate ρ)) reserved :=
    envAt_cons candidateEnv
      (by simpa only [frei_cons, q.indexWidth, ← q.origin] using predecessorValue)
  have edgeReady : x.Ready m σ (.cons a (.cons candidate ρ)) :=
    { h.ready with env := edgeEnv }
  have edgeCtx : frei (.index (D.count x.table) :: .index (D.count x.table) :: Γ) reserved ≤
      x.s + 4 := by
    simp only [frei_cons, q.indexWidth, ← q.origin]
    omega
  apply (edgeReady.eval 24 edgeCtx q.edgeCode q.edgeTop rfl trivial).bind
  intro mem result
  obtain ⟨ready, frame, value, read, encoding⟩ := result
  have state : q.PredState σ ρ candidate live j mem := h.agree frame (by omega) room
  have word : value = Runner.IR.bool (q.edgeAt σ ρ a candidate) := by
    simpa only [Enc, edgeAt, bool_word] using encoding
  subst value
  cases edgeValue : q.edgeAt σ ρ a candidate with
  | false =>
    change x.read mem (x.s + 4) (Runner.IR.bool (q.edgeAt σ ρ a candidate)) at read
    rw [edgeValue] at read
    change ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr)
      (x.addr 25) (x.addr 14) mem (q.PredState σ ρ candidate live (j + 1))
    exact predecessor_edge_false state read
  | true =>
    change x.read mem (x.s + 4) (Runner.IR.bool (q.edgeAt σ ρ a candidate)) at read
    rw [edgeValue] at read
    change ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr)
      (x.addr 25) (x.addr 31) mem (q.PredDone σ ρ candidate live)
    exact predecessor_edge_true state read

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
    different_position (offset_bound 17) (offset_bound 20)
    (by have := x.scratch; have := x.layout.ks; omega) sameRead
    (zero_next (i := 17) (cell := x.s + 4) (target := .different) rfl)
  by_cases self : a.n = candidate.n
  · simp only [self, decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    simp only [self, decide_true, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch1
    have skip := ready1.jump 18 28 .predecessorNext rfl predecessorNext_position
      (offset_bound 18) (offset_bound 28)
    exact ScanRun.prefix (branch1.trans skip) (predecessor_next state1)
  · simp only [self, decide_false, Bool.not_false, Bool.and_true]
    simp only [self, decide_false, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] at branch1
    apply ScanRun.prefix branch1
    apply (ready1.borrow (candidate := candidate) (predecessor := a) (member := q.member)
      q.origin q.indexWidth q.memberCode q.memberTop
      state1.candidateRead (by rw [ha, BitVec.ofInt_natCast]; exact state1.predecessorRead)).bind
    intro m2 result
    obtain ⟨ready2, frame2, memberRead⟩ := result
    have state2 := state1.agree frame2 (by omega) (by omega)
    have branch2 := ready2.branch 23 28 (x.s + 4) .predecessorNext _ rfl
      predecessorNext_position (offset_bound 23) (offset_bound 28)
      (by have := x.scratch; have := x.layout.ks; omega) memberRead
      (zero_next (i := 23) (cell := x.s + 4) (target := .predecessorNext) rfl)
    cases membership : q.memberAt σ ρ a with
    | false =>
      simp only [memberAt] at membership
      simp only [membership, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] at branch2
      simp only [memberAt, membership, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ScanRun.prefix branch2 (predecessor_next state2)
    | true =>
      have memberTrue : wahr? (Gabbro.Grammatik.eval σ q.member σ (.cons a ρ)) = true := membership
      simp only [memberTrue, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] at branch2
      apply ScanRun.prefix branch2
      exact predecessor_edge a ha state2

/-- Instantiate the existing suffix induction with actual bound and scan edges. -/
theorem predecessor_path (candidate : Wert D (.index (D.count x.table))) (live : Bool) :
    ∀ remaining j, j + remaining = (D.count x.table).toNat → ∀ m,
      q.PredState σ ρ candidate live j m →
      let answer := keinVorgaenger (idxAb (D.count x.table) j remaining)
        (q.memberAt σ ρ) (q.edgeAt σ ρ) (fun a b => decide (a.n = b.n)) candidate
      ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 14)
        (if answer then x.addr 37 else x.addr 31) m (q.PredDone σ ρ candidate live) := by
  have boundEnd : x.addr 14 +
      BitVec.ofNat 64 (16 * (travCountSize (D.count x.table) + 1)) = x.addr 15 := by
    simpa only [List.length_append, travCountC_length, List.length_singleton] using
      x.addr_next_code (i := 14)
        (block := travCountC (x.s + 5) (D.count x.table) ++
          [ci 13 (x.s + 4) (x.s + 1) (x.s + 5)]) rfl
  apply predecessor_scan (D.count x.table) candidate (q.memberAt σ ρ) (q.edgeAt σ ρ)
    (x.addr 14) (x.addr 37) (x.addr 31) (q.PredState σ ρ candidate live)
    (fun _ => q.PredDone σ ρ candidate live)
  · intro mem h
    apply (h.ready.bound (i := 14) (index := x.s + 1) (j := (D.count x.table).toNat)
      (by rw [← q.origin]; omega) (by omega)
      (by have := x.bounds.2.2.1; simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.predecessorRead rfl boundEnd).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have notLess : decide (((D.count x.table).toNat : Int) < D.count x.table) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [notLess] at read
    have exit := ready.branch 15 37 (x.s + 4) .selected _ rfl selected_position
      (offset_bound 15) (offset_bound 37) (by have := x.scratch; have := x.layout.ks; omega)
      read (zero_next (i := 15) (cell := x.s + 4) (target := .selected) rfl)
    exact ⟨mem', by simpa [Runner.IR.bool] using exit,
      AgreeW.refl _ _ _ _ _, Keeps.refl _ _ _, state.toPredDone⟩
  · intro j a ha hit mem h
    apply (h.ready.bound (i := 14) (index := x.s + 1) (j := j)
      (by rw [← q.origin]; omega) (by omega)
      (by have := a.le_hi; have := a.lo_le; have := x.bounds.2.2.1;
          simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.predecessorRead rfl boundEnd).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have less : decide ((j : Int) < D.count x.table) = true := by
      have := a.le_hi
      simp only [decide_eq_true_eq]
      omega
    rw [less] at read
    have pass := ready.branch 15 37 (x.s + 4) .selected _ rfl selected_position
      (offset_bound 15) (offset_bound 37) (by have := x.scratch; have := x.layout.ks; omega)
      read (zero_next (i := 15) (cell := x.s + 4) (target := .selected) rfl)
    apply ScanRun.prefix (by simpa [Runner.IR.bool] using pass)
    simpa only [hit, ↓reduceIte] using predecessor_test a ha state
  · intro j a ha miss mem h
    apply (h.ready.bound (i := 14) (index := x.s + 1) (j := j)
      (by rw [← q.origin]; omega) (by omega)
      (by have := a.le_hi; have := a.lo_le; have := x.bounds.2.2.1;
          simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at this; omega)
      h.predecessorRead rfl boundEnd).bind
    intro mem' result
    obtain ⟨ready, frame, read⟩ := result
    have state := h.agree frame (by omega) (by have := x.scratch; have := x.layout.ks; omega)
    have less : decide ((j : Int) < D.count x.table) = true := by
      have := a.le_hi
      simp only [decide_eq_true_eq]
      omega
    rw [less] at read
    have pass := ready.branch 15 37 (x.s + 4) .selected _ rfl selected_position
      (offset_bound 15) (offset_bound 37) (by have := x.scratch; have := x.layout.ks; omega)
      read (zero_next (i := 15) (cell := x.s + 4) (target := .selected) rfl)
    apply ScanRun.prefix (by simpa [Runner.IR.bool] using pass)
    simpa only [miss, Bool.false_eq_true, ↓reduceIte] using predecessor_test a ha state

end Selector
end Gabbro.Stage0.Senke.Consuming
