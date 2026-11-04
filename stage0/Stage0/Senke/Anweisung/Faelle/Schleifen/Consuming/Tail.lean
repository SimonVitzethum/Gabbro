/- Measure/body boundaries and the two post-body continuations. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Head
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming.Loop
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {reserved : Nat} {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)}
variable (q : Loop x Γ Λ) {n : Nat} {m : Mem} {σ : World D} {ρ : Env D Γ}

private theorem tail_width_append (a b : List Piece) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp only [List.nil_append, width, Nat.zero_add]
  | cons a rest ih => simp only [List.cons_append, width, ih, Nat.add_assoc]

private theorem tail_offset_step {i : Nat} {piece : Piece}
    (found : x.fragment[i]? = some piece) : x.offset (i + 1) = x.offset i + piece.width := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = piece := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  simp only [Image.offset, List.take_succ_eq_append_getElem inside, element,
    tail_width_append, width, Nat.add_zero]

private theorem tail_offset_bound (i : Nat) : x.offset i ≤ x.code.length := by
  have splitWidth := congrArg width (List.take_append_drop i x.fragment)
  rw [tail_width_append] at splitWidth
  calc
    x.offset i ≤ x.offset i + width (x.fragment.drop i) := Nat.le_add_right _ _
    _ = width x.fragment := splitWidth
    _ = x.code.length := (assemble_length x.assembled).symm

private theorem tail_zero_next {i cell : Nat} {target : Label}
    (found : x.fragment[i]? = some (.zero cell target)) : x.addr i + 16 = x.addr (i + 1) := by
  have step := tail_offset_step found
  change x.pc + BitVec.ofNat 64 (16 * x.offset i) + BitVec.ofNat 64 (16 * 1) =
    x.pc + BitVec.ofNat 64 (16 * x.offset (i + 1))
  rw [pc_add, step, Piece.width]

private theorem tail_position_prefix (target : Label) (before after : List Piece) (pc : Nat) :
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

private theorem tail_position_at_label {i : Nat} {target : Label}
    (found : x.fragment[i]? = some (.label target))
    (absent : (x.fragment.take i).all (fun piece => match piece with
      | .label name => decide (name ≠ target)
      | _ => true) = true) : position target x.fragment 0 = some (x.offset i) := by
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
  have located := tail_position_prefix target (x.fragment.take i)
    (.label target :: x.fragment.drop (i + 1)) 0 absent
  rw [← splitImage] at located
  have atLabel : position target (.label target :: x.fragment.drop (i + 1))
      (0 + width (x.fragment.take i)) = some (width (x.fragment.take i)) := by
    rw [position, ite_eq_left rfl, Nat.zero_add]
  exact located.trans atLabel

private theorem tail_stop_position : position .stop x.fragment 0 = some (x.offset 49) := by
  have step := tail_offset_step (i := 48) (piece := .label .stop) rfl
  simp only [Piece.width, Nat.add_zero] at step
  exact (tail_position_at_label (i := 48) rfl rfl).trans (congrArg some step.symm)

private theorem tail_done_position : position .done x.fragment 0 = some (x.offset 50) := by
  exact tail_position_at_label (i := 50) rfl rfl

private theorem measured_read {τ : World D} (h : x.Ready m τ ρ) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 37) (x.addr 38) m
      (fun mem => x.Ready mem τ ρ ∧ Agree x.fp (x.s + 4) x.K m mem ∧
        x.read mem (x.s + 4) (BitVec.ofInt 64 (Gabbro.Grammatik.eval τ q.mass τ ρ).n)) := by
  apply (h.eval 37 (by rw [← q.selector.origin]; omega) q.massCode q.massTop rfl trivial).map
  intro mem result
  obtain ⟨ready, frame, value, read, encoding⟩ := result
  have word : value = BitVec.ofInt 64 (Gabbro.Grammatik.eval τ q.mass τ ρ).n := encoding
  refine ⟨ready, frame, ?_⟩
  rw [← word]
  exact read

private theorem before_body_at {τ : World D} (k : Wert D (.index (D.count x.table)))
    {live : Bool} (h : q.selector.CandResult τ ρ (some k) live m)
    (fuelRead : x.read m x.counter (BitVec.ofNat 64 n)) :
    ∃ mem, Star ⟨x.addr 37, x.fp⟩ m ⟨x.addr 39, x.fp⟩ mem ∧
      AgreeW L x.fp x.lo x.K m mem ∧ Keeps x.fp x.pr m mem ∧
      x.Ready mem τ (.cons k ρ) ∧ x.read mem x.counter (BitVec.ofNat 64 n) ∧
      x.read mem x.saved (BitVec.ofInt 64 (Gabbro.Grammatik.eval τ q.mass τ ρ).n) := by
  obtain ⟨m1, measureRun, measureFrame, measureKept, ready1, localFrame, read⟩ :=
    measured_read (q := q) h.ready
  have counterRead := (measureKept x.counter (by simp)).trans fuelRead
  have candidateRead := Image.read_agree localFrame h.ready.frame (by omega)
    (by have := x.scratch; have := x.layout.ks; omega) (h.candidateRead k rfl)
  have saveEnd := x.addr_next_code (i := 38) (block := [ci 2 x.saved (x.s + 4) 0]) rfl
  change x.addr 38 + 16 = x.addr 39 at saveEnd
  obtain ⟨m2, saveRun, saveFrame, ready2, saveKept, savedRead, others⟩ :=
    ready1.save (i := 38) (cell := x.saved) (source := x.s + 4) rfl
      (by have := x.scratch; have := x.layout.ks; omega) read
      (by have := x.controls; omega) x.controls.2.2 rfl
      (by rw [← q.selector.origin]; have := x.scratch; have := x.layout.ks; omega) saveEnd
  have binderRead : x.read m2 x.s (BitVec.ofInt 64 k.n) :=
    (others x.s (by have := x.scratch; have := x.layout.ks; omega)
      (by have := x.controls; have := x.scratch; omega)).trans candidateRead
  have binderValue : ValueAt L m2 x.fp x.s (.index (D.count x.table)) k :=
    ValueAt.of_enc q.selector.indexWidth binderRead rfl
  have binderEnv : EnvAt L m2 x.fp (.cons k ρ) reserved :=
    envAt_cons ready2.env (by simpa only [← q.selector.origin] using binderValue)
  exact ⟨m2, measureRun.trans saveRun, measureFrame.trans saveFrame,
    (fun j hj => (saveKept j (by simp [hj])).trans (measureKept j (by simp [hj]))),
    { ready2 with env := binderEnv }, (saveKept x.counter (by simp)).trans counterRead, savedRead⟩

/-- Save the measured pre-body value, then install the selected body binder. -/
theorem before_body (k : Wert D (.index (D.count x.table)))
    {live : Bool} (h : q.selector.CandResult σ ρ (some k) live m)
    (fuelRead : x.read m x.counter (BitVec.ofNat 64 n)) :
    let measured := q.massW σ ρ
    ∃ m', Star ⟨x.addr 37, x.fp⟩ m ⟨x.addr 39, x.fp⟩ m' ∧
      AgreeW L x.fp x.lo x.K m m' ∧ Keeps x.fp x.pr m m' ∧
      x.Ready m' measured.1 (.cons k ρ) ∧
      x.read m' x.counter (BitVec.ofNat 64 n) ∧
      x.read m' x.saved (BitVec.ofInt 64 measured.2) := by
  let τ := σ.lese Λ q.mass.orte
  have current : q.selector.CandResult τ ρ (some k) live m :=
    { h with ready := h.ready.lese }
  have made := before_body_at (q := q) k current fuelRead
  dsimp only [massW]
  exact made

/-- The typed measure supplies both range conjuncts of verbrauchLauf. -/
theorem measure_bounds (σ : World D) (ρ : Env D Γ) :
    0 ≤ (q.massW σ ρ).2 ∧ (q.massW σ ρ).2 ≤ x.bound :=
  ⟨(eval (q.massW σ ρ).1 q.mass (q.massW σ ρ).1 ρ).lo_le,
    (eval (q.massW σ ρ).1 q.mass (q.massW σ ρ).1 ρ).le_hi⟩

private theorem after_body_dispatch {τ : World D} (i : Nat) (old new : Int)
    (found : x.fragment[i]? = some (.code (decrease (x.s + 4) x.saved
      (logikCode (D := D) .schleife) x.bound x.measure)))
    (h : x.Ready m τ ρ) (fuelRead : x.read m x.counter (BitVec.ofNat 64 n))
    (bounds : 0 ≤ new ∧ new ≤ x.bound)
    (checked : if new < old then
      Ok m (x.addr i) x.fp x.K (x.s + 4)
        (decrease (x.s + 4) x.saved (logikCode (D := D) .schleife) x.bound x.measure) (· = 1)
      else Stops ⟨x.addr i, x.fp⟩ m (logikCode (D := D) .schleife)) :
    if 0 ≤ new ∧ new ≤ x.bound ∧ new < old then
      ScanRun L x.fp x.lo x.K x.pr (x.addr i) (x.addr (i + 1)) m
        (fun mem => x.Ready mem τ ρ ∧ x.read mem x.counter (BitVec.ofNat 64 n))
    else Stops ⟨x.addr i, x.fp⟩ m (logikCode (D := D) .schleife) := by
  by_cases falls : new < old
  · simp only [bounds.1, bounds.2, falls, and_self, ↓reduceIte] at checked ⊢
    obtain ⟨mem, run, frame, kept, ready, localFrame, value, read, encoding⟩ :=
      h.ok checked (x.addr_next_code found) (by rw [← q.selector.origin]; omega) (by omega)
        (by have := x.scratch; have := x.layout.ks; omega)
    exact ⟨mem, run, frame, (fun j hj => kept j (by simp [hj])), ready,
      (kept x.counter (by simp)).trans fuelRead⟩
  · simp only [falls, and_false, ↓reduceIte] at checked ⊢
    exact checked

/-- Execute either copy of the complete post-body measure check. -/
theorem after_body (i : Nat) (which : i = 41 ∨ i = 44) (old : Int)
    (oldBound : -2 ^ 63 ≤ old ∧ old < 2 ^ 63)
    (h : x.Ready m σ ρ) (fuelRead : x.read m x.counter (BitVec.ofNat 64 n))
    (savedRead : x.read m x.saved (BitVec.ofInt 64 old)) :
    let measured := q.massW σ ρ
    if 0 ≤ measured.2 ∧ measured.2 ≤ x.bound ∧ measured.2 < old then
      ScanRun L x.fp x.lo x.K x.pr (x.addr i) (x.addr (i + 1)) m
        (fun m' => x.Ready m' measured.1 ρ ∧ x.read m' x.counter (BitVec.ofNat 64 n))
    else Stops ⟨x.addr i, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have found : x.fragment[i]? = some (.code (decrease (x.s + 4) x.saved
      (logikCode (D := D) .schleife) x.bound x.measure)) := by
    rcases which with rfl | rfl <;> rfl
  have pre := h.pre i (x.s + 4) _ (by rw [← q.selector.origin]; omega) found
  have checked := decrease_ok q.massCode q.massTop (by have := x.scratch; omega) x.layout
    pre h.world (by have := x.controls; have := x.scratch; omega) x.bounds.2.1
    x.bounds.2.2.2 oldBound savedRead
  let τ := σ.lese Λ q.mass.orte
  let new := (Gabbro.Grammatik.eval τ q.mass τ ρ).n
  have current : x.Ready m τ ρ := h.lese
  have bounds : 0 ≤ new ∧ new ≤ x.bound :=
    ⟨(Gabbro.Grammatik.eval τ q.mass τ ρ).lo_le, (Gabbro.Grammatik.eval τ q.mass τ ρ).le_hi⟩
  have completed := after_body_dispatch (q := q) i old new found current fuelRead bounds checked
  dsimp only [massW]
  exact completed

private theorem leave_read {τ : World D} (h : x.Ready m τ ρ) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 45) (x.addr 46) m
      (fun mem => x.Ready mem τ ρ ∧
        x.read mem (x.s + 4) (Runner.IR.bool (wahr? (Gabbro.Grammatik.eval τ q.inv τ ρ)))) := by
  apply (h.eval 45 (by rw [← q.selector.origin]; omega) q.invCode q.invTop rfl trivial).map
  intro mem result
  obtain ⟨ready, frame, value, read, encoding⟩ := result
  have word : value = Runner.IR.bool (wahr? (Gabbro.Grammatik.eval τ q.inv τ ρ)) := by
    simpa only [Enc, bool_word] using encoding
  refine ⟨ready, ?_⟩
  rw [← word]
  exact read

private theorem leave_dispatch {τ : World D} {b : Bool} {mem : Mem}
    (prefixRun : Star ⟨x.addr 45, x.fp⟩ m ⟨x.addr 46, x.fp⟩ mem)
    (frame : AgreeW L x.fp x.lo x.K m mem) (kept : Keeps x.fp x.pr m mem)
    (ready : x.Ready mem τ ρ) (read : x.read mem (x.s + 4) (Runner.IR.bool b)) :
    if b = true then Reach L x.fp x.lo x.K x.pr ⟨x.addr 45, x.fp⟩ m (x.addr 50) τ ρ reserved
    else Stops ⟨x.addr 45, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have branch := ready.branch 46 49 (x.s + 4) .stop _ rfl tail_stop_position
    (tail_offset_bound 46) (tail_offset_bound 49)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (tail_zero_next (i := 46) (cell := x.s + 4) (target := .stop) rfl)
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have stopRun : Star ⟨x.addr 46, x.fp⟩ mem ⟨x.addr 49, x.fp⟩ mem := by
      simpa only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] using branch
    exact Stops.prefix (prefixRun.trans stopRun) ready.stop
  | true =>
    simp only [↓reduceIte]
    have passRun : Star ⟨x.addr 46, x.fp⟩ mem ⟨x.addr 47, x.fp⟩ mem := by
      simpa only [Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] using branch
    have exit := ready.jump 47 50 .done rfl tail_done_position
      (tail_offset_bound 47) (tail_offset_bound 50)
    exact ⟨mem, prefixRun.trans (passRun.trans exit), frame, ready.env, ready.world, kept⟩

/-- The leave continuation checks its invariant after the falling measure. -/
theorem leave_invariant (h : x.Ready m σ ρ) :
    if (q.invW σ ρ).2 = true then
      Reach L x.fp x.lo x.K x.pr ⟨x.addr 45, x.fp⟩ m (x.addr 50) (q.invW σ ρ).1 ρ reserved
    else Stops ⟨x.addr 45, x.fp⟩ m (logikCode (D := D) .schleife) := by
  let τ := σ.lese Λ q.inv.orte
  have current : x.Ready m τ ρ := h.lese
  obtain ⟨mem, run, frame, kept, ready, read⟩ := leave_read (q := q) current
  have completed := leave_dispatch (q := q) (τ := τ)
    (b := wahr? (Gabbro.Grammatik.eval τ q.inv τ ρ)) run frame
    (fun j hj => kept j (by simp [hj])) ready read
  dsimp only [invW]
  exact completed

end Gabbro.Stage0.Senke.Consuming.Loop
