/- Full consuming-loop composition on the canonical semantic fuel. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Tail
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Runtime
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming.Loop
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {reserved : Nat} {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)}
variable (q : Loop x Γ Λ)
variable {sc : List D.Lock}

private theorem execution_width_append (a b : List Piece) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp only [List.nil_append, width, Nat.zero_add]
  | cons a rest ih => simp only [List.cons_append, width, ih, Nat.add_assoc]

private theorem execution_offset_step {i : Nat} {piece : Piece}
    (found : x.fragment[i]? = some piece) : x.offset (i + 1) = x.offset i + piece.width := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = piece := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  simp only [Image.offset, List.take_succ_eq_append_getElem inside, element,
    execution_width_append, width, Nat.add_zero]

private theorem execution_offset_bound (i : Nat) : x.offset i ≤ x.code.length := by
  have splitWidth := congrArg width (List.take_append_drop i x.fragment)
  rw [execution_width_append] at splitWidth
  calc
    x.offset i ≤ x.offset i + width (x.fragment.drop i) := Nat.le_add_right _ _
    _ = width x.fragment := splitWidth
    _ = x.code.length := (assemble_length x.assembled).symm

private theorem execution_zero_next {i cell : Nat} {target : Label}
    (found : x.fragment[i]? = some (.zero cell target)) : x.addr i + 16 = x.addr (i + 1) := by
  have step := execution_offset_step found
  change x.pc + BitVec.ofNat 64 (16 * x.offset i) + BitVec.ofNat 64 (16 * 1) =
    x.pc + BitVec.ofNat 64 (16 * x.offset (i + 1))
  rw [pc_add, step, Piece.width]

private theorem execution_position_prefix (target : Label) (before after : List Piece) (pc : Nat) :
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

private theorem execution_position_at_label {i : Nat} {target : Label}
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
  have located := execution_position_prefix target (x.fragment.take i)
    (.label target :: x.fragment.drop (i + 1)) 0 absent
  rw [← splitImage] at located
  have atLabel : position target (.label target :: x.fragment.drop (i + 1))
      (0 + width (x.fragment.take i)) = some (width (x.fragment.take i)) := by
    rw [position, ite_eq_left rfl, Nat.zero_add]
  exact located.trans atLabel

omit [Kern] in
/-- Locate the header while keeping the initializer and its width abstract. -/
private theorem execution_header_of_shape (fragment : List Piece) (first : List II)
    (rest : List Piece) (shape : fragment = .code first :: .label .header :: rest) :
    position .header fragment 0 = some (width (fragment.take 2)) := by
  subst fragment
  simp only [position, List.take_succ_cons,
    List.take_zero, width, Piece.width, ↓reduceIte, Nat.add_zero, Nat.zero_add]

private theorem execution_header_position : position .header x.fragment 0 = some (x.offset 2) :=
  execution_header_of_shape x.fragment (travCountC x.counter (x.fuel : Int))
    (x.fragment.drop 2) rfl

private theorem execution_stop_position : position .stop x.fragment 0 = some (x.offset 49) := by
  have step := execution_offset_step (x := x) (i := 48) (piece := .label .stop) rfl
  simp only [Piece.width, Nat.add_zero] at step
  exact (execution_position_at_label (i := 48) rfl rfl).trans (congrArg some step.symm)

private theorem execution_done_position : position .done x.fragment 0 = some (x.offset 50) := by
  exact execution_position_at_label (i := 50) rfl rfl

private theorem resume_continue {m mem : Mem} {τ : World D} {ρ : Env D Γ} {n : Nat}
    (prefixRun : Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 42, x.fp⟩ mem)
    (frame : AgreeW L x.fp x.lo x.K m mem) (kept : Keeps x.fp x.pr m mem)
    (ready : x.Ready mem τ ρ) (fuelRead : x.read mem x.counter (BitVec.ofNat 64 n))
    (fuelBound : n ≤ x.fuel) :
    ∃ result, Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 2, x.fp⟩ result ∧
      AgreeW L x.fp x.lo x.K m result ∧ Keeps x.fp x.pr m result ∧ q.Entry n result τ ρ := by
  have jump := ready.jump 42 2 .header rfl execution_header_position
    (execution_offset_bound 42) (execution_offset_bound 2)
  exact ⟨mem, prefixRun.trans jump, frame, kept, ready, fuelRead, fuelBound⟩

private theorem resume_leave {m mem : Mem} {τ : World D} {ρ : Env D Γ}
    (prefixRun : Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 45, x.fp⟩ mem)
    (frame : AgreeW L x.fp x.lo x.K m mem) (kept : Keeps x.fp x.pr m mem)
    (ready : x.Ready mem τ ρ) :
    if (q.invW τ ρ).2 = true then
      Reach L x.fp x.lo x.K x.pr ⟨x.addr 39, x.fp⟩ m (x.addr 50) (q.invW τ ρ).1 ρ reserved
    else Stops ⟨x.addr 39, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have exit := q.leave_invariant ready
  by_cases valid : (q.invW τ ρ).2 = true
  · have left : Reach L x.fp x.lo x.K x.pr ⟨x.addr 45, x.fp⟩ mem (x.addr 50)
        (q.invW τ ρ).1 ρ reserved := by simpa only [valid, ↓reduceIte] using exit
    have completed := Reach.prefix prefixRun frame kept left
    simpa only [valid, ↓reduceIte] using completed
  · have stopped : Stops ⟨x.addr 45, x.fp⟩ mem (logikCode (D := D) .schleife) := by
      simpa only [valid, Bool.false_eq_true, ↓reduceIte] using exit
    have completed := Stops.prefix prefixRun stopped
    simpa only [valid, Bool.false_eq_true, ↓reduceIte] using completed

/-- Compose a completed body with its post-measure check and actual backedge
    or checked leave. The source body supplies both protected control words. -/
theorem resume {m : Mem} {σ : World D} {ρ : Env D (.index (D.count x.table) :: Γ)}
    {n : Nat} {old : Int} (leaving : Bool)
    (ready : x.Ready m σ ρ) (fuelBound : n ≤ x.fuel)
    (oldBound : -2 ^ 63 ≤ old ∧ old < 2 ^ 63)
    (fuelRead : x.read m x.counter (BitVec.ofNat 64 n))
    (savedRead : x.read m x.saved (BitVec.ofInt 64 old))
    (σ' : World D) (ρ' : Env D (.index (D.count x.table) :: Γ))
    (body : Reach L x.fp x.lo x.K (x.s :: x.counter :: x.saved :: x.pr)
      ⟨x.addr 39, x.fp⟩ m (if leaving then x.addr 44 else x.addr 41) σ' ρ' reserved) :
    let measured := q.massW σ' ρ'.tail
    if 0 ≤ measured.2 ∧ measured.2 ≤ x.bound ∧ measured.2 < old then
      if leaving then
        if (q.invW measured.1 ρ'.tail).2 = true then
          Reach L x.fp x.lo x.K x.pr ⟨x.addr 39, x.fp⟩ m (x.addr 50)
            (q.invW measured.1 ρ'.tail).1 ρ'.tail reserved
        else Stops ⟨x.addr 39, x.fp⟩ m (logikCode (D := D) .schleife)
      else ∃ m', Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 2, x.fp⟩ m' ∧
        AgreeW L x.fp x.lo x.K m m' ∧ Keeps x.fp x.pr m m' ∧ q.Entry n m' measured.1 ρ'.tail
    else Stops ⟨x.addr 39, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have body' : Reach L x.fp x.lo x.K (x.counter :: x.saved :: x.pr)
      ⟨x.addr 39, x.fp⟩ m (if leaving then x.addr 44 else x.addr 41) σ' ρ' reserved := by
    obtain ⟨mem, path, frame, env, world, kept⟩ := body
    exact ⟨mem, path, frame, env, world, fun j hj => kept j (by simp [hj])⟩
  obtain ⟨m1, bodyRun, bodyFrame, bodyEnv, bodyWorld, bodyKept, fuelRead1, savedRead1⟩ :=
    body_control_words body' fuelRead savedRead
  have ready1 := ready.body bodyFrame (envAt_tail bodyEnv) bodyWorld
  let i := if leaving then 44 else 41
  have which : i = 41 ∨ i = 44 := by cases leaving <;> simp [i]
  have bodyEnd : (if leaving then x.addr 44 else x.addr 41) = x.addr i := by
    cases leaving <;> rfl
  rw [bodyEnd] at bodyRun
  have checked := q.after_body i which old oldBound ready1 fuelRead1 savedRead1
  dsimp only
  by_cases good : 0 ≤ (q.massW σ' ρ'.tail).2 ∧ (q.massW σ' ρ'.tail).2 ≤ x.bound ∧
      (q.massW σ' ρ'.tail).2 < old
  · simp only [good, and_self, ↓reduceIte] at checked ⊢
    obtain ⟨m2, checkRun, checkFrame, checkKept, ready2, fuelRead2⟩ := checked
    have frame := bodyFrame.trans checkFrame
    have kept := bodyKept.trans checkKept
    cases leaving with
    | false =>
      change Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 41, x.fp⟩ m1 at bodyRun
      change Star ⟨x.addr 41, x.fp⟩ m1 ⟨x.addr 42, x.fp⟩ m2 at checkRun
      have completed := resume_continue (q := q) (bodyRun.trans checkRun) frame kept
        ready2 fuelRead2 fuelBound
      simpa only [Bool.false_eq_true, ↓reduceIte] using completed
    | true =>
      change Star ⟨x.addr 39, x.fp⟩ m ⟨x.addr 44, x.fp⟩ m1 at bodyRun
      change Star ⟨x.addr 44, x.fp⟩ m1 ⟨x.addr 45, x.fp⟩ m2 at checkRun
      have completed := resume_leave (q := q) (bodyRun.trans checkRun) frame kept ready2
      simpa only [↓reduceIte] using completed
  · simp only [good, and_self, ↓reduceIte] at checked ⊢
    exact Stops.prefix bodyRun checked

private theorem selection_empty {m : Mem} {τ : World D} {ρ : Env D Γ}
    (ready : x.Ready m τ ρ) (read : x.read m (x.s + 2) (Runner.IR.bool false)) :
    Reach L x.fp x.lo x.K x.pr ⟨x.addr 34, x.fp⟩ m (x.addr 50) τ ρ reserved := by
  have branch := ready.branch 34 50 (x.s + 2) .done _ rfl execution_done_position
    (execution_offset_bound 34) (execution_offset_bound 50)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (execution_zero_next (i := 34) (cell := x.s + 2) (target := .done) rfl)
  have finish : Star ⟨x.addr 34, x.fp⟩ m ⟨x.addr 50, x.fp⟩ m := by
    simpa only [Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] using branch
  exact ⟨m, finish, AgreeW.refl _ _ _ _ _, ready.env, ready.world, Keeps.refl _ _ _⟩

private theorem selection_cycle {m : Mem} {τ : World D} {ρ : Env D Γ}
    (ready : x.Ready m τ ρ) (read : x.read m (x.s + 2) (Runner.IR.bool true)) :
    Stops ⟨x.addr 34, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have branch := ready.branch 34 50 (x.s + 2) .done _ rfl execution_done_position
    (execution_offset_bound 34) (execution_offset_bound 50)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (execution_zero_next (i := 34) (cell := x.s + 2) (target := .done) rfl)
  have advance : Star ⟨x.addr 34, x.fp⟩ m ⟨x.addr 35, x.fp⟩ m := by
    simpa only [Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] using branch
  have jump := ready.jump 35 49 .stop rfl execution_stop_position
    (execution_offset_bound 35) (execution_offset_bound 49)
  exact Stops.prefix (advance.trans jump) ready.stop

/-- Fuel induction is supplied by runtime, with every premise instantiated by
    concrete assembled-image paths. No source interpreter or per-program premise. -/
theorem correct {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {body : Block D (vertragVon D f) true (.index (D.count x.table) :: Γ) Λ Λ}
    {l : Bool} {outerLeave outerNext : W}
    (bodyRun : ∀ m σ ρ, x.Ready m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K
        (x.s :: x.counter :: x.saved :: x.pr) ⟨x.addr 39, x.fp⟩ m
        (x.addr 41) (x.addr 44) (x.addr 41) (execBlock O passes R body σ ρ) reserved sc) :
    ∀ n m σ ρ, q.Entry n m σ ρ →
      Sim L P f x.σ0 x.ρ0 x.rp x.cfp x.fp x.lo x.K x.pr ⟨x.addr 2, x.fp⟩ m
        (x.addr 50) outerLeave outerNext
        (verbrauchLauf (l := l) x.table (fun σ ρ => execBlock O passes R body σ ρ)
          q.invW q.sel q.massW x.bound n σ ρ) reserved sc := by
  apply runtime x.table (fun σ ρ => execBlock O passes R body σ ρ)
    q.invW q.sel q.massW x.bound q.Entry x.low
  · intro mem σ ρ entry
    exact q.zero entry
  · intro n mem σ ρ entry invalid
    have head := q.head entry
    simpa only [invalid, ↓reduceIte] using head
  · intro n mem σ ρ σr entry valid selection
    obtain ⟨m1, scan, frame, kept, result, fuelRead⟩ := q.round entry valid
    rw [selection] at scan result
    simp only [Option.isSome_none, ↓reduceIte] at scan
    exact Reach.prefix scan frame kept (selection_empty result.ready result.liveRead)
  · intro n mem σ ρ σr entry valid selection
    obtain ⟨m1, scan, frame, kept, result, fuelRead⟩ := q.round entry valid
    rw [selection] at scan result
    simp only [Option.isSome_none, ↓reduceIte] at scan
    exact Stops.prefix scan (selection_cycle result.ready result.liveRead)
  · intro n mem σ ρ σr k live entry valid selection
    obtain ⟨m1, scan, scanFrame, scanKept, selected, fuelRead⟩ := q.round entry valid
    rw [selection] at scan selected
    simp only [Option.isSome_some, ↓reduceIte] at scan
    obtain ⟨m2, measureRun, measureFrame, measureKept, ready2, fuelRead2, savedRead⟩ :=
      q.before_body k selected fuelRead
    have completeRun := scan.trans measureRun
    have prefixFrame := scanFrame.trans measureFrame
    have prefixKept := scanKept.trans measureKept
    have oldBounds := q.measure_bounds σr ρ
    have oldBound := inW_spec x.bounds.2.2.2 oldBounds.1 oldBounds.2
    have pass := bodyRun m2 (q.massW σr ρ).1 (.cons k ρ) ready2
    dsimp only
    have again : ∀ (σ' : World D) (ρ' : Env D (.index (D.count x.table) :: Γ)),
        Reach L x.fp x.lo x.K (x.s :: x.counter :: x.saved :: x.pr)
          ⟨x.addr 39, x.fp⟩ m2 (x.addr 41) σ' ρ' reserved →
        let measured := q.massW σ' ρ'.tail
        if 0 ≤ measured.2 ∧ measured.2 ≤ x.bound ∧ measured.2 < (q.massW σr ρ).2 then
          ∃ m', Star ⟨x.addr 2, x.fp⟩ mem ⟨x.addr 2, x.fp⟩ m' ∧
            AgreeW L x.fp x.lo x.K mem m' ∧ Keeps x.fp x.pr mem m' ∧
            q.Entry n m' measured.1 ρ'.tail
        else Stops ⟨x.addr 2, x.fp⟩ mem (logikCode (D := D) .schleife) := by
      intro σ' ρ' body
      have resumed := q.resume false ready2 (by have := entry.2.2; omega)
        oldBound fuelRead2 savedRead σ' ρ' body
      dsimp only at resumed ⊢
      by_cases good : 0 ≤ (q.massW σ' ρ'.tail).2 ∧
          (q.massW σ' ρ'.tail).2 ≤ x.bound ∧ (q.massW σ' ρ'.tail).2 < (q.massW σr ρ).2
      · simp only [good, and_self, Bool.false_eq_true, ↓reduceIte] at resumed ⊢
        obtain ⟨m3, run, frame, kept, next⟩ := resumed
        exact ⟨m3, completeRun.trans run, prefixFrame.trans frame, prefixKept.trans kept, next⟩
      · simp only [good, and_self, ↓reduceIte] at resumed ⊢
        exact Stops.prefix completeRun resumed
    dsimp only [Sim] at pass
    generalize bodyOutcome : execBlock O passes R body (q.massW σr ρ).1 (.cons k ρ) = outcome at pass ⊢
    cases outcome with
    | ok σ' ρ' => exact again σ' ρ' pass
    | next _ σ' ρ' => exact again σ' ρ' pass
    | leave _ σ' ρ' =>
      have resumed := q.resume true ready2 (by have := entry.2.2; omega)
        oldBound fuelRead2 savedRead σ' ρ' pass
      dsimp only at resumed ⊢
      by_cases good : 0 ≤ (q.massW σ' ρ'.tail).2 ∧
          (q.massW σ' ρ'.tail).2 ≤ x.bound ∧ (q.massW σ' ρ'.tail).2 < (q.massW σr ρ).2
      · simp only [good, and_self, ↓reduceIte] at resumed ⊢
        by_cases valid : (q.invW (q.massW σ' ρ'.tail).1 ρ'.tail).2 = true
        · simp only [valid, ↓reduceIte] at resumed ⊢
          exact Reach.prefix completeRun prefixFrame prefixKept resumed
        · simp only [valid, Bool.false_eq_true, ↓reduceIte] at resumed ⊢
          exact Stops.prefix completeRun resumed
      · simp only [good, and_self, ↓reduceIte] at resumed ⊢
        exact Stops.prefix completeRun resumed
    | zurueck σ' value =>
      exact RetZR.prefix completeRun
        (prefixFrame.mono (Nat.le_trans (by decide : 2 ≤ FB) x.low)) pass
    | why σ' reason =>
      exact RetWhyR.prefix completeRun
        (prefixFrame.mono (Nat.le_trans (by decide : 2 ≤ FB) x.low)) pass
    | logik code => exact Stops.prefix completeRun pass
    | hardware code => exact Stops.prefix completeRun pass

end Gabbro.Stage0.Senke.Consuming.Loop
