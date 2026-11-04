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
  it : Nat
  mt : Nat
  invCode : lowE (reserved := reserved) L inv (x.s + 4) = some (x.invariant, it)
  massCode : lowE (reserved := reserved) L mass (x.s + 4) = some (x.measure, mt)
  invTop : it ≤ x.Ks
  massTop : mt ≤ x.Ks

namespace Loop
variable {x : Image L P f reserved} {Γ : Ctx} {Λ : List (Res D)} (q : Loop x Γ Λ)

def invW (σ : World D) (ρ : Env D Γ) : World D × Bool :=
  let σi := σ.lese Λ q.inv.orte
  (σi, wahr? (Gabbro.Grammatik.eval σi q.inv σi ρ))
def massW (σ : World D) (ρ : Env D Γ) : World D × Int :=
  let σm := σ.lese Λ q.mass.orte
  (σm, (Gabbro.Grammatik.eval σm q.mass σm ρ).n)
def sel (σ : World D) (ρ : Env D Γ) :
    World D × Option (Wert D (.index (D.count x.table))) × Bool :=
  verbrauchSel x.table q.selector.member q.selector.edge σ ρ

def Entry (q : Loop x Γ Λ) (n : Nat) (m : Mem) (σ : World D) (ρ : Env D Γ) : Prop :=
  x.Ready m σ ρ ∧ x.read m x.counter (BitVec.ofNat 64 n) ∧ n ≤ x.fuel

variable {q} {n : Nat} {m : Mem} {σ : World D} {ρ : Env D Γ}

private theorem head_width_append (a b : List Piece) : width (a ++ b) = width a + width b := by
  induction a with
  | nil => simp only [List.nil_append, width, Nat.zero_add]
  | cons a rest ih => simp only [List.cons_append, width, ih, Nat.add_assoc]

private theorem head_offset_step {i : Nat} {piece : Piece}
    (found : x.fragment[i]? = some piece) : x.offset (i + 1) = x.offset i + piece.width := by
  have inside : i < x.fragment.length := by
    by_cases hi : i < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := i) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[i] = piece := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  simp only [Image.offset, List.take_succ_eq_append_getElem inside, element,
    head_width_append, width, Nat.add_zero]

private theorem head_offset_bound (i : Nat) : x.offset i ≤ x.code.length := by
  have splitWidth := congrArg width (List.take_append_drop i x.fragment)
  rw [head_width_append] at splitWidth
  calc
    x.offset i ≤ x.offset i + width (x.fragment.drop i) := Nat.le_add_right _ _
    _ = width x.fragment := splitWidth
    _ = x.code.length := (assemble_length x.assembled).symm

private theorem head_zero_next {i cell : Nat} {target : Label}
    (found : x.fragment[i]? = some (.zero cell target)) : x.addr i + 16 = x.addr (i + 1) := by
  have step := head_offset_step found
  change x.pc + BitVec.ofNat 64 (16 * x.offset i) + BitVec.ofNat 64 (16 * 1) =
    x.pc + BitVec.ofNat 64 (16 * x.offset (i + 1))
  rw [pc_add, step, Piece.width]

private theorem head_position_prefix (target : Label) (before after : List Piece) (pc : Nat) :
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

private theorem head_stop_position : position .stop x.fragment 0 = some (x.offset 49) := by
  have found : x.fragment[48]? = some (.label .stop) := rfl
  have inside : 48 < x.fragment.length := by
    by_cases hi : 48 < x.fragment.length
    · exact hi
    · have missing := List.getElem?_eq_none (l := x.fragment) (i := 48) (by omega)
      cases (missing.symm.trans found)
  have element : x.fragment[48] = .label .stop := by
    simpa only [List.getElem?_eq_getElem inside, Option.some.injEq] using found
  have splitImage : x.fragment =
      x.fragment.take 48 ++ .label .stop :: x.fragment.drop 49 := by
    have split := List.take_append_drop 48 x.fragment
    rw [List.drop_eq_getElem_cons inside, element] at split
    exact split.symm
  have absent : (x.fragment.take 48).all (fun piece => match piece with
      | .label name => decide (name ≠ .stop)
      | _ => true) = true := rfl
  have located := head_position_prefix .stop (x.fragment.take 48)
    (.label .stop :: x.fragment.drop 49) 0 absent
  rw [← splitImage] at located
  have atLabel : position .stop (.label .stop :: x.fragment.drop 49)
      (0 + width (x.fragment.take 48)) = some (width (x.fragment.take 48)) := by
    rw [position, ite_eq_left rfl, Nat.zero_add]
  calc
    position .stop x.fragment 0 = some (width (x.fragment.take 48)) := located.trans atLabel
    _ = some (x.offset 49) := by
      congr 1
      simpa only [Image.offset, Piece.width, Nat.add_zero] using (head_offset_step found).symm

/-- Zero fuel jumps to the actual stop block before reading the invariant. -/
theorem zero (entry : q.Entry 0 m σ ρ) :
    Stops ⟨x.addr 2, x.fp⟩ m (logikCode (D := D) .schleife) := by
  obtain ⟨ready, read, bound⟩ := entry
  have jump := ready.branch 2 49 x.counter .stop 0 rfl head_stop_position
    (head_offset_bound 2) (head_offset_bound 49)
    (by have := x.controls; have := x.scratch; have := x.layout.ks; omega)
    read (head_zero_next (i := 2) (cell := x.counter) (target := .stop) rfl)
  exact Stops.prefix (by simpa using jump) ready.stop

/-- Positive fuel is decremented in its reserved word, preserving all lexical
    variables and the surrounding protected words. -/
theorem fuel (entry : q.Entry (n + 1) m σ ρ) :
    ScanRun L x.fp x.lo x.K x.pr (x.addr 2) (x.addr 4) m (q.Entry n · σ ρ) := by
  obtain ⟨ready, read, bound⟩ := entry
  have room : x.s + 4 < x.K := by have := x.scratch; have := x.layout.ks; omega
  have controlRoom : x.counter < x.K := by have := x.controls; have := x.scratch; omega
  have counterBelow : x.counter < x.s + 4 := by
    have := x.controls
    have := x.scratch
    omega
  have fuelEq := counter_fuel_step n (by have := x.bounds.1; omega)
  have branch := ready.branch 2 49 x.counter .stop _ rfl head_stop_position
    (head_offset_bound 2) (head_offset_bound 49) controlRoom read
    (head_zero_next (i := 2) (cell := x.counter) (target := .stop) rfl)
  simp only [fuelEq.1, ↓reduceIte] at branch
  have code := (ready.slice 3 (.code [ci 1 (x.s + 4) 1 0, ci 4 x.counter x.counter (x.s + 4)])
    _ rfl rfl).1
  obtain ⟨oneRun, oneFrame, oneReady, oneRead⟩ := ready.literal
    (codeAt_left (a := [ci 1 (x.s + 4) 1 0]) code)
    (by rw [← q.selector.origin]; omega) (by omega) room (by decide)
  have wholeFar := (ready.slice 3 (.code [ci 1 (x.s + 4) 1 0,
    ci 4 x.counter x.counter (x.s + 4)]) _ rfl rfl).2
  have tail := (codeAt_right (a := [ci 1 (x.s + 4) 1 0]) code).agree oneFrame
    (codeFar_right (n := 1) (k := 1) wholeFar)
  have counterRead := Image.read_agree oneFrame ready.frame counterBelow (Nat.le_of_lt room) read
  let m1 := write m (slot x.fp (BitVec.ofNat 64 (x.s + 4))) 8 1
  let value := BitVec.ofNat 64 (n + 1) - 1
  let m2 := write m1 (slot x.fp (BitVec.ofNat 64 x.counter)) 8 value.toNat
  have run := Image.binary_to (cell := x.counter) (a := x.counter) (b := x.s + 4) (o := 4)
    (value := value) tail oneReady.frame x.small controlRoom controlRoom room
    counterRead oneRead (g := fun a b => some (a - b)) rfl (by decide) rfl
  have counterFrame : Agree x.fp x.counter x.K m1 m2 :=
    agree_write oneReady.frame.room (Nat.le_refl _) controlRoom value.toNat
  have frame : Agree x.fp x.counter x.K m m2 :=
    (oneFrame.mono (Nat.le_of_lt counterBelow)).trans counterFrame
  have finalReady := oneReady.reserved value x.controls.1
    (by have := x.controls; omega) (by rw [← q.selector.origin]; have := x.scratch; omega)
  have blockEnd := x.addr_next_code (i := 3)
    (block := [ci 1 (x.s + 4) 1 0, ci 4 x.counter x.counter (x.s + 4)]) rfl
  change x.addr 3 + 32 = x.addr 4 at blockEnd
  refine ⟨m2, ?_, agreeW_of (frame.mono x.controls.1), ?_, finalReady, ?_, by omega⟩
  · have total := branch.trans (oneRun.trans run)
    change Star ⟨x.addr 2, x.fp⟩ m ⟨x.addr 3 + 16 + 16, x.fp⟩ m2 at total
    rw [BitVec.add_assoc, show (16 : W) + 16 = 32 from rfl, blockEnd] at total
    exact total
  · have k1 := keeps_of_agree oneFrame ready.frame.room
      (fun j hj => by have := x.kept j hj; omega) (by omega)
    have k2 := keeps_write oneReady.frame.room controlRoom
      (fun j hj => by have := x.kept j hj; have := x.scratch; omega)
      (fun hj => (x.kept _ hj).2.1 rfl) value.toNat
    exact k1.trans k2
  · have result := rd_same oneReady.frame controlRoom value
    simpa only [Image.read, m2, value, fuelEq.2] using result

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
  have branch := ready2.branch 5 49 (x.s + 4) .stop _ rfl head_stop_position
    (head_offset_bound 5) (head_offset_bound 49)
    (by have := x.scratch; have := x.layout.ks; omega) read
    (head_zero_next (i := 5) (cell := x.s + 4) (target := .stop) rfl)
  cases truth : (q.invW σ ρ).2 with
  | false =>
    simp only [truth, ↓reduceIte]
    have stopRun : Star ⟨x.addr 5, x.fp⟩ m2 ⟨x.addr 49, x.fp⟩ m2 := by
      simpa only [truth, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte] using branch
    exact Stops.prefix (fuelRun.trans (invRun.trans stopRun)) ready2.stop
  | true =>
    simp only [truth, Bool.true_eq_false, ↓reduceIte]
    have passRun : Star ⟨x.addr 5, x.fp⟩ m2 ⟨x.addr 6, x.fp⟩ m2 := by
      simpa only [truth, Runner.IR.bool, show (1 : W) ≠ 0 by decide, ↓reduceIte] using branch
    exact ⟨m2, fuelRun.trans (invRun.trans passRun), fuelFrame.trans invFrame,
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
  obtain ⟨m2, scan, frame, kept, result⟩ := q.selector.selection (σ := σr) (ρ := ρ) readReady
  exact ⟨m2, scan, frame, (fun j hj => kept j (by simp [hj])), result,
    (kept x.counter (by simp)).trans read⟩

end Loop
end Gabbro.Stage0.Senke.Consuming
