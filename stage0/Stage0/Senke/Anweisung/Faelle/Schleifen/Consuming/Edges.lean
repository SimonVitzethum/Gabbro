/- Concrete local edges; all paths are executions of the assembled image. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Image
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}

/-- Normalize assembler-derived offsets, retaining symbolic operand lengths. -/
macro "consume_arith " x:ident : tactic => `(tactic| (
  have imageLength := assemble_length $x.assembled
  have imageSize := assemble_size $x.assembled
  have initialLiteral := lit32_nat $x.bounds.1
  simp [Image.addr, Image.offset, Image.fragment, pieces, position, width, Piece.width,
    travCountC_length, travCountSize, initialLiteral, decrease, narrowC,
    stopC, sysC, List.length_append] at imageLength imageSize ⊢
  all_goals first | omega | rfl | ac_rfl | (rw [addr_norm]; congr 2 <;> omega)
    | (apply adr_eq; omega)))

namespace Image
variable {reserved : Nat} {x : Image L P f reserved}
variable {Γ : Ctx} {m m' : Mem} {σ : World D} {ρ : Env D Γ}

/-- One reserved write preserves lexical variables even though they lie above it. -/
theorem Ready.reserved (h : x.Ready m σ ρ) {cell : Nat} (value : W)
    (low : x.lo ≤ cell) (allocated : cell < FB + reserved)
    (ctx : frei Γ reserved ≤ x.K) :
    x.Ready (write m (slot x.fp (BitVec.ofNat 64 cell)) 8 value.toNat) σ ρ := by
  have inside : cell < x.K := by unfold frei at ctx; omega
  have a := agree_write h.frame.room (lo := cell) (Nat.le_refl _) inside value.toNat
  have env := (reserved_write_preserves (L := L) (j := cell - FB) value.toNat
    h.frame.room ctx (by have := x.low; omega) h.env).1
  have cellEq : FB + (cell - FB) = cell := by have := x.low; omega
  rw [cellEq] at env
  exact ⟨h.frame.agree a, h.code.agree a x.far, env,
    weltAt_stab x.layout.lay x.layout.top m _ h.world (a.mono (Nat.zero_le _)),
    h.surround.agree a h.frame (by have := x.low; omega),
    h.head.agree a h.frame (by rw [← x.abi]; omega)⟩

/-- A move to reserved control storage is proved at the actual write. -/
theorem Ready.save (h : x.Ready m σ ρ) {i cell source : Nat} {value : W}
    (found : x.fragment[i]? = some (.code [ci 2 cell source 0]))
    (sourceBound : source < x.K) (read : x.read m source value)
    (low : x.lo ≤ cell) (allocated : cell < FB + reserved)
    (savedCell : cell = x.saved)
    (ctx : frei Γ reserved ≤ x.K)
    (endAt : x.addr i + 16 = x.addr (i + 1)) :
    ∃ m', Star ⟨x.addr i, x.fp⟩ m ⟨x.addr (i + 1), x.fp⟩ m' ∧
      AgreeW L x.fp x.lo x.K m m' ∧ x.Ready m' σ ρ ∧
      Keeps x.fp (x.counter :: x.pr) m m' ∧ x.read m' cell value ∧
      (∀ j, j < x.K → j ≠ cell →
        m'.rd64 (slot x.fp (BitVec.ofNat 64 j)) = m.rd64 (slot x.fp (BitVec.ofNat 64 j))) := by
  have inside : cell < x.K := by unfold frei at ctx; omega
  have slice := h.slice i (.code [ci 2 cell source 0]) _ found rfl
  have run := mov_to slice.1 h.frame inside sourceBound x.small read
  have a := agree_write h.frame.room (lo := cell) (Nat.le_refl _) inside value.toNat
  refine ⟨_, ?_, agreeW_of (a.mono low), h.reserved value low allocated ctx, ?_,
    rd_same h.frame inside value, ?_⟩
  · simpa only [List.length_singleton, endAt] using run
  · apply keeps_write h.frame.room inside
    · intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · have := x.controls; have := x.scratch; have := x.layout.ks; omega
      · have := x.protected j hj; have := x.scratch; have := x.layout.ks; omega
    · intro member
      simp only [List.mem_cons] at member
      rcases member with eq | member
      · have := x.controls; omega
      · have := x.protected cell member; omega
  · intro j insideJ different
    exact rd_other h.frame.room inside insideJ (Ne.symm different)

/-- Evaluate a scan bound using the existing instruction-level lemma. -/
theorem Ready.bound (h : x.Ready m σ ρ) {i index j : Nat}
    (ctx : frei Γ reserved ≤ x.s + 4) (below : index < x.s + 4)
    (smallIndex : j < 2 ^ 63) (read : x.read m index (BitVec.ofNat 64 j))
    (found : x.fragment[i]? = some (.code
      (travCountC (x.s + 5) (D.count x.table) ++ [ci 13 (x.s + 4) index (x.s + 5)])))
    (endAt : x.addr i + BitVec.ofNat 64 (16 * (travCountSize (D.count x.table) + 1)) =
      x.addr (i + 1)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr i) (x.addr (i + 1)) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp (x.s + 4) x.K m m' ∧ x.read m' (x.s + 4)
        (Runner.IR.bool (decide ((j : Int) < D.count x.table)))) := by
  have pre := h.pre i (x.s + 4) _ ctx found
  have run := scan_bound_ok pre (by have := x.scratch; have := x.layout.ks; omega)
    below smallIndex x.bounds.2.2.1 read
  obtain ⟨m', path, a, kept, ready, localFrame, v, rv, rfl⟩ := h.ok run
    (by simpa only [List.length_append, travCountC_length, List.length_singleton] using endAt)
    ctx (by omega) (by have := x.scratch; have := x.layout.ks; omega)
  exact ⟨m', path, a, kept, ready, localFrame, rv⟩

/-- Read a surviving selector word after expression scratch has been used. -/
theorem read_agree {d cell : Nat} {v : W} (a : Agree x.fp d x.K m m')
    (h : FrameOK m x.fp x.K) (below : cell < d) (room : d ≤ x.K)
    (read : x.read m cell v) : x.read m' cell v := by
  rw [Image.read, agree_rd_low a h.room below room]
  exact read

/-- A binary instruction with its exact destination write. -/
theorem binary_to {m : Mem} {pc fp : W} {K cell a b o : Nat} {va vb value : W}
    {g : W → W → Option W} (code : CodeAt m pc [ci o cell a b])
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (cellBound : cell < K) (aBound : a < K) (bBound : b < K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some va)
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 b)) = some vb)
    (opEq : op o = bin g) (opBound : o < 256) (valueEq : g va vb = some value) :
    Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩
      (write m (slot fp (BitVec.ofNat 64 cell)) 8 value.toNat) := by
  have hi := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply star_ins code (by simpa only [ci] using opBound)
  simp only [ci, opEq]
  apply run_bin hi
  · simpa only [sx_nat (by omega)] using ra
  · simpa only [sx_nat (by omega)] using rb
  · exact valueEq
  · simpa only [sx_nat (by omega)] using wr64_some (frame.wr cell cellBound)

/-- Increment one selector word; retain every other word below scratch. -/
theorem Ready.increment (h : x.Ready m σ ρ) {i j cell n : Nat}
    (ctx : frei Γ reserved ≤ cell) (low : x.s ≤ cell)
    (room : cell < x.s + 4) (read : x.read m cell (BitVec.ofNat 64 n))
    (found : x.fragment[i]? = some (.code
      [ci 1 (x.s + 4) 1 0, ci 3 cell cell (x.s + 4)]))
    (endAt : x.addr i + 32 = x.addr j) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr i) (x.addr j) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp cell x.K m m' ∧
        (∀ q, q < x.s + 4 → q ≠ cell →
          m'.rd64 (slot x.fp (BitVec.ofNat 64 q)) = m.rd64 (slot x.fp (BitVec.ofNat 64 q))) ∧
        x.read m' cell (BitVec.ofNat 64 (n + 1))) := by
  have inside : x.s + 4 < x.K := by have := x.scratch; have := x.layout.ks; omega
  have pre := h.pre i cell _ ctx found
  let m1 := write m (slot x.fp (BitVec.ofNat 64 (x.s + 4))) 8 1
  have a1 : Agree x.fp (x.s + 4) x.K m m1 := agree_write h.frame.room (by omega) inside 1
  have run1 := const_to pre.left.code h.frame inside x.small (by decide : lit32 1 = true)
  have tail := pre.next (a1.mono (by omega)) (Nat.le_refl _) (by omega)
  have old := read_agree a1 h.frame room (by omega) read
  have one : x.read m1 (x.s + 4) 1 := rd_same h.frame inside 1
  let value := BitVec.ofNat 64 n + 1
  let m2 := write m1 (slot x.fp (BitVec.ofNat 64 cell)) 8 value.toNat
  have run2 := binary_to tail.code tail.frame x.small (by omega) (by omega) inside old one
    (g := fun a b => some (a + b)) rfl (by decide) rfl
  have a2 : Agree x.fp cell x.K m1 m2 := agree_write tail.frame.room (by omega) (by omega) _
  have aa := (a1.mono (by omega : cell ≤ x.s + 4)).trans a2
  refine ⟨m2, ?_, agreeW_of (aa.mono (by have := x.controls; have := x.scratch; omega)),
    keeps_of_agree aa h.frame.room (by
      intro q hq; have := x.controls; have := x.scratch
      simp only [List.mem_cons] at hq
      rcases hq with rfl | rfl | hq <;> try omega
      have := x.protected q hq; omega) (by omega),
    h.agree aa ctx (by rw [← x.abi]; have := x.controls; have := x.scratch; omega) (by omega),
    aa, ?_, ?_⟩
  · simpa only [addr_norm, show (16 : Nat) + 16 = 32 by decide, endAt] using run1.trans run2
  · intro q below different
    rw [rd_other tail.frame.room (by omega) (by omega) (Ne.symm different)]
    exact agree_rd_low a1 h.frame.room below (by omega)
  · have result := rd_same tail.frame (by omega : cell < x.K) value
    simpa only [value, BitVec.ofNat_add] using result

/-- Stop code is reached through an ordinary extracted block. -/
theorem Ready.stop (h : x.Ready m σ ρ) :
    Stops ⟨x.addr 49, x.fp⟩ m (logikCode (D := D) .schleife) := by
  have slice := h.slice 49 (.code (stopC (logikCode (D := D) .schleife) (x.s + 4)))
    _ rfl rfl
  exact stop_ok slice.1 (by simpa [stopC, sysC] using slice.2) h.frame
    (by have := x.scratch; have := x.layout.ks; omega) x.small x.bounds.2.1

/-- A literal edge with an exact write, for the two selector initializers. -/
theorem Ready.literal (h : x.Ready m σ ρ) {pc : W} {cell : Nat} {value : Int}
    (code : CodeAt m pc [ci 1 cell value 0])
    (ctx : frei Γ reserved ≤ cell) (low : x.s ≤ cell)
    (inside : cell < x.K) (literal : lit32 value = true) :
    let m' := write m (slot x.fp (BitVec.ofNat 64 cell)) 8 (BitVec.ofInt 64 value).toNat
    Star ⟨pc, x.fp⟩ m ⟨pc + 16, x.fp⟩ m' ∧
      Agree x.fp cell x.K m m' ∧ x.Ready m' σ ρ ∧ x.read m' cell (BitVec.ofInt 64 value) := by
  have a := agree_write h.frame.room (lo := cell) (Nat.le_refl _) inside
    (BitVec.ofInt 64 value).toNat
  exact ⟨const_to code h.frame inside x.small literal, a,
    h.agree a ctx (by rw [← x.abi]; have := x.controls; have := x.scratch; omega)
      (by omega), rd_same h.frame inside _⟩

/-- The self-index test preceding membership borrowing. -/
theorem Ready.same (h : x.Ready m σ ρ) {a b : Zahl 0 (D.count x.table - 1)}
    (ctx : frei Γ reserved ≤ x.s + 4)
    (ra : x.read m (x.s + 1) (BitVec.ofInt 64 a.n))
    (rb : x.read m x.s (BitVec.ofInt 64 b.n)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.addr 16) (x.addr 17) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp (x.s + 4) x.K m m' ∧
        x.read m' (x.s + 4) (Runner.IR.bool (decide (a.n = b.n)))) := by
  have pre := h.pre 16 (x.s + 4) [ci 14 (x.s + 4) (x.s + 1) x.s] ctx rfl
  have countBounds := x.bounds.2.2.1
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at countBounds
  have ae : -2 ^ 63 ≤ a.n ∧ a.n < 2 ^ 63 := by have := a.lo_le; have := a.le_hi; omega
  have be : -2 ^ 63 ≤ b.n ∧ b.n < 2 ^ 63 := by have := b.lo_le; have := b.le_hi; omega
  obtain ⟨m', run, frame, kept, ready, localFrame, v, read, rfl⟩ := h.ok
    (eng_bin_ok pre (by have := x.scratch; have := x.layout.ks; omega)
      (by have := x.scratch; have := x.layout.ks; omega)
      (by have := x.scratch; have := x.layout.ks; omega) ra rb
      (g := fun a b => some (Runner.IR.bool (a == b))) rfl (by decide) rfl)
    (by consume_arith x) ctx (by omega) (by have := x.scratch; have := x.layout.ks; omega)
  refine ⟨m', run, frame, kept, ready, localFrame, ?_⟩
  simpa only [beq_in ae be] using read

end Image
end Gabbro.Stage0.Senke.Consuming
