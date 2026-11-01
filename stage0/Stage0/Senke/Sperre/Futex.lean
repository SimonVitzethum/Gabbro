/- The actual request-building instructions and syscall of `futexC`.
   Memory interference is an explicit client premise, never supplied by FutexOK. -/
module
public import Stage0.Senke.Sperre.Waiter
public import Runner.IR.Futex
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern]

/-- The exact seven request words emitted by `futexC`. -/
def FutexArgs (f : Nat → W) (a op v : W) : Prop :=
  f 10 = 202 ∧ f 11 = a ∧ f 12 = op ∧ f 13 = v ∧ f 14 = 0 ∧ f 15 = 0 ∧ f 16 = 0

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

theorem futex_prepare (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    {p op : Nat} {value : Option Int}
    (hc : At code p (futexC a op (s + 4) (s + 10) value))
    (hop : op < 2 ^ 31) (hv : ∀ k, value = some k → lit32 k = true) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (p + 7)), fp⟩ m' ∧
      LS m0 m' fp s a f' o c w ∧
      FutexArgs f' (BitVec.ofNat 64 a) (BitVec.ofNat 64 op)
        (match value with | some k => BitVec.ofInt 64 k | none => f 4) ∧
      (∀ j, j < 10 → f' j = f j) := by
  have ht := E.top
  obtain ⟨m1, s1, h1⟩ := ls_const E h (hc.get (j := 0) rfl) (d := 10) rfl (by omega) (by decide)
  obtain ⟨m2, s2, h2⟩ := ls_const E h1 (hc.get (j := 1) rfl) (d := 11) (by omega) (by omega) (lit32_nat (by omega))
  obtain ⟨m3, s3, h3⟩ := ls_const E h2 (hc.get (j := 2) rfl) (d := 12) (by omega) (by omega) (lit32_nat hop)
  have fourth : ∃ m4, Star ⟨pc + BitVec.ofNat 64 (16 * (p + 3)), fp⟩ m3
      ⟨pc + BitVec.ofNat 64 (16 * (p + 4)), fp⟩ m4 ∧
      LS m0 m4 fp s a (upd (upd (upd (upd f 10 202) 11 (BitVec.ofNat 64 a)) 12
        (BitVec.ofNat 64 op)) 13 (match value with | some k => BitVec.ofInt 64 k | none => f 4)) o c w := by
    cases value with
    | none =>
      obtain ⟨m4, s4, h4⟩ := ls_mov E h3 (hc.get (j := 3) rfl) (d := 13) (e := 4)
        (by omega) rfl (by omega) (by omega)
      exact ⟨m4, s4, by simpa [upd, BitVec.ofInt_natCast] using h4⟩
    | some k =>
      obtain ⟨m4, s4, h4⟩ := ls_const E h3 (hc.get (j := 3) rfl) (d := 13) (by omega) (by omega) (hv k rfl)
      exact ⟨m4, s4, by simpa [BitVec.ofInt_natCast] using h4⟩
  obtain ⟨m4, s4, h4⟩ := fourth
  obtain ⟨m5, s5, h5⟩ := ls_const E h4 (hc.get (j := 4) rfl) (d := 14) (by omega) (by omega) (by decide)
  obtain ⟨m6, s6, h6⟩ := ls_const E h5 (hc.get (j := 5) rfl) (d := 15) (by omega) (by omega) (by decide)
  obtain ⟨m7, s7, h7⟩ := ls_const E h6 (hc.get (j := 6) rfl) (d := 16) (by omega) (by omega) (by decide)
  refine ⟨m7, _, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7))))), h7, ?_, ?_⟩
  · cases value <;> simp [FutexArgs, upd]
  · intro j hj
    simp [upd, show j ≠ 10 by omega, show j ≠ 11 by omega, show j ≠ 12 by omega,
      show j ≠ 13 by omega, show j ≠ 14 by omega, show j ≠ 15 by omega, show j ≠ 16 by omega]

/-- Entry to the actual syscall, independent of any kernel behavior. -/
theorem futex_entry (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    {i : Nat} {op v : W}
    (hi : code[i]? = some (ci 23 ((s + 17 : Nat) : Int) ((s + 10 : Nat) : Int) 0))
    (hf : FutexArgs f (BitVec.ofNat 64 a) op v) :
    StopAt ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m (futexReq (BitVec.ofNat 64 a) op v) := by
  have ins := E.ins h.ag hi
  simp only [ci] at ins
  have hs := E.small
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hf
  apply runTo_sys ins
  all_goals rw [sx_nat (d := s + 10) (by omega)]
  · simpa [h0, futexReq] using h.sl 10 (by omega)
  · rw [show (8 : W) = BitVec.ofNat 64 (8 * 1) from rfl, slot_plus]
    simpa [h1, futexReq, Nat.add_assoc] using h.sl 11 (by omega)
  · rw [show (16 : W) = BitVec.ofNat 64 (8 * 2) from rfl, slot_plus]
    simpa [h2, futexReq, Nat.add_assoc] using h.sl 12 (by omega)
  · rw [show (24 : W) = BitVec.ofNat 64 (8 * 3) from rfl, slot_plus]
    simpa [h3, futexReq, Nat.add_assoc] using h.sl 13 (by omega)
  · rw [show (32 : W) = BitVec.ofNat 64 (8 * 4) from rfl, slot_plus]
    simpa [h4, futexReq, Nat.add_assoc] using h.sl 14 (by omega)
  · rw [show (40 : W) = BitVec.ofNat 64 (8 * 5) from rfl, slot_plus]
    simpa [h5, futexReq, Nat.add_assoc] using h.sl 15 (by omega)
  · rw [show (48 : W) = BitVec.ofNat 64 (8 * 6) from rfl, slot_plus]
    simpa [h6, futexReq, Nat.add_assoc] using h.sl 16 (by omega)

/-- Return from the real syscall. `resume` explicitly states what interference
    preserved/changed while the thread slept. No release is smuggled into FutexOK.
    A response is required: this theorem does not assert eventual WAIT return. -/
theorem futex_return (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w)
    {i : Nat} {op v r x o' c' w' : W} {mr : Mem}
    (hi : code[i]? = some (ci 23 ((s + 17 : Nat) : Int) ((s + 10 : Nat) : Int) 0))
    (hf : FutexArgs f (BitVec.ofNat 64 a) op v)
    (answer : Kern.ans (futexReq (BitVec.ofNat 64 a) op v) m (some (r, x)) mr)
    (resume : LS m0 mr fp s a f o' c' w') :
    ∃ m', Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (i + 1)), fp⟩ m' ∧
      LS m0 m' fp s a (upd f 17 r) o' c' w' := by
  have ins := E.ins h.ag hi
  simp only [ci] at ins
  have hs := E.small
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hf
  refine ⟨_, ls_star ins (by decide) ?_, resume.slot E (by omega) r⟩
  rw [← pc_next]
  simp only [Runner.IR.op]
  refine f1_run ins (f2_run ins ?_)
  rw [sx_nat (d := s + 17) (by omega), sx_nat (d := s + 10) (by omega)]
  simp only [ld]
  have r0 := h.sl 10 (by omega)
  rw [h0] at r0
  refine run_rd64 r0 ?_
  have args : ∀ j, j < 6 → m.rd64 (slot fp (BitVec.ofNat 64 (s + 10)) + BitVec.ofNat 64 (8 * (j + 1))) =
      some (match j with | 0 => BitVec.ofNat 64 a | 1 => op | 2 => v | _ => 0) := by
    intro j hj
    rw [slot_plus]
    match j, hj with
    | 0, _ => simpa [h1, Nat.add_assoc] using h.sl 11 (by omega)
    | 1, _ => simpa [h2, Nat.add_assoc] using h.sl 12 (by omega)
    | 2, _ => simpa [h3, Nat.add_assoc] using h.sl 13 (by omega)
    | 3, _ => simpa [h4, Nat.add_assoc] using h.sl 14 (by omega)
    | 4, _ => simpa [h5, Nat.add_assoc] using h.sl 15 (by omega)
    | 5, _ => simpa [h6, Nat.add_assoc] using h.sl 16 (by omega)
  refine run_rd64 (args 0 (by decide)) (run_rd64 (args 1 (by decide))
    (run_rd64 (args 2 (by decide)) (run_rd64 (args 3 (by decide))
    (run_rd64 (args 4 (by decide)) (run_rd64 (args 5 (by decide)) ?_)))))
  refine Run.sys answer ?_
  simp only [Runner.opt]
  exact run_wr64 (wr64_some ((E.frameK resume.ag).wr _ (by omega)))

end
end Gabbro.Stage0.Senke
