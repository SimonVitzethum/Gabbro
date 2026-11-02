/- Runtime loop edges consume the actual block simulation and its world-aware frame. -/
module

public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counters.Counter
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil3
public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Anweisung.Verzweigung
public import Stage0.Senke.Anweisung.Faelle.Kontext

@[expose] public section



namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR

variable [Kern]

/-- Initialize from the semantic fuel argument itself. The representability
check rejects budgets outside the instruction's signed immediate range. -/
theorem counter_initialize {m : Mem} {pc fp : W} {K counter budget : Nat}
    (code : CodeAt m pc (foreverCounterInit counter (budget : Int)))
    (frame : FrameOK m fp K) (inside : counter < K)
    (small : K < 2 ^ 31) (fuel : budget < 2 ^ 31) :
    ∃ m', Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget) := by
  have literal : lit32 (budget : Int) = true := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have run := const_step_counted code frame inside small literal
  refine ⟨_, run, ?_⟩
  rw [BitVec.ofInt_natCast]
  exact rd64_write_same (frame.rd counter inside)

/-- Execute a literal in the reserved prefix and retain the complete body-entry
interface with exactly one completed S0IR instruction. This transports the lexical
locals, callee availability, entry snapshot, world and enclosing sentinels. -/
theorem reserved_literal_entry {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc rp cfp : W} {K Ks lo reserved cell : Nat} {pr : List Nat}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {m : Mem} {code : List II} {value : Int}
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) ([ci 1 cell value 0] ++ code) ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (abi : (functionFrame P f).internalResult ≤ lo) (low : lo ≤ cell)
    (allocated : cell < FB + reserved) (bound : frei Γ reserved ≤ K)
    (literal : lit32 value = true)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ cell) :
    ∃ m', Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' (pc + 16) fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 cell)) = some (BitVec.ofInt 64 value) := by
  have protectedPrefix := functionFrame_prefix P f
  have inside : cell < K := by unfold frei at bound; omega
  have run := const_step_counted (codeAt_left pre.code) pre.frame inside pre.small literal
  obtain ⟨write, stored, frame⟩ := wr_slot pre.frame inside (BitVec.ofInt 64 value)
  have allFrame := frame.mono low
  have env := (reserved_write_preserves (L := L) (j := cell - FB)
    (BitVec.ofInt 64 value).toNat pre.frame.room bound (by omega) pre.env).1
  have eq : FB + (cell - FB) = cell := by omega
  rw [eq] at env
  have far := codeFar_right (n := 1) (k := code.length)
    (by simpa [Nat.add_comm] using pre.far)
  refine ⟨_, run, agreeW_of allFrame, ?_,
    surround.agreeW layout (agreeW_of allFrame) (by omega),
    head.agree allFrame pre.frame abi, ?_, ?_, stored⟩
  · exact ⟨pre.ctx, pre.small, pre.frame.agree frame,
      (codeAt_right pre.code).agree allFrame far, far, env, trivial, wstab_true _ _⟩
  · exact weltAt_stab layout.lay layout.top m _ world (allFrame.mono (Nat.zero_le _))
  · intro j hj
    exact Mem.rd64_write_far (slot_far pre.frame.room inside (hprotected j hj).1
      (Ne.symm (hprotected j hj).2))

/-- Exactly two emitted initialization instructions preserve the complete source entry.
    The second write protects the freshly initialized counter as well as the
    enclosing sentinels; neither value is supplied as a runtime assumption. -/
theorem forever_initialize_entry {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc rp cfp : W} {K Ks lo reserved counter one budget : Nat} {pr : List Nat}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {m : Mem} {code : List II}
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounterInit counter budget ++ [ci 1 one 1 0] ++ code) ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (abi : (functionFrame P f).internalResult ≤ lo)
    (lowCounter : lo ≤ counter) (lowOne : lo ≤ one)
    (allocatedCounter : counter < FB + reserved) (allocatedOne : one < FB + reserved)
    (distinct : counter ≠ one) (bound : frei Γ reserved ≤ K)
    (fuel : budget < 2 ^ 31)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ counter ∧ j ≠ one) :
    ∃ m', Counted 2 ⟨pc, fp⟩ m ⟨pc + 32, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' (pc + 32) fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1 := by
  have protectedPrefix := functionFrame_prefix P f
  have counterBound : counter < K := by unfold frei at bound; omega
  have literal : lit32 (budget : Int) = true := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
    omega
  obtain ⟨m1, run1, frame1, pre1, surround1, head1, world1, keeps1, read1⟩ :=
    reserved_literal_entry layout pre surround head world abi lowCounter
      allocatedCounter bound literal (fun j hj => ⟨(hprotected j hj).1, (hprotected j hj).2.1⟩)
  obtain ⟨m2, run2, frame2, pre2, surround2, head2, world2, keeps2, read2⟩ :=
    reserved_literal_entry (pr := counter :: pr) layout pre1 surround1 head1 world1 abi lowOne
      allocatedOne bound (by decide) (by
        intro j hj
        rcases List.mem_cons.mp hj with h | h
        · subst j; exact ⟨counterBound, distinct⟩
        · exact ⟨(hprotected j h).1, (hprotected j h).2.2⟩)
  have pcEq : pc + 16 + 16 = pc + 32 := by
    rw [BitVec.add_assoc]; rfl
  rw [pcEq] at run2 pre2
  refine ⟨m2, run1.trans run2, frame1.trans frame2, pre2, surround2, head2,
    world2, ?_, ?_, read2⟩
  · intro j hj
    exact (keeps2 j (by simp [hj])).trans (keeps1 j hj)
  · rw [keeps2 counter (by simp)]
    simpa only [BitVec.ofInt_natCast] using read1

/-- The emitted word decrement agrees with canonical natural fuel, without
    wrapping, for every representable positive budget. -/
theorem counter_fuel_step (n : Nat) (fits : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ 0 ∧
      BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    change (n + 1) % 2 ^ 64 = 0 at this
    rw [Nat.mod_eq_of_lt fits] at this
    omega
  · have h := BitVec.ofNat_sub_ofNat_of_le (w := 64) (n + 1) 1 (by decide) (by omega)
    simpa using h

/-- Zero, one and two are genuine fuel values with distinct nonwrapping steps. -/
theorem counter_fuel_step_zeuge :
    BitVec.ofNat 64 1 - 1 = 0 ∧ BitVec.ofNat 64 2 - 1 = 1 := by decide

/-- A lowered body reaches its backedge with the reserved runtime budget intact.
The equality follows from the body simulation's frame, including reachable calls
and world writes; no separate preservation hypothesis is admitted. -/
theorem Reach.counter_backedge {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {fp pc : W} {lo K Ks counter : Nat} {pr : List Nat}
    {t : T} {m : Mem} {σ : World D} {ρ : Env D Γ} {reserved : Nat}
    {jump b c : BitVec 32} {value : W}
    (body : Reach L fp lo K pr t m pc σ ρ reserved)
    (layout : WIn L fp Ks K) (hprotected : counter < lo ∨ counter ∈ pr) (bound : lo ≤ K)
    (initial : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value)
    (edge : InsAt m pc 18 jump b c) (far : CodeFar pc 1 fp K) :
    ∃ m', Star t m ⟨pc + sx jump, fp⟩ m' ∧
      AgreeW L fp lo K m m' ∧ EnvAt L m' fp ρ reserved ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value := by
  obtain ⟨m', run, frame, env, world, keeps⟩ := body
  have code : CodeAt m pc [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst k
    simpa [II.f] using edge
  have code' := codeAt_agreeWIn layout frame code far
  have edge' := code' 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at edge'
  have hj := Star.one (run_step (t := ⟨pc, fp⟩) edge' (by decide)
    (run_jmp (t := ⟨pc, fp⟩) edge'))
  refine ⟨m', run.trans ?_, frame, env, world, keeps, ?_⟩
  · simpa [II.f] using hj
  · cases hprotected with
    | inl below => rw [counter_preserved layout frame below bound]; exact initial
    | inr member => rw [keeps counter member]; exact initial

end Gabbro.Stage0.Senke
