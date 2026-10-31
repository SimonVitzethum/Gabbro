/- Runtime loop edges consume the actual block simulation and its world-aware frame. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Anweisung.Verzweigung
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR

variable [Kern]

/-- Initialize from the semantic fuel argument itself. The representability
check rejects budgets outside the instruction's signed immediate range. -/
theorem counter_initialize {m : Mem} {pc fp : W} {K counter budget : Nat}
    (code : CodeAt m pc (foreverCounterInit counter (budget : Int)))
    (frame : FrameOK m fp K) (inside : counter < K)
    (small : K < 2 ^ 31) (fuel : budget < 2 ^ 31) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget) := by
  have literal : lit32 (budget : Int) = true := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have run := const_step code frame inside small literal
  refine ⟨_, run, ?_⟩
  rw [BitVec.ofInt_natCast]
  exact rd64_write_same (frame.rd counter inside)

/-- Execute a literal in the reserved prefix and retain the complete body-entry
interface. Unlike initialization by a bare `Star`, this transports the lexical
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
    (abi : FB + (D.params f).length ≤ lo) (low : lo ≤ cell)
    (allocated : cell < FB + reserved) (bound : frei Γ reserved ≤ K)
    (literal : lit32 value = true)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ cell) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' (pc + 16) fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 cell)) = some (BitVec.ofInt 64 value) := by
  have inside : cell < K := by unfold frei at bound; omega
  have run := const_step (codeAt_left pre.code) pre.frame inside pre.small literal
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

/-- Both emitted initialization instructions preserve the complete source entry.
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
    (abi : FB + (D.params f).length ≤ lo)
    (lowCounter : lo ≤ counter) (lowOne : lo ≤ one)
    (allocatedCounter : counter < FB + reserved) (allocatedOne : one < FB + reserved)
    (distinct : counter ≠ one) (bound : frei Γ reserved ≤ K)
    (fuel : budget < 2 ^ 31)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ counter ∧ j ≠ one) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 32, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' (pc + 32) fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1 := by
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

/-- Reconstruct the complete body-entry interface after an actual backedge.
    Code and callee availability follow from the simulated world-aware frame;
    the new environment and world come from execution, not preservation claims.
    The reservation retains the counter and any immutable control slots in `pr`. -/
theorem Reach.counter_reentry {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc back rp cfp : W} {lo K Ks counter reserved : Nat} {pr : List Nat}
    {m : Mem} {σ' : World D} {ρ ρ' : Env D Γ}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {code : List II}
    {jump b c : BitVec 32} {value : W}
    (body : Reach L fp lo K pr ⟨pc, fp⟩ m back σ' ρ' reserved)
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hprotected : counter < lo ∨ counter ∈ pr) (bound : lo ≤ K)
    (abi : FB + (D.params f).length ≤ lo)
    (initial : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value)
    (edge : InsAt m back 18 jump b c) (far : CodeFar back 1 fp K)
    (target : back + sx jump = pc) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' pc fp K (frei Γ reserved) code ρ' reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ' ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value := by
  obtain ⟨m', run, frame, env, world, keeps, counter⟩ :=
    body.counter_backedge layout hprotected bound initial edge far
  refine ⟨m', ?_, frame, ?_, surround.agreeW layout frame (by omega),
    head.agreeW layout frame abi, world, keeps, counter⟩
  · simpa only [target] using run
  · exact ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame frame,
      codeAt_agreeWIn layout frame pre.code pre.far, pre.far, env,
      trivial, wstab_true _ _⟩

/-- A zero budget executes the real conditional branch into the progress stop,
before an invariant or body can execute. -/
theorem counter_budget_stop {t : T} {m : Mem} {d jump c : BitVec 32}
    (instruction : InsAt m t.pc 19 d jump c)
    (zero : m.rd64 (slot t.fp (sx d)) = some 0)
    (stop : Stops {t with pc := t.pc + sx jump} m 111) :
    Stops t m 111 :=
  Stops.prefix (Star.one (counter_zero instruction zero)) stop

/-- Test, decrement, actual simulated body and emitted backedge compose into
one runtime iteration. The body result is the ordinary lowering simulation,
whose frame supplies counter retention even through world writes and calls. -/
theorem counter_iteration {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {fp pc back : W} {lo K Ks counter : Nat} {pr : List Nat}
    {m m1 : Mem} {σ : World D} {ρ : Env D Γ} {reserved : Nat}
    {d stop one jump b c : BitVec 32} {value : W}
    (test : InsAt m pc 19 d stop 0)
    (positive : m.rd64 (slot fp (sx d)) = some value) (nonzero : value ≠ 0)
    (decrement : InsAt m (pc + 16) 4 d d one)
    (unit : m.rd64 (slot fp (sx one)) = some 1)
    (write : m.wr64 (slot fp (sx d)) (value - 1) = some m1)
    (body : Reach L fp lo K pr ⟨pc + 16 + 16, fp⟩ m1 back σ ρ reserved)
    (layout : WIn L fp Ks K) (hprotected : counter < lo ∨ counter ∈ pr)
    (bound : lo ≤ K)
    (location : sx d = BitVec.ofNat 64 counter)
    (edge : InsAt m1 back 18 jump b c) (far : CodeFar back 1 fp K) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨back + sx jump, fp⟩ m' ∧
      EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (value - 1) := by
  have first := Star.one (counter_positive (t := ⟨pc, fp⟩) test positive nonzero)
  have second := Star.one (counter_decrement (t := ⟨pc + 16, fp⟩)
    decrement positive unit write)
  have stored := Runner.Mem.rd64_wr64 write (rd64_some_all positive)
  rw [location] at stored
  obtain ⟨m', rest, _, env, world, _, kept⟩ := Reach.counter_backedge body
    layout hprotected bound stored edge far
  exact ⟨m', first.trans (second.trans rest), env, world, kept⟩

/-- The zero arm reaches the actual emitted exit request with progress code 111.
This does not postulate that a desired stop occurs. -/
theorem counter_budget_stop_code {m : Mem} {pc fp : W} {d jump c : BitVec 32}
    {K scratch : Nat}
    (instruction : InsAt m pc 19 d jump c)
    (zero : m.rd64 (slot fp (sx d)) = some 0)
    (code : CodeAt m (pc + sx jump) (stopC 111 scratch))
    (far : CodeFar (pc + sx jump) 3 fp K) (frame : FrameOK m fp K)
    (room : scratch + 8 ≤ K) (small : K < 2 ^ 31) :
    Stops ⟨pc, fp⟩ m 111 :=
  counter_budget_stop instruction zero (stop_ok code far frame room small (by decide))

/-- Canonical fuel induction at a fixed runtime loop header. `entry` describes
    the concrete counter, code, frame and surrounding program at that header.
    The positive arm simulates just one invariant/body pass (not the loop).
    Continuing passes carry the smaller-fuel entry in their actual runtime result.
    This composition does not by itself discharge those lowering obligations. -/
theorem forever_runtime {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {l : Bool} {reserved : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp pc exit outerLeave outerNext : W} {lo K : Nat} {pr : List Nat}
    (a : D.Annahme)
    (body : World D → Env D Γ → Ausgang (vertragVon D f) true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (entry : Nat → Mem → World D → Env D Γ → Prop)
    (lower : FB ≤ lo)
    (zero : ∀ m σ ρ, entry 0 m σ ρ → Stops ⟨pc, fp⟩ m (hwCode (.fortschritt a)))
    (invalid : ∀ n m σ ρ, entry (n + 1) m σ ρ → (inv σ ρ).2 = false →
      Stops ⟨pc, fp⟩ m (logikCode (D := D) .schleife))
    (pass : ∀ n m σ ρ, entry (n + 1) m σ ρ → (inv σ ρ).2 ≠ false →
      match body (inv σ ρ).1 ρ with
      | .ok σ' ρ' | .next _ σ' ρ' =>
        ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
          EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧ Keeps fp pr m m' ∧ entry n m' σ' ρ'
      | o => Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m pc exit pc o reserved) :
    ∀ n m σ ρ, entry n m σ ρ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
        (foreverLauf (l := l) a body inv n σ ρ) reserved := by
  intro n
  induction n with
  | zero =>
    intro m σ ρ he
    exact zero m σ ρ he
  | succ n ih =>
    intro m σ ρ he
    simp only [foreverLauf]
    by_cases hv : (inv σ ρ).2 = false
    · rw [ite_eq_left hv]
      exact invalid n m σ ρ he hv
    · rw [ite_eq_right hv]
      have hb := pass n m σ ρ he hv
      have again : ∀ σ' ρ',
          (∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
            EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧ Keeps fp pr m m' ∧ entry n m' σ' ρ') →
          Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
            (foreverLauf (l := l) a body inv n σ' ρ') reserved := by
        intro σ' ρ' hr
        obtain ⟨m', run, frame, _, _, keeps, he'⟩ := hr
        exact Sim.prefix lower run frame keeps (ih m' σ' ρ' he')
      generalize body (inv σ ρ).1 ρ = o at hb ⊢
      cases o with
      | ok σ' ρ' => exact again σ' ρ' hb
      | next h σ' ρ' => exact again σ' ρ' hb
      | leave h σ' ρ' => exact hb
      | zurueck | why | logik | hardware => exact hb


/-- Route every actual body outcome using the loop's real control targets.
    Fallthrough executes the emitted backedge; next already targets the header.
    Leave and returns retain the ordinary simulation, including its frame and ABI.
    Counter retention is derived from the body frame, never supplied separately. -/
theorem Sim.counter_dispatch {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp header back exit : W} {lo K Ks counter reserved : Nat} {pr : List Nat}
    {t : T} {m : Mem} {o : Ausgang (vertragVon D f) true Γ}
    {jump b c : BitVec 32} {value : W}
    (body : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m back exit header o reserved)
    (layout : WIn L fp Ks K) (hprotected : counter < lo ∨ counter ∈ pr)
    (bound : lo ≤ K)
    (initial : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value)
    (edge : InsAt m back 18 jump b c) (far : CodeFar back 1 fp K)
    (target : back + sx jump = header) :
    match o with
    | .ok σ' ρ' | .next _ σ' ρ' =>
      ∃ m', Star t m ⟨header, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
        EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧ Keeps fp pr m m' ∧
        m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value
    | o => Sim L P f σ0 ρ0 rp cfp fp lo K pr t m header exit header o reserved := by
  cases o with
  | ok σ' ρ' =>
    obtain ⟨m', run, frame, env, world, keeps, count⟩ :=
      Reach.counter_backedge body layout hprotected bound initial edge far
    exact ⟨m', by simpa only [target] using run, frame, env, world, keeps, count⟩
  | next h σ' ρ' =>
    obtain ⟨m', run, frame, env, world, keeps⟩ := body
    refine ⟨m', run, frame, env, world, keeps, ?_⟩
    rcases hprotected with below | member
    · rw [counter_preserved layout frame below bound]; exact initial
    · rw [keeps counter member]; exact initial
  | leave h σ' ρ' => exact body
  | zurueck | why | logik | hardware => exact body

/-- The actual positive header reconstructs the ordinary source-pass interface.
    Counter storage is above the saved ABI parameters and below relocated locals.
    Outer counters and sentinels are retained by disjoint writes, even when they
    lie above this counter. The fuel equality is natural, without word wrapping. -/
theorem counter_header {D : Deklaration} {L : Lay D} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc rp cfp : W} {K Ks lo reserved counter one n : Nat} {pr : List Nat}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {m : Mem} {code : List II} {stop : Int}
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounter counter one stop ++ code) ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (abi : FB + (D.params f).length ≤ lo) (low : lo ≤ counter)
    (allocated : counter < FB + reserved) (bound : frei Γ reserved ≤ K)
    (unit : one < K)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 (n + 1)))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (fits : n + 1 < 2 ^ 64)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ counter) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 32, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' (pc + 32) fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 n) := by
  have inside : counter < K := by unfold frei at bound; omega
  have sc := sx_nat (d := counter) (by have := pre.small; omega)
  have so := sx_nat (d := one) (by have := pre.small; omega)
  have test := pre.code 0 (by simp [foreverCounter])
  have dec := pre.code 1 (by simp [foreverCounter])
  simp [foreverCounter, ci] at test dec
  obtain ⟨positive, subtract⟩ := counter_fuel_step n fits
  obtain ⟨write, stored, frame⟩ := wr_slot pre.frame inside (BitVec.ofNat 64 n)
  have run1 := Star.one (counter_positive (t := ⟨pc, fp⟩) test
    (by simpa only [ci, sc] using read) positive)
  have run2 := Star.one (counter_decrement (t := ⟨pc + 16, fp⟩) dec
    (by simpa only [ci, sc] using read) (by simpa only [ci, so] using readOne)
    (by simpa only [ci, sc, subtract] using write))
  have allFrame := frame.mono low
  have env := (reserved_write_preserves (L := L) (j := counter - FB) (BitVec.ofNat 64 n).toNat
    pre.frame.room bound (by omega) pre.env).1
  have eq : FB + (counter - FB) = counter := by omega
  rw [eq] at env
  have far := codeFar_right (n := 2) (k := code.length) (by simpa [foreverCounter, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using pre.far)
  refine ⟨_, ?_, agreeW_of allFrame, ?_, surround.agreeW layout (agreeW_of allFrame) (by omega),
    head.agree allFrame pre.frame abi, ?_, ?_, stored⟩
  · simpa [nxt, Nat.reduceMul, show (16 : W) + 16 = 32 by decide, BitVec.add_assoc] using run1.trans run2
  · exact ⟨pre.ctx, pre.small, pre.frame.agree frame,
      (codeAt_right pre.code).agree allFrame far, far, env, trivial, wstab_true _ _⟩
  · exact weltAt_stab layout.lay layout.top m _ world (allFrame.mono (Nat.zero_le _))
  · intro j hj
    exact Mem.rd64_write_far (slot_far pre.frame.room inside (hprotected j hj).1
      (Ne.symm (hprotected j hj).2))

/-- Execute the actual source invariant and then the generically lowered body.
    The read event, callee frame, return ABI and protected slots are inherited
    from `lowE_ok`, `choice_ok` and the explicit child induction contract.
    This is one positive pass, not yet the counter/header integration. -/
theorem forever_source_pass {D : Deklaration} {L : Lay D}
    {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp rp cfp : W} {K Ks lo : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length)
    (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)}
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D f) true Γ Λ Λ)
    {cc cb : List II} {tc tb : Nat}
    (hcc : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (hcb : lowB (reserved := reserved) passes A L lo (cens, tens) pr (exPlus ex 4) body = some (cb, tb))
    (htc : tc ≤ Ks) (htb : tb + cap ≤ Ks) (room : frei Γ reserved + 8 ≤ Ks)
    (hs : 16 * (cc.length + 1 + cb.length + 1 + 3) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    (bodyRuns : BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp
      σ0 ρ0 cens tens pr (exPlus ex 4) body reserved)
    {m : Mem} {pc : W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ reserved)
      (cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)) ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hw : WeltAt m L σ) :
    let code := cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
      [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length))
      (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2)
      (if wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) then
        execBlock O passes R body (σ.lese Λ inv.orte) ρ else .logik .schleife) reserved := by
  have hks := hW.ks
  have htop := lowE_top inv (frei Γ reserved) cc tc hcc
  apply choice_ok (d := frei Γ reserved) (ct := cb) (ce := stopC 104 (frei Γ reserved))
    (Nat.le_refl _) (by omega) (by simpa [stopC, sysC] using hs) hW hlo hlo0 hlo2 hpr
  · intro hpc
    have hpw := PreS.welt hpc hks hw hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, st, a1, w, hr, hen⟩ := lowE_ok (σ.lese Λ inv.orte) (σ.lese Λ inv.orte)
      (fun _ h => h) inv (frei Γ reserved) cc tc hcc (by omega) m pc ρ hpw
    exact ⟨m1, st, Agree.widen a1 hks, w, hr, hen⟩
  · intro _ m' pc' hp' _ hu' hk' hw'
    exact bodyRuns cb tb hcb htb (by omega) hW
      m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr
  · intro _ m' pc' hp' _ _ _ _
    exact stop_ok hp'.code hp'.far hp'.frame (by omega) hp'.small (by simp [logikCode])
  · exact hp
  · exact hu
  · exact hk
  · exact hw

/-- Compose the emitted counter header with the actual generic invariant/body lowering
    and induct on semantic fuel, retaining the concrete entry interface. -/
theorem forever_counter_loop {D : Deklaration} {L : Lay D}
    {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp rp cfp : W} {K Ks lo : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length)
    (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {counter one : Nat}
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)}
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D f) true Γ Λ Λ)
    {cc cb : List II} {tc tb : Nat}
    (hcc : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (hcb : lowB (reserved := reserved) passes A L lo (cens, tens) (counter :: one :: pr) (exPlus ex 4) body = some (cb, tb))
    (htc : tc ≤ Ks) (htb : tb + cap ≤ Ks) (room : frei Γ reserved + 8 ≤ Ks)
    (hs : 16 * (cc.length + 1 + cb.length + 1 + 3) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ counter :: one :: pr, j < frei Γ reserved)
    (bodyRuns : BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp
      σ0 ρ0 cens tens (counter :: one :: pr) (exPlus ex 4) body reserved)

    {pc back exit : W} {stop : Int} {jump b c : BitVec 32}
    (backAt : pc + 32 + BitVec.ofNat 64
      (16 * (cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)).length) = back)
    (leaveAt : back + BitVec.ofInt 64 ex.1 = exit)
    (nextAt : back + BitVec.ofInt 64 ex.2 = pc)
    (jumpAt : back + sx jump = pc)
    (low : lo ≤ counter) (allocated : counter < FB + reserved)
    (oneBound : one < K) (distinct : one ≠ counter)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ counter)
    (backFar : CodeFar back 1 fp K)
    (stopFar : CodeFar (pc + sx (BitVec.ofInt 32 stop)) 3 fp K)
    (stopRoom : frei Γ reserved + 8 ≤ K)
    {l : Bool} (a : D.Annahme)
    {m : Mem} {σ : World D} {ρ : Env D Γ} {budget : Nat}
    (fits : budget < 2 ^ 64)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounter counter one stop ++
        (cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
          [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))) ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (edge : InsAt m back 18 jump b c)
    (stopCode : CodeAt m (pc + sx (BitVec.ofInt 32 stop)) (stopC 111 (frei Γ reserved))) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit exit pc
      (foreverLauf (l := l) a (execBlock O passes R body)
        (fun σ ρ => (σ.lese Λ inv.orte,
          wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) budget σ ρ) reserved := by
  have bound : frei Γ reserved ≤ K := by omega
  have inside : counter < K := by unfold frei at bound; omega
  induction budget generalizing m σ ρ with
  | zero =>
    have test := pre.code 0 (by simp [foreverCounter])
    simp [foreverCounter, ci] at test
    have sc := sx_nat (d := counter) (by have := pre.small; omega)
    exact counter_budget_stop_code test (by simpa [sc] using read)
      stopCode stopFar pre.frame stopRoom pre.small
  | succ n ih =>
    obtain ⟨m1, run, frame, hp, hu, hk, hw, keeps, count⟩ :=
      counter_header hW pre surround head world (by omega) low allocated
        (by omega) oneBound read readOne fits (by
          intro j hj
          rcases List.mem_cons.mp hj with h | h
          · subst j; exact ⟨oneBound, distinct⟩
          · exact hprotected j h)
    have pass := forever_source_pass (O := O) hS hA hlo0 hens inv body hcc hcb htc htb room hs
      hW hlo hlo2 hpr bodyRuns hp hu hk hw
    simp only [] at pass
    rw [backAt, leaveAt, nextAt] at pass
    have edge1 : InsAt m1 back 18 jump b c := by
      have hc : CodeAt m back [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
        intro k hk
        have : k = 0 := by simpa using hk
        subst k
        simpa [II.f] using edge
      have h := (codeAt_agreeWIn hW frame hc backFar) 0 (by simp)
      simpa [II.f] using h
    have again : ∀ σ' ρ',
        (∃ m', Star ⟨pc + 32, fp⟩ m1 ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m1 m' ∧
          EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧
          Keeps fp (counter :: one :: pr) m1 m' ∧
          m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 n)) →
        Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit exit pc
          (foreverLauf (l := l) a (execBlock O passes R body)
            (fun σ ρ => (σ.lese Λ inv.orte,
              wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) n σ' ρ') reserved := by
      intro σ' ρ' result
      obtain ⟨m2, run2, frame2, env2, world2, keeps2, count2⟩ := result
      have total := frame.trans frame2
      have kp : Keeps fp pr m m2 := fun j hj => (keeps2 j (by simp [hj])).trans (keeps j (by simp [hj]))
      have pre2 : PreS L m2 pc fp K (frei Γ reserved) _ ρ' reserved :=
        ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame total,
          codeAt_agreeWIn hW total pre.code pre.far, pre.far, env2, trivial, wstab_true _ _⟩
      have edge2 : InsAt m2 back 18 jump b c := by
        have hc : CodeAt m1 back [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
          intro k hk
          have : k = 0 := by simpa using hk
          subst k
          simpa [II.f] using edge1
        have h := (codeAt_agreeWIn hW frame2 hc backFar) 0 (by simp)
        simpa [II.f] using h
      have one2 : m2.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1 := by
        rw [keeps2 one (by simp), keeps one (by simp)]
        exact readOne
      exact Sim.prefix hlo (run.trans run2) total kp
        (ih (by omega) pre2 (surround.agreeW hW total (by omega))
          (head.agreeW hW total (by omega)) world2 count2 one2 edge2
          (codeAt_agreeWIn hW total stopCode stopFar))
    simp only [foreverLauf]
    split
    · rename_i hv
      simp [hv] at pass
      exact Stops.prefix run pass
    · rename_i hv
      have ht : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
        cases h : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) <;> simp_all
      simp only [ht, ite_true] at pass
      have dispatch := pass.counter_dispatch hW (Or.inr (by simp)) (by omega)
        count edge1 backFar jumpAt
      generalize execBlock O passes R body (σ.lese Λ inv.orte) ρ = o at pass dispatch ⊢
      cases o with
      | ok σ' ρ' => exact again σ' ρ' dispatch
      | next h σ' ρ' => exact again σ' ρ' dispatch
      | leave h σ' ρ' =>
        exact Reach.prefix run frame (fun j hj => keeps j (by simp [hj]))
          (by obtain ⟨m', r, f, e, w, k⟩ := dispatch
              exact ⟨m', r, f, e, w, fun j hj => k j (by simp [hj])⟩)
      | zurueck | why | logik | hardware =>
        exact Sim.prefix hlo run frame (fun j hj => keeps j (by simp [hj])) dispatch

end Gabbro.Stage0.Senke
