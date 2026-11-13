/- Runtime loop edges consume the actual block simulation and its world-aware frame. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil1a

public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counters.Counter
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil3
public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Anweisung.Verzweigung
public import Stage0.Senke.Anweisung.Faelle.Kontext

@[expose] public section



namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR

variable [Kern]

/-- Reconstruct the complete body-entry interface after an actual backedge.
    Code and callee availability follow from the simulated world-aware frame;
    the new environment and world come from execution, not preservation claims.
    The reservation retains the counter and any immutable control slots in `pr`. -/
theorem Reach.counter_reentry {D : Deklaration} {L : Lay D} {H : List D.Lock} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc back rp cfp : W} {lo K Ks counter reserved : Nat} {pr : List Nat}
    {m : Mem} {σ' : World D} {ρ ρ' : Env D Γ}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {code : List II}
    {jump b c : BitVec 32} {value : W}
    (body : Reach L fp lo K pr ⟨pc, fp⟩ m back σ' ρ' reserved)
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surround : Umf L A C dv m fp Ks K H)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hprotected : counter < lo ∨ counter ∈ pr) (bound : lo ≤ K)
    (abi : (functionFrame P f).internalResult ≤ lo)
    (initial : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value)
    (edge : InsAt m back 18 jump b c) (far : CodeFar back 1 fp K)
    (target : back + sx jump = pc) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' pc fp K (frei Γ reserved) code ρ' reserved ∧
      Umf L A C dv m' fp Ks K H ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ' ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some value := by
  have protectedPrefix := functionFrame_prefix P f
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
    {f : D.Fn} {Γ : Ctx} {l : Bool} {reserved : Nat} {sc : List D.Lock}
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
      | o => Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m pc exit pc o reserved sc) :
    ∀ n m σ ρ, entry n m σ ρ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
        (foreverLauf (l := l) a body inv n σ ρ) reserved sc := by
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
            (foreverLauf (l := l) a body inv n σ' ρ') reserved sc := by
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
    {f : D.Fn} {Γ : Ctx} {σ0 : World D} {ρ0 : Env D (D.params f)} {sc : List D.Lock}
    {rp cfp fp header back exit : W} {lo K Ks counter reserved : Nat} {pr : List Nat}
    {t : T} {m : Mem} {o : Ausgang (vertragVon D f) true Γ}
    {jump b c : BitVec 32} {value : W}
    (body : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m back exit header o reserved sc)
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
    | o => Sim L P f σ0 ρ0 rp cfp fp lo K pr t m header exit header o reserved sc := by
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
theorem counter_header {D : Deklaration} {L : Lay D} {H : List D.Lock} {P : Programm D}
    {f : D.Fn} {Γ : Ctx} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {fp pc rp cfp : W} {K Ks lo reserved counter one n : Nat} {pr : List Nat}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {m : Mem} {code : List II} {stop : Int}
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounter counter one stop ++ code) ρ reserved)
    (surround : Umf L A C dv m fp Ks K H)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (abi : (functionFrame P f).internalResult ≤ lo) (low : lo ≤ counter)
    (allocated : counter < FB + reserved) (bound : frei Γ reserved ≤ K)
    (unit : one < K)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 (n + 1)))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (fits : n + 1 < 2 ^ 64)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ counter) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + 32, fp⟩ m' ∧ AgreeW L fp lo K m m' ∧
      PreS L m' (pc + 32) fp K (frei Γ reserved) code ρ reserved ∧
      Umf L A C dv m' fp Ks K H ∧ Kopf L f m' fp K rp cfp ρ0 P σ0 ∧
      WeltAt m' L σ ∧ Keeps fp pr m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 n) := by
  have protectedPrefix := functionFrame_prefix P f
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

end Gabbro.Stage0.Senke
