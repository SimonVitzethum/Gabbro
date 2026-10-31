/- Source-bound instruction costs for actual statement lowering. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted
import Stage0.Senke.Anweisung.Faelle.Schleifen.RelocateProbe
import Stage0.Senke.Ausdruck.Old.Proben
import Stage0.Senke.Funktion
import Stage0.Senke.Anweisung.Hilfe
import Stage0.Senke.Ausdruck.FnptrAufrufProben

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern]
variable {D : Deklaration} {L : Lay D} {reserved : Nat}
set_option maxHeartbeats 2000000

/-- Argument costs follow the actual right-to-left lowering. Each expression
    has its own source certificate; no bound on an argument execution is assumed. -/
inductive ArgsCost (L : Lay D) (reserved F : Nat) :
    {Γ : Ctx} → {Λ : List (Res D)} → {ts : List Ty} →
      Args D Γ Λ ts → World D → World D → Env D Γ → Nat → Type
  | nil {Γ Λ σ₀ σ} {ρ : Env D Γ} :
      ArgsCost L reserved F (.nil (Γ := Γ) (Λ := Λ)) σ₀ σ ρ 0
  | cons {Γ Λ τ ts} {e : Expr D Γ Λ τ} {rest : Args D Γ Λ ts}
      {σ₀ σ : World D} {ρ : Env D Γ} {nr ne : Nat}
      (tail : ArgsCost L reserved F rest σ₀ σ ρ nr)
      (head : ExprCost L reserved e (F + FB + ts.length) ne
        (Enc L τ (eval σ₀ e σ ρ))) :
      ArgsCost L reserved F (.cons e rest) σ₀ σ ρ (nr + ne)

/-- Count actual argument instructions and retain the callee parameter frame.
    Evaluation order, scratch preservation and world stability are inherited
    from the existing expression contract and the canonical `lowA`. -/
theorem ArgsCost.sound {Γ : Ctx} {Λ : List (Res D)} {ts : List Ty}
    {args : Args D Γ Λ ts} {σ₀ σ : World D} {ρ : Env D Γ} {n F : Nat}
    (certificate : ArgsCost L reserved F args σ₀ σ ρ n)
    {c : List II} {top K : Nat} {m : Mem} {pc fp : W} {W : Mem → Prop}
    (lower : lowA L args (F + FB) reserved = some (c, top))
    (fits : top ≤ K) (room : F + FB + ts.length ≤ K)
    (pre : Pre L m pc fp K (F + FB) c ρ W reserved) :
    ∃ m', Counted n ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
      Agree fp (F + FB) K m m' ∧
      EnvAt L m' (slot fp (BitVec.ofNat 64 F)) (evalArgs σ₀ args σ ρ) := by
  induction certificate generalizing c top m pc with
  | nil =>
    simp only [lowA, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨rfl, rfl⟩ := lower
    exact ⟨m, by simpa using Counted.refl ⟨pc, fp⟩ m,
      Agree.refl _ _ _ _, fun _ x => nomatch x⟩
  | @cons τ ts e rest σ₀ σ ρ nr ne tail head ih =>
    simp only [lowA, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cr, tr⟩, hr, ⟨ce, te⟩, he, hc⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    simp only [List.length_cons] at room
    obtain ⟨m1, s1, a1, e1⟩ := ih hr (by omega) (by omega) pre.left
    have hp1 := (pre.next a1 (Nat.le_refl _) (by omega)).up
      (d' := F + FB + ts.length) (by omega)
    obtain ⟨m2, s2, a2, w, hw, hen⟩ := head.sound he (by omega) hp1
    refine ⟨m2, s1.trans (by rw [pc_add1]; exact s2),
      a1.trans (a2.mono (by omega)), ?_⟩
    simp only [evalArgs]
    have hfr : F + frei ts = F + FB + ts.length := by simp only [frei]; omega
    refine envAt_cons (fp := slot fp (BitVec.ofNat 64 F)) ?_
      (by rw [slot_slot, hfr]; exact hw) hen
    intro τ' y
    obtain ⟨w', hw', he'⟩ := e1 τ' y
    refine ⟨w', ?_, he'⟩
    have := vslot_lt (reserved := 0) y
    rw [slot_slot] at hw' ⊢
    rw [agree_rd_low a2 hp1.frame.room
      (by simp only [frei] at this; omega) (by omega)]
    exact hw'

theorem st_step_counted {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {va vb : Runner.W} {m' : Runner.Mem}
    (hc : CodeAt m pc [ci 16 ((s + 1 : Nat) : Int) s 0]) (hK : s + 1 < K) (hK2 : K < 2 ^ 31)
    (ha : m.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some va) (hb : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some vb)
    (hw : m.wr64 va vb = some m') : Counted 1 ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m' := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine counted_ins hc (by simp [ci]) ?_
  simp only [ci]
  exact run_st (t := ⟨pc, fp⟩) hi (by rw [sx_nat (by omega)]; exact ha) (by rw [sx_nat (by omega)]; exact hb) hw

/-- The store of a cell at address `a`: the value code `ce` into `s`, the address code `ca` into `s + 1`, `st`. -/
theorem store_counted {m : Runner.Mem} {pc fp : Runner.W} {K Ks a d ne na : Nat} {Γ : Ctx} {ρ : Env D Γ} {L : Lay D}
    {σ σ' : World D} {ce ca : List II} {Pe : Runner.W → Prop}
    (hp : PreS L m pc fp K (d) (ce ++ ca ++ [stC (d)]) ρ reserved)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) (htop : d + 2 ≤ Ks)
    (hE : ∀ m pc, Pre L m pc fp Ks (d) ce ρ (fun m => WeltAt m L σ) reserved → CountedOk ne m pc fp Ks (d) ce Pe)
    (hA : ∀ m pc, Pre L m pc fp Ks (d + 1) ca ρ (fun m => WeltAt m L σ) reserved →
      CountedOk na m pc fp Ks (d + 1) ca (· = BitVec.ofNat 64 a))
    (ha : L.lo ≤ a ∧ a + 8 ≤ L.hi)
    (hnew : ∀ m w, WeltAt m L σ → Pe w → WeltAt (write m (BitVec.ofNat 64 a) 8 w.toNat) L σ') :
    ∃ m', Counted (ne + (na + 1)) ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (ce ++ ca ++ [stC (d)]).length), fp⟩ m' ∧
      AgreeW L fp (d) K m m' ∧ EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ' := by
  have hks := hW.ks
  have hwl := hW.lo
  have htp := hW.top
  have hl3 := hW.lay.2.2
  have hsm := hp.small
  have hq : PreS L m pc fp K (d) (ce ++ (ca ++ [stC (d)])) ρ reserved := by
    simpa [List.append_assoc] using hp
  -- the value
  have hpw := PreS.welt hq.left hks hWa hW.lay (by omega)
  obtain ⟨m1, s1, a1s, w, hw, hpe⟩ := hE m pc hpw
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have a1 := Agree.widen a1s hks
  have hq1 := hq.next a1 (Nat.le_refl _) (by omega)
  -- the address
  have hpa := PreS.welt (hq1.left.up (d' := d + 1) (by omega)) hks hWa1 hW.lay (by omega)
  obtain ⟨m2, s2, a2s, adr, hadr, hae⟩ := hA m1 _ hpa
  have a2 := Agree.widen a2s hks
  have hF2 := hq1.frame.agree a2
  have hw2 : m2.rd64 (slot fp (BitVec.ofNat 64 (d))) = some w := by
    rw [agree_rd_low a2s (frameOK_sub hq1.frame hks).room (Nat.lt_succ_self _) (by omega)]; exact hw
  have hWa2 : WeltAt m2 L σ := hpa.wstab m1 m2 hWa1 (a2s.mono (Nat.zero_le _))
  have hq2 := hq1.next (a := ca) (a2.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  -- the store
  have hroom := hF2.room
  have hwr := hWa2.2.2.word ha.1 ha.2 hl3
  subst hae
  have s3 := st_step_counted hq2.code (by omega) hsm hadr hw2 (wr64_some hwr)
  have a3 : AgreeW L fp (d) K m2 (write m2 (BitVec.ofNat 64 a) 8 w.toNat) :=
    agreeW_write_welt ha.1 ha.2 hl3 _
  have a13 : AgreeW L fp (d) K m (write m2 (BitVec.ofNat 64 a) 8 w.toNat) :=
    (agreeW_of (a1.trans (a2.mono (Nat.le_succ _)))).trans a3
  refine ⟨_, s1.trans (s2.trans ?_), a13, envAt_agreeW hp.env a13 htp hp.frame.room hp.ctx (by omega),
    hnew m2 w hWa2 hpe⟩
  have e : pc + BitVec.ofNat 64 (16 * (ce ++ ca ++ [stC (d)]).length) =
      pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * 1) := by
    simp only [List.length_append, List.length_singleton, pc_add]
  rw [e]; exact s3


/-- The emitted variable move completes one instruction. -/
theorem mov_to_counted {m : Mem} {pc fp : W} {K j s : Nat} {w : W}
    (hc : CodeAt m pc [ci 2 j s 0]) (hF : FrameOK m fp K)
    (hj : j < K) (hs : s < K) (hK : K < 2 ^ 31)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci 2 j s 0].length), fp⟩
      (write m (slot fp (BitVec.ofNat 64 j)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply counted_ins hc (by simp [ci])
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 hv ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr j hj))

/-- A successful emitted guard executes the conditional branch and the jump
    across the failure block. Its five encoded instructions cost two steps. -/
theorem guard_pass_counted {m : Mem} {pc fp : W} {a c s : Nat} {v : W}
    (hc : CodeAt m pc (guardC a c s)) (ha : a < 2 ^ 31)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some v) (hne : v ≠ 0) :
    Counted 2 ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (guardC a c s).length), fp⟩ m := by
  have hd : sx (II.f (a : Int)) = BitVec.ofNat 64 a := sx_nat (by omega)
  have rb := run_brz_ne (t := ⟨pc, fp⟩) (guard_brz hc) (by rw [hd]; exact hv) hne
  have first := counted_ins (fp := fp) (m' := m)
    (codeAt_left (a := [ci 19 a 32 0]) hc) (by simp [ci]) (by simp only [ci]; exact rb)
  have hj := (codeAt_right (a := [ci 19 a 32 0]) hc) 0 (by simp [guardC])
  simp only [guardC, ci, List.cons_append, List.getElem_cons_zero,
    Nat.mul_zero, BitVec.add_zero] at hj
  have jump := run_step (t := ⟨_, fp⟩) hj (by decide) (run_jmp (t := ⟨_, fp⟩) hj)
  have hl : sx (II.f 64) = BitVec.ofNat 64 64 := sx_nat (d := 64) (by omega)
  rw [hl] at jump
  have rest := Counted.next jump (Counted.refl _ _)
  have result := first.trans rest
  simpa [guardC, stopC, sysC, addr_norm] using result

/-- Execute a recursively certified true source condition and its real guard.
    This is the successful requires phase; its bound comes from the expression
    certificate and two control instructions, not from code length. -/
theorem ExprCost.guard {Γ : Ctx} {Λ : List (Res D)}
    {e : Expr D Γ Λ .bool} {d n top K failure : Nat} {cq : List II}
    {m : Mem} {pc fp : W} {ρ : Env D Γ} {W : Mem → Prop}
    (certificate : ExprCost L reserved e d n (· = 1))
    (lower : lowE L (reserved := reserved) e d = some (cq, top))
    (fits : top ≤ K)
    (pre : Pre L m pc fp K d (cq ++ guardC d failure d) ρ W reserved) :
    ∃ m', Counted (n + 2) ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (cq ++ guardC d failure d).length), fp⟩ m' ∧
      Agree fp d K m m' ∧ EnvAt L m' fp ρ reserved ∧ W m' := by
  have room := lowE_top e d cq top lower
  obtain ⟨m', run, agree, w, read, value⟩ := certificate.sound lower fits pre.left
  have tail := pre.next agree (Nat.le_refl _) (by omega)
  subst w
  have guard := guard_pass_counted tail.code (by have := pre.small; omega) read (by decide)
  refine ⟨m', ?_, agree, tail.env, tail.welt⟩
  simpa only [List.length_append, pc_add] using run.trans guard

namespace RequiresCostProbe

def code : List II := [ci 1 4 1 0] ++ guardC 4 101 4

def memory : Mem := {
  b := fun a => ((code.flatMap encII)[a.toNat]?).getD 0
  rd := fun _ => true
  wr := fun _ => true }

/-- A loaded true requires expression executes one constant and two guard
    instructions, preserving the empty lexical environment and world predicate. -/
theorem requires_counted_zeuge {D : Deklaration} (L : Lay D) :
    ∃ m', Counted 3 ⟨0, 4096⟩ memory ⟨96, 4096⟩ m' ∧
      Agree 4096 4 32 memory m' ∧
      EnvAt L m' 4096 (Env.nil : Env D []) 0 ∧ True := by
  have loaded : CodeAt memory 0 code := by
    have h : ∀ k : Fin code.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 code[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f code[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f code[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f code[k.val].c) := by
      apply FnptrProben.allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS L memory 0 4096 32 4 code (Env.nil : Env D []) 0 :=
    ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      loaded, by unfold CodeFar; decide, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  exact ExprCost.guard (e := Expr.tru (Λ := [])) (.truth) rfl (by decide) pre

end RequiresCostProbe

/-- Actual Runner execution, exact destination frame, and all relocated words.
    No disjointness premise between the source and destination ranges is needed. -/
theorem relocate_counted {m : Mem} {pc fp : W} {K base shift n : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (bound : base + shift + n ≤ K)
    (code : CodeAt m pc (relocateC base shift n))
    (far : CodeFar pc n fp K) :
    ∃ m', Counted n ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), fp⟩ m' ∧
      Agree fp (base + shift) (base + shift + n) m m' ∧
      ∀ i, i < n → m'.rd64 (slot fp (BitVec.ofNat 64 (base + shift + i))) =
        m.rd64 (slot fp (BitVec.ofNat 64 (base + i))) := by
  induction n generalizing m pc with
  | zero =>
    exact ⟨m, by simpa using (Counted.refl ⟨pc, fp⟩ m), .refl _ _ _ _, by omega⟩
  | succ n ih =>
    let dst := base + shift + n
    let src := base + n
    let v := BitVec.ofNat 64 (le m (slot fp (BitVec.ofNat 64 src)) 8)
    have read : m.rd64 (slot fp (BitVec.ofNat 64 src)) = some v := by
      simp only [Mem.rd64, frame.rd src (by dsimp [src]; omega), ↓reduceIte]
      rfl
    let m1 := write m (slot fp (BitVec.ofNat 64 dst)) 8 v.toNat
    have writeFrame : Agree fp dst K m m1 := agree_write frame.room (by omega) (by dsimp [dst]; omega) _
    have step := mov_to_counted (codeAt_left code) frame (show dst < K by dsimp [dst]; omega)
      (show src < K by dsimp [src]; omega) small read
    have tailCode : CodeAt m1 (pc + 16) (relocateC base shift n) := by
      exact (codeAt_right code).agree writeFrame (by simpa [relocateC_length, Nat.add_comm] using (codeFar_right (n := 1) (k := n) (by simpa [Nat.add_comm] using far)))
    obtain ⟨m2, rest, tailFrame, moved⟩ := ih (frame.agree writeFrame) (by omega)
      tailCode (by simpa [relocateC_length, Nat.add_comm] using (codeFar_right (n := 1) (k := n) (by simpa [Nat.add_comm] using far)))
    refine ⟨m2, ?_, ?_, ?_⟩
    · have run := step.trans rest
      have eq : pc + 16 + BitVec.ofNat 64 (16 * n) = pc + BitVec.ofNat 64 (16 * (n + 1)) := by
        simpa [Nat.add_comm] using (pc_add pc 1 n)
      rw [eq] at run
      simpa [Nat.add_comm] using run
    · have first : Agree fp (base + shift) (base + shift + (n + 1)) m m1 :=
        agree_write (by have := frame.room; omega) (by dsimp [dst]; omega) (by dsimp [dst]; omega) _
      exact first.trans ⟨tailFrame.rd, tailFrame.wr, fun x hx => tailFrame.b x (by
        unfold inSlots at *; omega)⟩
    · intro i hi
      by_cases top : i = n
      · subst i
        rw [agree_rd_high tailFrame frame.room (by omega) (by omega)]
        rw [read]
        exact rd64_write_same (frame.rd dst (by dsimp [dst]; omega))
      · rw [moved i (by omega)]
        rw [Mem.rd64_write_far (slot_far frame.room (show dst < K by dsimp [dst]; omega)
          (show base + i < K by omega) (by dsimp [dst]; omega))]

/-- Relocate the complete lexical environment, parameters and locals together. -/
theorem relocate_env_counted {D : Deklaration} {L : Lay D} {Γ : Ctx}
    {ρ : Env D Γ} {m : Mem} {pc fp : W} {K reserved extra : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (bound : frei Γ (reserved + extra) ≤ K)
    (env : EnvAt L m fp ρ reserved)
    (code : CodeAt m pc (relocateC (FB + reserved) extra Γ.length))
    (far : CodeFar pc Γ.length fp K) :
    ∃ m', Counted Γ.length ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * Γ.length), fp⟩ m' ∧
      Agree fp (FB + reserved + extra) (frei Γ (reserved + extra)) m m' ∧
      EnvAt L m' fp ρ (reserved + extra) := by
  obtain ⟨m', run, writes, moved⟩ := relocate_counted frame small
    (show FB + reserved + extra + Γ.length ≤ K by unfold frei at bound; omega) code far
  refine ⟨m', run, ?_, ?_⟩
  · simpa [frei, Nat.add_assoc] using writes
  · intro τ x
    obtain ⟨w, read, enc⟩ := env τ x
    have ix := idx_lt x
    have h := moved (Γ.length - 1 - Var.idx x) (by omega)
    refine ⟨w, ?_, enc⟩
    simpa [vslot, Nat.add_assoc] using h.trans read

namespace RelocateProbe

/-- The exact count holds on the existing loaded, overlapping six-word fixture. -/
theorem relocate_counted_zeuge :
    ∃ m', Counted 6 ⟨0, 4096⟩ memory ⟨96, 4096⟩ m' ∧
      Agree 4096 8 14 memory m' ∧
      ∀ i, i < 6 → m'.rd64 (slot 4096 (BitVec.ofNat 64 (8 + i))) =
        memory.rd64 (slot 4096 (BitVec.ofNat 64 (4 + i))) := by
  exact relocate_counted frame (by decide) (by decide) code_at
    (by unfold CodeFar; decide)

/-- Parameters and locals retain their values with the same exact count. -/
theorem relocate_env_counted_zeuge {D : Deklaration} (L : Lay D) :
    ∃ m', Counted 6 ⟨0, 4096⟩ memory ⟨96, 4096⟩ m' ∧
      Agree 4096 8 14 memory m' ∧ EnvAt L m' 4096 env 4 := by
  exact relocate_env_counted frame (by decide) (by decide) (env_at L) code_at
    (by unfold CodeFar; decide)

end RelocateProbe

/-- The successful suffix emitted by `retC` takes exactly three S0IR
    instructions: check the ensures flag, copy the result to ABI slot 2,
    restore the caller PC and frame. The flag is a checked memory premise;
    this lemma does not establish execution of the preceding ensures code. -/
theorem returnTail_counted {m : Mem} {pc fp rp cfp w : W} {K lo : Nat}
    (code : CodeAt m pc
      [ci 19 ((lo + 1 : Nat) : Int) 48 0, ci 2 2 lo 0, ci 21 0 0 0])
    (far : CodeFar pc 3 fp K) (frame : FrameOK m fp K)
    (small : K < 2 ^ 31) (abi : 2 < lo) (room : lo + 1 < K)
    (flag : m.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 1)
    (value : m.rd64 (slot fp (BitVec.ofNat 64 lo)) = some w)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp) :
    ∃ m', Counted 3 ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
      Agree fp 2 K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 1 := by
  have branch := code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at branch
  have stepBranch : Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m :=
    .next (run_step branch (by decide)
      (run_brz_ne branch (by rw [sx_nat (by omega)]; exact flag) (by decide))) (.refl _ _)
  have tail := codeAt_right (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0]) code
  have moved := mov_to_counted (codeAt_left tail) frame (j := 2) (s := lo)
    (by omega) (by omega) small value
  let m' := write m (slot fp (BitVec.ofNat 64 2)) 8 w.toNat
  have agree : Agree fp 2 K m m' := agree_write frame.room (by omega) (by omega) _
  have farRet : CodeFar (pc + 16 + 16) 1 fp K := by
    simpa using codeFar_tail (a := [ci 2 2 lo 0])
      (codeFar_tail (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0])
        (b := [ci 2 2 lo 0, ci 21 0 0 0]) far)
  have retBefore : CodeAt m (pc + 16 + 16) [ci 21 0 0 0] := by
    simpa using codeAt_right (a := [ci 2 2 lo 0]) tail
  have retCode := retBefore.agree agree farRet
  have ret := retCode 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ret
  have rpc : m'.rd64 fp = some rp := by
    have h := agree_rd_low (i := 0) agree frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedPC)
  have rfp : m'.rd64 (fp + 8) = some cfp := by
    have h := agree_rd_low (i := 1) agree frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedFP)
  have leave : Counted 1 ⟨pc + 16 + 16, fp⟩ m' ⟨rp, cfp⟩ m' :=
    .next (run_step ret (by decide) (run_ret rpc rfp)) (.refl _ _)
  refine ⟨m', ?_, agree, rd_same frame (by omega) w, ?_⟩
  · exact (stepBranch.trans (by simpa using moved)).trans leave
  · change (write m (slot fp (BitVec.ofNat 64 2)) 8 w.toNat).rd64 _ = _
    rw [rd_other frame.room (by omega) (by omega) (by omega)]
    exact flag

/-- The four actual call-tail instructions establish the callee ABI, parameter
    frame and decremented depth together. No callee execution is assumed. -/
theorem callTail_counted {indirect : Bool} {A : D.Fn → Nat} {C : D.Fn → List II}
    {dv : Runner.W} {m : Mem} {pc fp : W} {K Ks F : Nat} {f : D.Fn}
    {σ : World D} {ρa : Env D (D.params f)}
    (hc : CodeAt m pc (callTail A f F indirect)) (hcf : CodeFar pc 4 fp K)
    (hF : FrameOK m fp K) (hK : K < 2 ^ 31)
    (hFB : FB ≤ F) (hT : F + FB + (D.params f).length + 1 ≤ Ks)
    (hA : A f < 2 ^ 31) (hP : PCode m A C fp K)
    (hdv : m.rd64 (slot fp (BitVec.ofNat 64 2)) = some (dv + 1))
    (hE : EnvAt L m (slot fp (BitVec.ofNat 64 F)) ρa)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) (hy : SyncOK m L fp Ks)
    (htarget : indirect = true → m.rd64 (slot fp (BitVec.ofNat 64 F)) =
      some (BitVec.ofNat 64 (A f)) := by simp) :
    ∃ m', Counted 4 ⟨pc, fp⟩ m
        ⟨BitVec.ofNat 64 (A f), slot fp (BitVec.ofNat 64 F)⟩ m' ∧
      Agree fp F K m m' ∧
      FrameOK m' (slot fp (BitVec.ofNat 64 F)) (K - F) ∧
      PCode m' A C (slot fp (BitVec.ofNat 64 F)) (K - F) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 F)) = some (pc + 64) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 F) + 8) = some fp ∧
      m'.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 2)) = some dv ∧
      EnvAt L m' (slot fp (BitVec.ofNat 64 F)) ρa ∧ WeltAt m' L σ ∧
      SyncOK m' L (slot fp (BitVec.ofNat 64 F)) (Ks - F) := by
  have hroom := hF.room
  have hlt := hF.lt
  have hFB3 : FB = 4 := rfl
  have hks := hW.ks
  have hroomS : fp.toNat + 8 * Ks ≤ 2 ^ 64 := by omega
  -- the four instructions, read where they lie
  have far : ∀ k, k < 4 → (pc + BitVec.ofNat 64 (16 * k)).toNat + 16 ≤ 2 ^ 64 ∧
      ((pc + BitVec.ofNat 64 (16 * k)).toNat + 16 ≤ fp.toNat ∨
        fp.toNat + 8 * K ≤ (pc + BitVec.ofNat 64 (16 * k)).toNat) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hcf
    have := pc.isLt
    have hx : (pc + BitVec.ofNat 64 (16 * k)).toNat = pc.toNat + 16 * k := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [hx]; omega
  have i0 := hc 0 (by simp [callTail, callTailN])
  have i1 := hc 1 (by simp [callTail, callTailN])
  have i2 := hc 2 (by simp [callTail, callTailN])
  have i3 := hc 3 (by simp [callTail, callTailN])
  simp only [callTail, callTailN, ci, List.getElem_cons_zero, List.getElem_cons_succ] at i0 i1 i2 i3
  -- the writes
  let T := F + FB + (D.params f).length
  have hsT : sx (II.f (T : Int)) = BitVec.ofNat 64 T := sx_nat (by omega)
  have hs2 : sx (II.f ((F + 2 : Nat) : Int)) = BitVec.ofNat 64 (F + 2) := sx_nat (by omega)
  have hsF : sx (II.f (F : Int)) = BitVec.ofNat 64 F := sx_nat (by omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 T)) 8 (BitVec.ofInt 64 1).toNat
  have a1s : Agree fp F Ks m m1 := agree_write hroomS (by omega) (by omega) _
  have a1 : Agree fp F K m m1 := Agree.widen a1s hks
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (F + 2))) 8 dv.toNat
  have a2s : Agree fp F Ks m1 m2 := agree_write hroomS (by omega) (by omega) _
  have a2 : Agree fp F K m1 m2 := Agree.widen a2s hks
  let m3 := write m2 (slot fp (BitVec.ofNat 64 T)) 8 (BitVec.ofInt 64 (A f)).toNat
  have a3s : Agree fp F Ks m2 m3 := agree_write hroomS (by omega) (by omega) _
  have a3 : Agree fp F K m2 m3 := Agree.widen a3s hks
  let m4 := write m3 (slot fp (BitVec.ofNat 64 F)) 8 (pc + BitVec.ofNat 64 (16 * 3) + 16).toNat
  have a4s : Agree fp F Ks m3 m4 := agree_write hroomS (by omega) (by omega) _
  have a4 : Agree fp F K m3 m4 := Agree.widen a4s hks
  let m5 := write m4 (slot fp (BitVec.ofNat 64 (F + 1))) 8 fp.toNat
  have a5s : Agree fp F Ks m4 m5 := agree_write hroomS (by omega) (by omega) _
  have a5 : Agree fp F K m4 m5 := Agree.widen a5s hks
  have hF1 := hF.agree a1
  have hF2 := hF1.agree a2
  have hF3 := hF2.agree a3
  have hF4 := hF3.agree a4
  have a15 : Agree fp F K m m5 := a1.trans (a2.trans (a3.trans (a4.trans a5)))
  have hF5 := hF4.agree a5
  -- the instructions in the memories they run in
  have j1 := i1.agree a1 (far 1 (by decide))
  have j2 := i2.agree (a1.trans a2) (far 2 (by decide))
  have j3 := i3.agree (a1.trans (a2.trans a3)) (far 3 (by decide))
  have e16 : ∀ k : Nat, pc + BitVec.ofNat 64 (16 * k) + 16 = pc + BitVec.ofNat 64 (16 * (k + 1)) := fun k => by
    rw [BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add (16 * k)]; rfl
  -- 1: const T 1
  have s1 : Counted 1 ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m1 := by
    have := const_step_counted (j := T) (k := 1) (codeAt_left (a := [ci 1 ((T : Nat) : Int) 1 0]) hc) hF (by omega) hK
      (by decide)
    simpa [m1] using this
  -- 2: sub (F+2) 2 T
  have s2 : Counted 1 ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m1 ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 := by
    refine Counted.next ?_ (.refl _ _)
    have r := run_step (t := ⟨_, fp⟩) j1 (by decide) (run_bin (t := ⟨_, fp⟩) j1 (m1 := m2) (va := dv + 1)
      (vb := BitVec.ofInt 64 1) (g := fun a b => some (a - b)) ?_ ?_
      (by show some (dv + 1 - BitVec.ofInt 64 1) = some dv
          rw [show BitVec.ofInt 64 1 = 1 by decide, BitVec.add_sub_cancel]) ?_)
    · simp only [nxt] at r; rw [e16] at r; exact r
    · rw [sx_lit (by decide), show BitVec.ofInt 64 2 = BitVec.ofNat 64 2 by decide]
      simp only [m1]; rw [rd_other hroom (by omega) (by omega) (by omega)]; exact hdv
    · rw [hsT]; exact rd_same hF (by omega) _
    · rw [hs2]; exact wr64_some (hF1.wr _ (by omega))
  -- 3: const T (A f)
  have s3 : Counted 1 ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m3 := by
    cases indirect with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at j2
      refine Counted.next ?_ (.refl _ _)
      have r : Run (op 1 ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩) m2 (nxt ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩) m3 := by
        simp only [op]
        refine f2_run (t := ⟨_, fp⟩) j2 ?_
        simp only [ret1]
        refine f1_run (t := ⟨_, fp⟩) j2 ?_
        rw [hsT, sx_lit (n := ((A f : Nat) : Int)) (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)]
        exact run_wr64 (wr64_some (hF2.wr _ (by omega)))
      have r2 := run_step (t := ⟨_, fp⟩) j2 (by decide) r
      simp only [nxt] at r2; rw [e16] at r2; exact r2
    | true =>
      simp only [↓reduceIte] at j2
      have hread : m2.rd64 (slot fp (BitVec.ofNat 64 F)) = some (BitVec.ofInt 64 (A f)) := by
        simp only [m2, m1]
        rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega)]
        simpa only [BitVec.ofInt_natCast] using htarget rfl
      have hc2 : CodeAt m2 (pc + BitVec.ofNat 64 (16 * 2)) [ci 2 T F 0] := by
        intro k hk
        have : k = 0 := by simp only [List.length_singleton] at hk; omega
        subst k
        simpa only [ci, T, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] using j2
      have st := mov_to_counted hc2 hF2 (j := T) (s := F) (by omega) (by omega) hK hread
      simpa only [List.length_singleton, show BitVec.ofNat 64 (16 * 1) = (16 : Runner.W) by decide, e16] using st
  -- 4: call T F
  have s4 : Counted 1 ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m3 ⟨BitVec.ofNat 64 (A f), slot fp (BitVec.ofNat 64 F)⟩ m5 := by
    refine Counted.next ?_ (.refl _ _)
    have := run_call (t := ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩) (m1 := m4) (m2 := m5) j3
      (tg := BitVec.ofInt 64 (A f)) (by rw [hsT]; exact rd_same hF2 (by omega) _)
      (by rw [hsF]; exact wr64_some (hF3.wr _ (by omega)))
      (by rw [hsF, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]
          exact wr64_some (hF4.wr _ (by omega)))
    rw [hsF, show BitVec.ofInt 64 (A f : Int) = BitVec.ofNat 64 (A f) by simp] at this
    exact run_step (t := ⟨_, fp⟩) j3 (by decide) this
  -- the callee's frame
  have hFF : F ≤ K := by omega
  have g0 : m5.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 0)) =
      some (pc + BitVec.ofNat 64 (16 * 3) + 16) := by
    rw [slot_slot, Nat.add_zero]
    simp only [m5]; rw [rd_other hroom (by omega) (by omega) (by omega)]
    exact rd_same hF3 (by omega) _
  have g1 : m5.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 1)) = some fp := by
    rw [slot_slot]; exact rd_same hF4 (by omega) _
  have g2 : m5.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 2)) = some dv := by
    rw [slot_slot]
    simp only [m5, m4, m3]
    rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega)]
    exact rd_same hF1 (by omega) _
  have gE : EnvAt L m5 (slot fp (BitVec.ofNat 64 F)) ρa := by
    intro τ x
    obtain ⟨w, hw, he⟩ := hE τ x
    refine ⟨w, ?_, he⟩
    have h1 := vslot_lt (reserved := 0) x
    have h2 : FB ≤ vslot x := by unfold vslot; omega
    simp only [frei] at h1
    rw [slot_slot] at hw ⊢
    simp only [m5, m4, m3, m2, m1]
    rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega)]
    exact hw
  have hW5 : WeltAt m5 L σ := weltAt_stab hW.lay (by have := hW.lo; omega) m m5 hWa
    ((a1s.trans (a2s.trans (a3s.trans (a4s.trans a5s)))).mono (Nat.zero_le _))
  refine ⟨m5, s1.trans (s2.trans (s3.trans s4)), a15, frame_sub hF5 hFF,
    pcode_sub (pcode_agree hP a15) hF5.lt hFF, ?_, ?_, g2, gE, hW5, ?_⟩
  · simpa [slot, BitVec.add_assoc] using g0
  · simpa [slot, BitVec.add_assoc] using g1
  · exact (hy.agree a15 (by have := hW.top; have := hW.ord; omega)).call (by omega)

/-- Actual recursive argument evaluation followed by the complete four-opcode
    call entry. This exposes the callee frame for a source-derived contract;
    it does not assume a bound on the whole call. -/
theorem ArgsCost.callEntry {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na : Nat}
    (certificate : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
    {ca : List II} {ta K Ks : Nat} {m : Mem} {pc fp : Runner.W}
    (lower : lowA L args (frei Γ reserved + FB) reserved = some (ca, ta))
    (fits : callTop f (frei Γ reserved) ta ≤ Ks)
    (address : A f < 2 ^ 31)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (callC A f (frei Γ reserved) ca) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ) :
    ∃ m', Counted (na + 4) ⟨pc, fp⟩ m
        ⟨BitVec.ofNat 64 (A f), slot fp (BitVec.ofNat 64 (frei Γ reserved))⟩ m' ∧
      Agree fp (frei Γ reserved) K m m' ∧
      FrameOK m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved) ∧
      PCode m' A C (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) =
        some (pc + BitVec.ofNat 64 (16 * (ca.length + 4))) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved)) + 8) = some fp ∧
      m'.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (BitVec.ofNat 64 2)) = some dv ∧
      EnvAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (evalArgs σ₀ args σ ρ) ∧
      WeltAt m' L σ ∧
      SyncOK m' L (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (Ks - frei Γ reserved) := by
  have hFB : FB ≤ frei Γ reserved := by simp only [frei]; omega
  have hks := inside.ks
  have bounds := fits
  simp only [callTop] at bounds
  have pre' : PreS L m pc fp K (frei Γ reserved + FB)
      (ca ++ callTail A f (frei Γ reserved)) ρ reserved := pre.up (by omega)
  have argPre := PreS.welt pre'.left hks world inside.lay (by have := inside.lo; omega)
  obtain ⟨m1, argsRun, argsAgree, params⟩ := certificate.sound lower
    (by omega) (by omega) argPre
  have widened := Agree.widen argsAgree hks
  have world1 := argPre.wstab m m1 world (argsAgree.mono (Nat.zero_le _))
  have tailPre := pre'.next widened (Nat.le_refl _) (by omega)
  have around := surroundings.agree widened pre.frame (by omega)
  obtain ⟨m2, tailRun, tailAgree, frame, code, rpc, rfp, depth, env, world2, sync⟩ :=
    callTail_counted (indirect := false) tailPre.code (by simpa [callTail, callTailN] using tailPre.far)
      tailPre.frame pre.small hFB (by omega) address around.code around.depth params inside world1 around.sync
  refine ⟨m2, argsRun.trans tailRun, (widened.mono (by omega)).trans tailAgree,
    frame, code, ?_, rfp, depth, env, world2, sync⟩
  simpa only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc,
    show BitVec.ofNat 64 (16 * 4) = (64 : Runner.W) from rfl] using rpc

/-- Assignment cost comes from its expression tree and the actual move.
    The result retains the changed source environment and unchanged world. -/
theorem countedAssignVar_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {x : Var Γ τ} {e : Expr D Γ Λ τ}
    {passes lo K Ks ne top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {v : Wert D τ} {σ : World D}
    (certificate : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
    (lower : lowS (V := V) (l := l) (reserved := reserved)
      passes A L lo ens pr ex (.assignVar x e) = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach (ne + 1) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ (ρ.set x v) reserved := by
  simp only [lowS] at lower
  split at lower
  next allowed =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ce, te⟩, he, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have hks := inside.ks
    have room := lowE_top e _ _ _ he
    have hpw := PreS.welt pre.left hks world inside.lay (by have := inside.lo; omega)
    obtain ⟨m1, run1, a1s, w, read, encoded⟩ := certificate.sound he fits hpw
    have a1 := Agree.widen a1s hks
    have hp1 := pre.next a1 (Nat.le_refl _) (by omega)
    have hxs := vslot_lt (reserved := reserved) x
    have hF1 := hp1.frame
    have run2 := mov_to_counted hp1.code hF1 (j := vslot x reserved)
      (by omega) (by omega) pre.small read
    have a2s : Agree fp lo Ks m1 _ :=
      agree_write (frameOK_sub hF1 hks).room allowed.1 (by omega) w.toNat
    refine ⟨_, ?_, agreeW_of ((a1.mono low).trans (Agree.widen a2s hks)), ?_,
      hpw.wstab m _ world ((a1s.mono (Nat.zero_le _)).trans (a2s.mono (Nat.zero_le _))),
      (keeps_of_agreeW inside a1 hprotected (by omega)).trans
        (keeps_write hF1.room (by omega) (fun j hj => by have := hprotected j hj; omega) allowed.2 _)⟩
    · rw [pc_add1]; exact run1.trans run2
    · refine envAt_set hp1.env
        (rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))) encoded ?_
      intro τ' y hy
      have := vslot_lt (reserved := reserved) y
      exact rd64_write_far (slot_far hF1.room (by omega) (by omega) (vslot_ne hy).symm)
  next refused => simp at lower

/-- A global write counts the actual value tree, address constant and store.
    The postcondition contains the updated world, with no timing assumption. -/
theorem countedAssignGlob_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Glob} {e : Expr D Γ Λ (D.gtyp g)} {hw : V.gschreibt g = true}
    {hL : gdarf D g Λ} {v : Wert D (D.gtyp g)}
    {passes lo K Ks ne top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W} {ρ : Env D Γ} {σ : World D}
    (certificate : ExprCost L reserved e (frei Γ reserved) ne (Enc L (D.gtyp g) v))
    (lower : lowS (V := V) (l := l) (reserved := reserved)
      passes A L lo ens pr ex (.assignGlob g e hw hL) = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach (ne + (1 + 1)) L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) (σ.storeGlob g v) ρ reserved := by
  simp only [lowS] at lower
  split at lower
  next allowed =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ce, te⟩, he, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have room := lowE_top e _ _ _ he
    obtain ⟨m', run, agree, env, world'⟩ := store_counted pre inside world (by omega)
      (fun m pc hp => certificate.sound he (by omega) hp)
      (fun m pc hp => by
        obtain ⟨_, rd, agree⟩ := wr_slot hp.frame (d := frei Γ reserved + 1)
          (by omega) (BitVec.ofInt 64 (L.ga g))
        exact ⟨_, const_step_counted hp.code hp.frame (by omega) hp.small allowed,
          agree, _, rd, BitVec.ofInt_natCast _ _⟩)
      (inside.lay.2.1 g)
      (fun m w hm hpe => weltAt_glob hm inside.lay inside.dis hpe)
    exact ⟨m', run, agree.mono low, env, world',
      keeps_of_agreeW inside agree hprotected (by have := inside.ks; omega)⟩
  next refused => simp at lower

/-- Recursive source certificate for normal block outcomes. Only constructors
    with proved lowering costs are admitted; there is no arbitrary-run leaf.
    Both source states are indices, so cons threads the actual changed world
    and environment instead of silently restoring the entry state. -/
inductive BlockCost (L : Lay D) (reserved : Nat) (V : Vertrag D) (l : Bool) :
    {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' →
      World D → Env D Γ → World D → Env D Γ → Nat → Type
  | nil {Γ Λ σ} {ρ : Env D Γ} :
      BlockCost L reserved V l (.nil (Λ := Λ)) σ ρ σ ρ 0
  | assign {Γ Λ τ} {x : Var Γ τ} {e : Expr D Γ Λ τ}
      {rest : Block D V l Γ Λ Λ} {σ σ' : World D}
      {ρ ρ' : Env D Γ} {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : BlockCost L reserved V l rest σ (ρ.set x v) σ' ρ' nr) :
      BlockCost L reserved V l (.cons (.assignVar x e) rest) σ ρ σ' ρ' (ne + 1 + nr)

  | global {Γ Λ} {g : D.Glob} {e : Expr D Γ Λ (D.gtyp g)}
      {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
      {rest : Block D V l Γ Λ Λ} {σ σ' : World D}
      {ρ ρ' : Env D Γ} {v : Wert D (D.gtyp g)} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L (D.gtyp g) v))
      (tail : BlockCost L reserved V l rest (σ.storeGlob g v) ρ σ' ρ' nr) :
      BlockCost L reserved V l (.cons (.assignGlob g e hw hL) rest)
        σ ρ σ' ρ' (ne + (1 + 1) + nr)

  | bind {Γ Λ Λ' τ} {e : Expr D Γ Λ τ}
      {rest : Block D V l (τ :: Γ) Λ Λ'} {σ σ' : World D}
      {ρ : Env D Γ} {ρ' : Env D (τ :: Γ)} {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : BlockCost L reserved V l rest σ (.cons v ρ) σ' ρ' nr) :
      BlockCost L reserved V l (.bind e rest) σ ρ σ' ρ'.tail (ne + nr)

  | branch {Γ Λ Λmid Λ'} {c : Expr D Γ Λ .bool}
      {t e : Block D V l Γ Λ Λmid} {rest : Block D V l Γ Λmid Λ'}
      {σ σ1 σ' : World D} {ρ ρ1 ρ' : Env D Γ} {choice : Bool} {nc nb nr : Nat}
      (condition : ExprCost L reserved c (frei Γ reserved) nc (· = if choice then 1 else 0))
      (jumps : ∀ passes A lo ens pr ex ct tt ce te,
        lowB (reserved := reserved) passes A L lo ens pr ex e = some (ce, te) →
        lowB (reserved := reserved) passes A L lo ens pr (exPlus ex (ce.length + 1)) t = some (ct, tt) →
        16 * (ct.length + 2) < 2 ^ 31 ∧ 16 * (ce.length + 1) < 2 ^ 31)
      (child : BlockCost L reserved V l (if choice then t else e) σ ρ σ1 ρ1 nb)
      (tail : BlockCost L reserved V l rest σ1 ρ1 σ' ρ' nr) :
      BlockCost L reserved V l (.cons (.ite c t e) rest) σ ρ σ' ρ'
        ((nc + 1 + nb + if choice then 1 else 0) + nr)

/-- Every count is derived from an accepted source lowering. The only
    additional obligations are the existing frame/layout/world conditions. -/
theorem BlockCost.sound {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'}
    {σ σ' : World D} {ρ ρ' : Env D Γ} {n : Nat}
    (certificate : BlockCost L reserved V l b σ ρ σ' ρ' n)
    {passes lo K Ks top : Nat} {A : D.Fn → Nat} {ens : List II × Nat}
    {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp : W}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach n L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ' ρ' reserved := by
  induction certificate generalizing top code m pc ex with
  | nil =>
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨rfl, rfl⟩ := lower
    simpa using countedBlockNil_case (L := L) (lo := lo) (pr := pr) pre.env world
  | assign value tail ih =>
    have decoded := lower
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨⟨cr0, tr0⟩, hr0, ⟨cs0, ts0⟩, hs0, out⟩ := decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    apply countedBlockCons_case lower inside pre
    · intro cr tr cs ts hr hs hp
      rw [hr0] at hr
      cases hr
      rw [hs0] at hs
      cases hs
      exact countedAssignVar_case value hs0
        (Nat.le_trans (Nat.le_max_left _ _) fits) inside low hprotected hp world
    · intro cr tr hr m' pc' hp hw
      rw [hr0] at hr
      cases hr
      exact ih hr0 (Nat.le_trans (Nat.le_max_right _ _) fits) low hprotected hp hw
  | global value tail ih =>
    have decoded := lower
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨⟨cr0, tr0⟩, hr0, ⟨cs0, ts0⟩, hs0, out⟩ := decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    apply countedBlockCons_case lower inside pre
    · intro cr tr cs ts hr hs hp
      rw [hr0] at hr
      cases hr
      rw [hs0] at hs
      cases hs
      exact countedAssignGlob_case value hs0
        (Nat.le_trans (Nat.le_max_left _ _) fits) inside low hprotected hp world
    · intro cr tr hr m' pc' hp hw
      rw [hr0] at hr
      cases hr
      exact ih hr0 (Nat.le_trans (Nat.le_max_right _ _) fits) low hprotected hp hw
  | bind value tail ih =>
    have decoded := lower
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨⟨ce0, te0⟩, he0, ⟨cr0, tr0⟩, hr0, out⟩ := decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have result := countedBlockBind_case value lower fits inside low hprotected pre world
      (fun cr tr hr m' pc' hp hw => by
        rw [hr0] at hr
        cases hr
        apply ih hr0 (Nat.le_trans (Nat.le_max_right _ _) fits) ?_ ?_ hp hw
        · simp only [frei, List.length_cons] at low ⊢; omega
        · intro j hj
          have h := hprotected j hj
          simp only [frei, List.length_cons] at h ⊢; omega)
    obtain ⟨m', run, agree, env, world', keep⟩ := result
    exact ⟨m', run, agree, envAt_tail env, world', keep⟩

  | @branch Γ Λ Λmid Λ' c t e rest σ σ1 σ' ρ ρ1 ρ' choice nc nb nr condition jumps child tail ih it =>
    have hks := inside.ks
    have normalize (x : Nat) : 16 + (16 + x) = 32 + x := by omega
    have decoded := lower
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at decoded
    obtain ⟨⟨cr0, tr0⟩, hr0, ⟨cs0, ts0⟩, hs0, out⟩ := decoded
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    apply countedBlockCons_case lower inside pre
    · intro cr tr cs ts hr hs hp
      rw [hr0] at hr; cases hr
      rw [hs0] at hs; cases hs
      simp only [lowS, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs0
      obtain ⟨⟨cc, tc⟩, hc, ⟨ce, te⟩, he, ⟨ct, tt⟩, ht, out⟩ := hs0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
      have room := lowE_top _ _ _ _ hc
      have hq : PreS L m pc fp K (frei Γ reserved)
          (cc ++ ([ci 19 (frei Γ reserved) (16 * (ct.length + 2)) 0] ++
            (ct ++ ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)))) ρ reserved := by
        simpa [List.append_assoc] using hp
      have hpw := PreS.welt hq.left inside.ks world inside.lay (by have := inside.lo; omega)
      obtain ⟨m1, run1, a1s, w, read, value⟩ := condition.sound hc (by omega) hpw
      have a1 := Agree.widen a1s inside.ks
      have h1 := hq.next a1 (Nat.le_refl _) (by omega)
      have h2 := h1.next (a := [ci 19 (frei Γ reserved) (16 * (ct.length + 2)) 0])
        (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      have ins := h1.code 0 (by simp)
      simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
      have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) := sx_nat (by have := pre.small; omega)
      have world1 := hpw.wstab m m1 world (a1s.mono (Nat.zero_le _))
      have sizes := jumps _ _ _ _ _ _ _ _ _ _ he ht
      cases choice with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at value child ih ⊢
        subst w
        have step := run_step (t := ⟨_, fp⟩) ins (by decide) (run_brz_zero ins (by rw [hd]; exact read))
        have offset : sx (II.f (16 * ((ct.length : Int) + 2))) = BitVec.ofNat 64 (16 * (ct.length + 2)) := by
          simpa using sx_nat (d := 16 * (ct.length + 2)) sizes.1
        rw [offset] at step
        have h3 := h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
        have h4 := h3.next (a := [ci 18 (16 * (ce.length + 1)) 0 0]) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
        obtain ⟨m2, run2, agree, env, hw, keep⟩ := ih he (by omega) low hprotected h4 world1
        refine ⟨m2, ?_, (agreeW_of (a1.mono low)).trans agree, env, hw, ?_⟩
        · simpa [List.length_append, List.length_singleton, pc_add, addr_norm, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run1.trans ((Counted.next step (Counted.refl _ _)).trans (by simpa [List.length_singleton, pc_add, addr_norm, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, normalize] using run2))
        · exact (keeps_of_agreeW inside (agreeW_of a1) hprotected (by have := inside.ks; omega)).trans keep
      | true =>
        simp only [Bool.true_eq, ↓reduceIte] at value child ih ⊢
        subst w
        have sb := counted_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
          (by simp only [ci]; exact run_brz_ne ins (by rw [hd]; exact read) (by decide))
        obtain ⟨m2, run2, agree, env, hw, keep⟩ := ih ht (by omega) low hprotected h2.left world1
        have h3 : PreS L m2 _ fp K (frei Γ reserved) ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce) ρ1 reserved :=
          ⟨h2.ctx, h2.small, frameOK_agreeW h2.frame agree,
            codeAt_agreeWIn inside agree (codeAt_right h2.code) (codeFar_right (by simpa only [List.length_append] using h2.far)),
            codeFar_right (by simpa only [List.length_append] using h2.far), env, trivial, wstab_true _ _⟩
        have ji := h3.code 0 (by simp)
        simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ji
        have step := run_step (t := ⟨_, fp⟩) ji (by decide) (run_jmp ji)
        have offset : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
          simpa using sx_nat (d := 16 * (ce.length + 1)) sizes.2
        rw [offset] at step
        refine ⟨m2, ?_, (agreeW_of (a1.mono low)).trans agree, env, hw, ?_⟩
        · simpa [List.length_append, List.length_singleton, pc_add, addr_norm, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, normalize] using run1.trans (sb.trans (run2.trans (Counted.next step (Counted.refl _ _))))
        · exact (keeps_of_agreeW inside (agreeW_of a1) hprotected (by have := inside.ks; omega)).trans keep
    · intro cr tr hr m' pc' hp hw
      rw [hr0] at hr; cases hr
      exact it hr0 (by omega) low hprotected hp hw

/-- Actual `lowEnd .cons` threads a normal statement outcome into a terminal
    continuation. The continuation can return to its caller or stop in a
    nested loop; it need not fall through to the end of the instruction list.
    Its cost is a recursive child obligation, never a bound on the whole body. -/
theorem countedEndCons_case
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λmid : List (Res D)}
    {s : Stmt D V l Γ Λ Λmid} {rest : Endblock D V l Γ Λmid}
    {passes lo K Ks ns nr top : Nat} {A : D.Fn → Nat}
    {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    {ρ ρ1 : Env D Γ} {σ1 : World D} {Done : T → Mem → Prop}
    (lower : lowEnd (reserved := reserved) passes A L lo ens pr ex (.cons s rest) =
      some (code, top))
    (inside : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (stmtRuns : ∀ cr tr cs ts,
      lowEnd (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      lowS (reserved := reserved) passes A L lo ens pr (exPlus ex cr.length) s = some (cs, ts) →
      PreS L m pc fp K (frei Γ reserved) cs ρ reserved →
      CountedReach ns L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * cs.length)) σ1 ρ1 reserved)
    (restRuns : ∀ cr tr,
      lowEnd (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr) →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved) cr ρ1 reserved →
      WeltAt m' L σ1 → ∃ u b, Counted nr ⟨pc', fp⟩ m' u b ∧ Done u b) :
    ∃ u b, Counted (ns + nr) ⟨pc, fp⟩ m u b ∧ Done u b := by
  simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, out⟩ := lower
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
  obtain ⟨m1, run1, agree1, env1, world1, keep1⟩ :=
    stmtRuns cr tr cs ts hr hs pre.left
  have far := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
  have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K
      (frei Γ reserved) cr ρ1 reserved :=
    ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame agree1,
      codeAt_agreeWIn inside agree1 (codeAt_right pre.code) far,
      far, env1, trivial, wstab_true _ _⟩
  obtain ⟨u, b, run2, done⟩ := restRuns cr tr hr m1 _ nextPre world1
  exact ⟨u, b, run1.trans run2, done⟩

namespace ReturnTailProbe
open FnptrProben

def image : List II := [ci 19 5 48 0, ci 2 2 4 0, ci 21 0 0 0]

def memory : Mem :=
  let base : Mem := {
    b := fun a => ((image.flatMap encII)[a.toNat]?).getD 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write (write (write base 4096 8 2048) 4104 8 8192) 4128 8 37) 4136 8 1

/-- Loaded nonzero result and distinct caller frame exercise the real return. -/
theorem return_tail_zeuge :
    ∃ m', Counted 3 ⟨0, 4096⟩ memory ⟨2048, 8192⟩ m' ∧
      Agree 4096 2 16 memory m' ∧ m'.rd64 4112 = some 37 ∧
      m'.rd64 4136 = some 1 := by
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  exact returnTail_counted code (by unfold CodeFar; decide +kernel)
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩ (by decide) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end ReturnTailProbe

namespace BlockCostProbe
/-- A genuine nonempty statement body under a lexical binding. -/
def body (V : Vertrag D) : Block D V false [] [] [] :=
  .bind (.lit 2) (.cons (.assignVar .here (.lit 2)) .nil)

omit [Kern] in
/-- The count is derived from source constructors: binding, literal and move.
    This witness covers assignment blocks, not calls or nested forever. -/
theorem block_certificate_zeuge (V : Vertrag D) (σ : World D) :
    Nonempty (BlockCost L reserved V false (body V) σ .nil σ .nil 3) := by
  let v : Wert D (.int 2 2) := ⟨2, by decide, by decide⟩
  have value {Γ : Ctx} (d : Nat) :
      ExprCost L reserved (Γ := Γ) (Λ := []) (.lit 2) d 1 (Enc L (.int 2 2) v) :=
    .literal
  exact ⟨.bind (value _) (.assign (value _) .nil)⟩

open FnptrProben in
def image : List II := [ci 1 4 2 0, ci 1 5 2 0, ci 2 4 5 0]

open FnptrProben in
def memory : Mem := { callMem with
  b := fun a => if a.toNat < 48 then
    ((image.flatMap encII)[a.toNat]?).getD 0 else callMem.b a }

open FnptrProben in
omit [Kern] in
/-- Two actual argument expressions inhabit the recursive certificate. -/
theorem args_certificate_zeuge (σ : World FnptrProben.D) :
    Nonempty (ArgsCost callLayout 0 0
      (show Args FnptrProben.D [] [] [.int 2 2, .int 2 2] from
        .cons (.lit 2) (.cons (.lit 2) .nil)) σ σ .nil 2) := by
  exact ⟨.cons (nr := 1) (ne := 1) (.cons (nr := 0) (ne := 1) .nil .literal) .literal⟩

open FnptrProben in
/-- The certificate and every simulation premise are inhabited together on a
    loaded accepted body; this is not merely a syntactic certificate fixture. -/
theorem block_sound_zeuge :
    CountedReach 3 callLayout 4096 4 256 [] ⟨0, 4096⟩ memory
      48 world (Env.nil : Env FnptrProben.D []) 0 := by
  have lower : lowB 2 addresses callLayout 4 ([], 6) [] (0, 0)
      (body (vertragVon FnptrProben.D 2)) = some (image, 6) := by decide +kernel
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        (memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o)) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨op, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using op, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout memory 0 4096 256 4 image (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt memory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  obtain ⟨cert⟩ := block_certificate_zeuge (L := callLayout) (reserved := 0)
    (vertragVon FnptrProben.D 2) world
  exact cert.sound lower (by decide) call_win (by decide)
    (by intro j hj; cases hj) pre hw

namespace Branch
open FnptrProben

def source (choice : Bool) : Block FnptrProben.D (vertragVon FnptrProben.D 2) false [] [] [] :=
  .cons (.ite (if choice then .tru else .fls)
    (body (vertragVon FnptrProben.D 2)) (body (vertragVon FnptrProben.D 2))) (body (vertragVon FnptrProben.D 2))

def image (choice : Bool) : List II :=
  [ci 1 4 (if choice then 1 else 0) 0, ci 19 4 80 0] ++
    BlockCostProbe.image ++ [ci 18 64 0 0] ++ BlockCostProbe.image ++ BlockCostProbe.image

def memory (choice : Bool) : Mem := { callMem with
  b := fun a => if a.toNat < 192 then
    (((image choice).flatMap encII)[a.toNat]?).getD 0 else callMem.b a }

set_option maxHeartbeats 2000000 in
/-- Both directions run a nonempty child and then the recursive continuation. -/
theorem sound_zeuge (choice : Bool) :
    CountedReach (8 + if choice then 1 else 0) callLayout 4096 4 256 []
      ⟨0, 4096⟩ (memory choice) 192 world (Env.nil : Env FnptrProben.D []) 0 := by
  have lower : lowB 2 addresses callLayout 4 ([], 6) [] (0, 0) (source choice) =
      some (image choice, 6) := by cases choice <;> decide +kernel
  have code : CodeAt (memory choice) 0 (image choice) := by
    have h : ∀ k : Fin (image choice).length,
        (memory choice).rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 (image choice)[k.val].o) ∧
        (memory choice).rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f (image choice)[k.val].a) ∧
        (memory choice).rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f (image choice)[k.val].b) ∧
        (memory choice).rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f (image choice)[k.val].c) := by
      cases choice <;> apply allFin <;> decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout (memory choice) 0 4096 256 4 (image choice) (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩, code, ?_, ?_, trivial, wstab_true _ _⟩
    · cases choice <;> unfold CodeFar <;> decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt (memory choice) callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    cases choice <;> decide +kernel
  obtain ⟨leaf⟩ := block_certificate_zeuge (L := callLayout) (reserved := 0)
    (vertragVon FnptrProben.D 2) world
  have cert : BlockCost callLayout 0 (vertragVon FnptrProben.D 2) false
      (source choice) world .nil world .nil (8 + if choice then 1 else 0) := by
    have cost : (8 + if choice then 1 else 0) = ((1 + 1 + 3 + if choice then 1 else 0) + 3) := by omega
    rw [cost]
    apply BlockCost.branch (nc := 1) (nb := 3) (nr := 3)
    · cases choice
      · exact .falsity
      · exact .truth
    · intro passes A lo ens pr ex ct tt ce te he ht
      have equation (ex : Int × Int) :
          lowB passes A callLayout lo ens pr ex (body (vertragVon FnptrProben.D 2)) =
          (do let rest ← (do
                let piece ← (if lo ≤ 4 ∧ 4 ∉ pr then
                  some ([ci 1 5 2 0, ci 2 4 5 0], 6) else none)
                pure (piece.1 ++ [], max piece.2 5))
              pure ([ci 1 4 2 0] ++ rest.1, max 5 rest.2)) := rfl
      rw [equation] at he ht
      by_cases allowed : lo ≤ 4 ∧ 4 ∉ pr
      · simp only [if_pos allowed, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at he ht
        obtain ⟨rfl, _⟩ := he
        obtain ⟨rfl, _⟩ := ht
        decide
      · simp only [if_neg allowed, bind, Option.bind_none, reduceCtorEq] at he
    · cases choice <;> exact leaf
    · exact leaf
  have result := cert.sound lower (by decide) call_win (by decide)
    (by intro j hj; cases hj) pre hw
  simpa [image, BlockCostProbe.image] using result

end Branch

open FnptrProben in
/-- The certificate executes jointly with a loaded image and frame. Argument
    slots 4 and 5 contain both source values after exactly two instructions. -/
theorem args_sound_zeuge :
    ∃ m', Counted 2 ⟨0, 4096⟩ memory ⟨32, 4096⟩ m' ∧
      Agree 4096 4 256 memory m' ∧
      EnvAt callLayout m' 4096
        (evalArgs world
          (show Args FnptrProben.D [] [] [.int 2 2, .int 2 2] from
            .cons (.lit 2) (.cons (.lit 2) .nil)) world .nil) := by
  let args : Args FnptrProben.D [] [] [.int 2 2, .int 2 2] :=
    .cons (.lit 2) (.cons (.lit 2) .nil)
  have lower : lowA callLayout args 4 =
      some ([ci 1 4 2 0, ci 1 5 2 0], 6) := rfl
  have code : CodeAt memory 0 [ci 1 4 2 0, ci 1 5 2 0] := by
    intro k hk
    have cases : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
    rcases cases with rfl | rfl <;>
      exact ⟨by decide +kernel +revert, by decide +kernel +revert, by decide +kernel +revert, by decide +kernel +revert⟩
  have pre : PreS callLayout memory 0 4096 256 4
      [ci 1 4 2 0, ci 1 5 2 0] (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  obtain ⟨certificate⟩ := args_certificate_zeuge world
  have result := certificate.sound lower (by decide) (by decide)
    (W := fun m => WeltAt m callLayout world)
    (show Pre callLayout memory 0 4096 256 4
      [ci 1 4 2 0, ci 1 5 2 0] .nil (fun m => WeltAt m callLayout world) from
      ⟨pre.ctx, pre.small, pre.frame, pre.code, pre.far, pre.env, ?_, ?_⟩)
  · simpa [slot, FB] using result
  · refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  · exact fun m m' h a => weltAt_stab call_win.lay (by decide) m m' h (a.mono (Nat.zero_le _))

open FnptrProben in
def entryImage : List II := callC addresses 0 4 []

open FnptrProben in
def entryMemory : Mem := { callMem with
  b := fun a => if 2048 ≤ a.toNat ∧ a.toNat < 2112 then
    ((entryImage.flatMap encII)[a.toNat - 2048]?).getD 0 else callMem.b a }

open FnptrProben in
/-- Loaded actual direct-call entry jointly inhabits all frame, code, world,
    depth and hardware premises; this witness does not claim callee return. -/
theorem call_entry_zeuge :
    ∃ m', Counted 4 ⟨2048, 4096⟩ entryMemory ⟨64, 4128⟩ m' ∧
      Agree 4096 4 256 entryMemory m' ∧
      m'.rd64 4128 = some 2112 ∧ m'.rd64 4136 = some 4096 ∧
      m'.rd64 4144 = some 2 ∧ WeltAt m' callLayout world := by
  have code : CodeAt entryMemory 2048 entryImage := by
    have h : ∀ k : Fin entryImage.length,
        entryMemory.rd8 (2048 + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 entryImage[k.val].o) ∧
        entryMemory.rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f entryImage[k.val].a) ∧
        entryMemory.rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f entryImage[k.val].b) ∧
        entryMemory.rd32 (2048 + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f entryImage[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨o, a, b, c⟩
  have functions : PCode entryMemory addresses target 4096 256 := by
    intro f
    refine ⟨?_, (targets_code f).2⟩
    have h : ∀ f : Fin 3, ∀ k : Fin (target f).length,
        entryMemory.rd8 (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 (target f)[k.val].o) ∧
        entryMemory.rd32 (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f (target f)[k.val].a) ∧
        entryMemory.rd32 (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f (target f)[k.val].b) ∧
        entryMemory.rd32 (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f (target f)[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h f ⟨k, hk⟩
    exact ⟨o, a, b, c⟩
  have pre : PreS callLayout entryMemory 2048 4096 256 4 entryImage (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      code, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
    unfold CodeFar; decide +kernel
  have worldAt : WeltAt entryMemory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g; decide +kernel
  have sync : SyncOK entryMemory callLayout 4096 128 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩
  have around : Umf callLayout addresses target 2 entryMemory 4096 128 256 :=
    ⟨functions, by decide +kernel, by decide, sync, by decide⟩
  have cert : ArgsCost callLayout 0 4 (show Args FnptrProben.D [] [] (FnptrProben.D.params 0) from .nil)
      world world .nil 0 := .nil
  obtain ⟨m', run, agree, _, _, rpc, rfp, depth, _, world', _⟩ :=
    ArgsCost.callEntry (reserved := 0) (Γ := []) (f := (0 : Fin 3))
      (args := .nil) (ca := []) (ta := 8) cert (by rfl) (by decide) (by decide) pre around call_win worldAt
  exact ⟨m', run, agree, rpc, rfp, depth, world'⟩

open FnptrProben in
def storeImage : List II := [ci 1 4 576 0, ci 1 5 8192 0, stC 4]

open FnptrProben in
def storeMemory : Mem := { callMem with
  b := fun a => if a.toNat < 48 then
    ((storeImage.flatMap encII)[a.toNat]?).getD 0 else callMem.b a }

open FnptrProben in
/-- Loaded nonempty world write: the global function pointer changes from
    target zero to target one in exactly three canonical instructions. -/
theorem store_counted_zeuge :
    ∃ m', Counted 3 ⟨0, 4096⟩ storeMemory ⟨48, 4096⟩ m' ∧
      AgreeW callLayout 4096 4 256 storeMemory m' ∧
      EnvAt callLayout m' 4096 (Env.nil : Env FnptrProben.D []) 0 ∧
      WeltAt m' callLayout (world.storeGlob () ⟨1, by decide⟩) := by
  have code : CodeAt storeMemory 0 storeImage := by
    have h : ∀ k : Fin storeImage.length,
        (storeMemory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 storeImage[k.val].o)) ∧
        (storeMemory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f storeImage[k.val].a)) ∧
        (storeMemory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f storeImage[k.val].b)) ∧
        (storeMemory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f storeImage[k.val].c)) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨op, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using op, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout storeMemory 0 4096 256 4 storeImage
      (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt storeMemory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  apply store_counted (ce := [ci 1 4 576 0]) (ca := [ci 1 5 8192 0])
    (ne := 1) (na := 1) (a := 8192) (Pe := (· = 576)) pre call_win hw (by decide)
  · intro m pc hp
    obtain ⟨_, rd, agree⟩ := wr_slot hp.frame (d := 4) (by decide) 576
    exact ⟨_, const_step_counted hp.code hp.frame (by decide) hp.small (by decide),
      agree, _, rd, rfl⟩
  · intro m pc hp
    obtain ⟨_, rd, agree⟩ := wr_slot hp.frame (d := 5) (by decide) 8192
    exact ⟨_, const_step_counted hp.code hp.frame (by decide) hp.small (by decide),
      agree, _, rd, rfl⟩
  · decide
  · intro m w hm hv
    subst w
    exact weltAt_glob hm call_win.lay call_win.dis rfl
end BlockCostProbe

/-- One actual snapshot load, including its memory requests, is one S0IR step. -/
theorem capture_load_counted {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {a w : Runner.W}
    (hf : FrameOK m fp K) (hk : K < 2 ^ 31) (hd : 3 < K)
    (hc : CodeAt m pc [ci 15 3 3 0])
    (ha : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some a) (hw : m.rd64 a = some w) :
    Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ (write m (slot fp (BitVec.ofNat 64 3)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  apply Counted.next (n := 0) _ (Counted.refl _ _)
  apply run_step (t := ⟨pc, fp⟩) hi (by decide)
  simp only [op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [show sx (II.f (3 : Int)) = (3 : Runner.W) by decide +kernel]
  refine run_rd64 ha ?_
  refine run_rd64 hw ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [show sx (II.f (3 : Int)) = (3 : Runner.W) by decide +kernel]
  exact run_wr64 (wr64_some (hf.wr 3 hd))


/-- Exact emitted snapshot cost with entry values, world and caller slots retained. -/
theorem snapC_counted {cs : List (Zelle D)} {c : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {K : Nat} {σ : World D} (hc : snapC L cs = some c) (hf : FrameOK m fp K)
    (hk : K < 2 ^ 31) (hd : 3 < K) (hcode : CodeAt m pc c) (hfar : CodeFar pc c.length fp K)
    (hw : WeltAt m L σ) (hl : LayIn L) (hwl : fp.toNat + 8 * K ≤ L.lo) :
    ∃ m', Counted c.length ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
      Agree fp 3 K m m' ∧ SnapAt L cs σ m' fp ∧
      (∀ j, j < K → j ≠ 3 → m'.rd64 (slot fp (BitVec.ofNat 64 j)) = m.rd64 (slot fp (BitVec.ofNat 64 j))) := by
  cases cs with
  | nil =>
    simp only [snapC, Option.some.injEq] at hc
    subst c
    exact ⟨m, by simpa using Counted.refl _ m, Agree.refl _ _ _ _, (fun _ h => nomatch h), fun _ _ _ => rfl⟩
  | cons z zs =>
    cases zs with
    | cons _ _ => simp [snapC] at hc
    | nil =>
      simp only [snapC] at hc
      split at hc
      · next htest =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
        cases hc
        let m1 := write m (slot fp (BitVec.ofNat 64 3)) 8 (BitVec.ofInt 64 (z.adr L)).toNat
        have s1 := const_step_counted (m := m) (pc := pc) (fp := fp) (K := K) (j := 3) (k := (z.adr L : Int)) (codeAt_left (b := [ci 15 3 3 0]) hcode) hf hd hk htest.2
        have a1 : Agree fp 3 K m m1 := agree_write hf.room (Nat.le_refl _) hd _
        have hf1 := hf.agree a1
        have hfar1 := codeFar_right (n := 1) (k := 1) hfar
        have hc1 := (codeAt_right (a := [ci 1 3 (z.adr L) 0]) hcode).agree a1 hfar1
        have hw1 : WeltAt m1 L σ := weltAt_stab hl hwl m m1 hw (a1.mono (Nat.zero_le _))
        obtain ⟨w, hword, he⟩ : ∃ w, m1.rd64 (BitVec.ofNat 64 (z.adr L)) = some w ∧ Enc L z.ty (z.val σ) w := by
          cases z with
          | glob g => exact hw1.2.1 g
          | elem t f k => exact hw1.1 t f k htest.1
        have ha : m1.rd64 (slot fp (BitVec.ofNat 64 3)) = some (BitVec.ofNat 64 (z.adr L)) := by
          simpa only [m1, BitVec.ofInt_natCast] using rd_same (a := 3) hf hd (BitVec.ofInt 64 (z.adr L))
        have s2 := capture_load_counted hf1 hk hd hc1 ha hword
        let m2 := write m1 (slot fp (BitVec.ofNat 64 3)) 8 w.toNat
        have a2 : Agree fp 3 K m1 m2 := agree_write hf1.room (Nat.le_refl _) hd _
        refine ⟨m2, ?_, a1.trans a2, ?_, ?_⟩
        · simpa [m1, m2, BitVec.add_assoc] using s1.trans s2
        · intro z' hz
          simp only [List.mem_singleton] at hz
          subst z'
          exact ⟨w, rd_same (a := 3) hf1 hd w, he⟩
        · intro j hj hne
          dsimp only [m2, m1]
          rw [rd_other (a := 3) (b := j) hf1.room hd hj (Ne.symm hne), rd_other (a := 3) (b := j) hf.room hd hj (Ne.symm hne)]
      · cases hc

namespace OldProbe
/-- A live world cell is captured in two steps while the other header slots survive. -/
theorem snapC_counted_zeuge :
    ∃ m', Counted 2 ⟨0, 1024⟩ (memory captureCode) ⟨32, 1024⟩ m' ∧
      SnapAt layout [.glob ()] exitWorld m' 1024 ∧
      (∀ j, j < 16 → j ≠ 3 →
        m'.rd64 (slot 1024 (BitVec.ofNat 64 j)) =
          (memory captureCode).rd64 (slot 1024 (BitVec.ofNat 64 j))) := by
  obtain ⟨m', hs, _, hp, keep⟩ := snapC_counted (L := layout) (cs := [.glob ()])
    (c := captureCode) (m := memory captureCode) (pc := 0) (fp := 1024)
    (K := 16) (σ := exitWorld) (by decide +kernel) (frame _) (by decide)
    (by decide) capture_at (by unfold CodeFar; decide +kernel)
    (world captureCode) lay (by decide)
  exact ⟨m', hs, hp, keep⟩
end OldProbe

/-- Recursive costs for the actual postcondition compiler. The immutable
    snapshot word is an input value, not an assumed execution or cost. -/
inductive EnsCost (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (snapshot : W) :
    {τ : Ty} → Expr D Γ Λ τ → Nat → Nat → (W → Prop) → Type
  | ordinary {τ} {e : Expr D Γ Λ τ} {d n P}
      (equation : lowEns L e d = lowE L e d)
      (body : ExprCost L 0 e d n P) : EnsCost L snapshot e d n P
  | captured {τ} {e : Expr D Γ Λ τ} {d}
      (equation : lowEns L e d = some ([ci 2 d 3 0], d + 1)) :
      EnsCost L snapshot e d 1 (· = snapshot)
  | binary {τ τa τb} {e : Expr D Γ Λ τ}
      {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {d o na nb Pa Pb P}
      {g : W → W → Option W}
      (equation : lowEns L e d = (do
        let ca ← lowEns L a d
        let cb ← lowEns L b (d + 1)
        pure (bin2 o d ca cb)))
      (left : EnsCost L snapshot a d na Pa)
      (right : EnsCost L snapshot b (d + 1) nb Pb)
      (values : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r)
      (opcode : op o = bin g) (byte : o < 256) :
      EnsCost L snapshot e d (na + nb + 1) P

/-- Addition exposes the real compiler equation and its machine opcode. -/
def EnsCost.add {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    {snapshot : W} {d na nb : Nat} {Pa Pb : W → Prop}
    (left : EnsCost L snapshot a d na Pa)
    (right : EnsCost L snapshot b (d + 1) nb Pb) :
    EnsCost L snapshot (.add a b) d (na + nb + 1)
      (fun r => ∃ wa wb, Pa wa ∧ Pb wb ∧ r = wa + wb) :=
  .binary rfl left right
    (fun wa wb ha hb => ⟨wa + wb, rfl, wa, wb, ha, hb, rfl⟩) rfl (by decide)

/-- A nested source tree exercises both recursive children. -/
theorem ensCost_recursive_zeuge {D : Deklaration} (L : Lay D) (snapshot : W) :
    Nonempty (EnsCost L (Γ := []) (Λ := []) snapshot
      (.add (.add (.lit 2) (.lit 3)) (.lit 4)) 4 5
      (fun r => ∃ wa wb,
        (∃ x y, x = BitVec.ofInt 64 2 ∧ y = BitVec.ofInt 64 3 ∧ wa = x + y) ∧
        wb = BitVec.ofInt 64 4 ∧ r = wa + wb)) :=
  ⟨EnsCost.add (EnsCost.add (.ordinary rfl .literal) (.ordinary rfl .literal))
    (.ordinary rfl .literal)⟩

/-- Count emitted postcondition instructions recursively while preserving the
    frame. In particular the second child reads the original header snapshot. -/
theorem EnsCost.sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {d n : Nat} {P : W → Prop} {snapshot : W}
    (certificate : EnsCost L snapshot e d n P)
    {code : List II} {top K : Nat} {m : Mem} {pc fp : W}
    {ρ : Env D Γ} {World : Mem → Prop}
    (lower : lowEns L e d = some (code, top)) (fits : top ≤ K)
    (pre : Pre L m pc fp K d code ρ World)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot) :
    CountedOk n m pc fp K d code P := by
  induction certificate generalizing code top K m pc with
  | ordinary equation body => exact body.sound (equation ▸ lower) fits pre
  | @captured τ e d equation =>
    rw [equation] at lower
    cases lower
    have ctx := pre.ctx
    have base : FB = 4 := rfl
    simp only [frei] at ctx
    obtain ⟨hw, rd, agree⟩ := wr_slot pre.frame (d := d) (by omega) snapshot
    exact ⟨_, mov_to_counted (s := 3) (j := d) pre.code pre.frame (by omega) (by omega) pre.small read,
      agree, _, rd, rfl⟩
  | binary equation left right values opcode byte ihA ihB =>
    rw [equation] at lower
    simp only [bind, Option.bind_eq_some_iff] at lower
    obtain ⟨⟨ca, ta⟩, ha, ⟨⟨cb, tb⟩, hb, out⟩⟩ := lower
    cases out
    have fitA : ta ≤ K := Nat.le_trans (Nat.le_max_left _ _) fits
    have fitB : tb ≤ K := Nat.le_trans (Nat.le_max_right _ _) fits
    have room := lowEns_top _ _ cb tb hb
    have ctx := pre.ctx
    have base : FB = 4 := rfl
    simp only [frei] at ctx
    have hp := pre
    change Pre L m pc fp K _ (ca ++ cb ++ [ci _ _ _ _]) ρ World at hp
    apply bin_counted_keep (ihA ha fitA hp.left.left read) _ values opcode byte (by omega) hp
    intro m' pc' agree next
    apply ihB hb fitB next
    rw [agree_rd_low agree pre.frame.room (by omega) (by omega)]
    exact read

namespace OldProbe
/-- The certificate executes a real captured entry value, distinct from the
    current global cell, through the existing postcondition compiler. -/
theorem ensCost_sound_zeuge :
    CountedOk 1 (memory readCode) 0 1024 16 4 readCode
      (· = BitVec.ofNat 64 64) := by
  apply EnsCost.sound (L := layout) (e := expr)
    (EnsCost.captured rfl) (top := 5) rfl (by decide) read_pre
  decide +kernel
end OldProbe

/-- Normal return costs come from the actual postcondition certificate and
    four ABI instructions. The input result is copied before ensures runs;
    snapshot and caller header reads are preserved by frame agreement. -/
theorem retC_counted {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {e : Expr D (τ :: Γ) Λ .bool} {v : Wert D τ} {snapshot w : W} {n lo r top K : Nat}
    {ens : List II} {m : Mem} {pc fp rp cfp : W} {ρ : Env D Γ}
    (certificate : EnsCost L snapshot e (lo + 1) n (· = 1))
    (lower : lowEns L e (lo + 1) = some (ens, top)) (fits : top ≤ K)
    (pre : PreS L m pc fp K lo (retC lo r ens) ρ)
    (abi : 3 < lo) (room : lo + 1 < K) (resultSlot : r < K)
    (resultBase : lo = frei Γ) (encoded : Enc L τ v w)
    (value : m.rd64 (slot fp (BitVec.ofNat 64 r)) = some w)
    (entry : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp) :
    ∃ m', Counted (1 + n + 3) ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 1 ∧ Agree fp 2 K m m' := by
  have hp : PreS L m pc fp K lo
      ([ci 2 lo r 0] ++ (ens ++
        ([ci 19 ((lo + 1 : Nat) : Int) 48 0, ci 2 2 lo 0, ci 21 0 0 0] ++ stopC 102 (lo + 1)))) ρ := by
    simpa [retC, List.append_assoc] using pre
  have first := mov_to_counted hp.left.code hp.frame (j := lo) (s := r)
    (by omega) resultSlot hp.small value
  let m1 := write m (slot fp (BitVec.ofNat 64 lo)) 8 w.toNat
  have a1 : Agree fp lo K m m1 := agree_write hp.frame.room (by omega) (by omega) _
  have next := hp.next a1 (Nat.le_refl _) (by omega)
  have postPre : PreS L m1 (pc + 16) fp K (lo + 1) ens (.cons v ρ) := by
    refine ⟨?_, next.small, next.frame, next.left.code, next.left.far,
      ?_, trivial, wstab_true _ _⟩
    · simp only [frei, List.length_cons]; simp only [frei] at resultBase; omega
    · apply envAt_cons next.env
      · rw [← resultBase]; exact rd_same hp.frame (by omega) w
      · exact encoded
  have snap : m1.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot := by
    rw [agree_rd_low a1 hp.frame.room abi (by omega)]; exact entry
  obtain ⟨m2, post, a2, flag, flagRead, flagValue⟩ :=
    certificate.sound lower fits postPre snap
  subst flag
  have tailPre := next.next (a2.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  have resultRead : m2.rd64 (slot fp (BitVec.ofNat 64 lo)) = some w := by
    rw [agree_rd_low a2 hp.frame.room (by omega) (by omega)]
    exact rd_same hp.frame (by omega) w
  have all := a1.trans (a2.mono (Nat.le_succ _))
  have rpc : m2.rd64 fp = some rp := by
    have h := agree_rd_low (i := 0) all hp.frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedPC)
  have rfp : m2.rd64 (fp + 8) = some cfp := by
    have h := agree_rd_low (i := 1) all hp.frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedFP)
  obtain ⟨m3, last, a3, result, normal⟩ := returnTail_counted
    tailPre.left.code tailPre.left.far tailPre.frame tailPre.small
    (by omega) room flagRead resultRead rpc rfp
  exact ⟨m3, (first.trans post).trans last, result, normal, (all.mono (by omega)).trans a3⟩

/-- A source result certificate and an actual ensures certificate compose
    through the emitted normal-return code. Parameter and lexical environments
    are separate: relocated locals cannot replace the original ensures inputs. -/
theorem normalRet_counted {Γ Δ : Ctx} {Λ Ξ : List (Res D)} {τ : Ty}
    {e : Expr D Γ Λ τ} {q : Expr D (τ :: Δ) Ξ .bool} {v : Wert D τ}
    {snapshot : W} {ne nq d lo te tq K : Nat} {ce cq : List II}
    {m : Mem} {pc fp rp cfp : W} {ρ : Env D Γ} {parameters : Env D Δ}
    (result : ExprCost L reserved e d ne (Enc L τ v))
    (ensures : EnsCost L snapshot q (lo + 1) nq (· = 1))
    (lowerResult : lowE L (reserved := reserved) e d = some (ce, te))
    (lowerEnsures : lowEns L q (lo + 1) = some (cq, tq))
    (fitResult : te ≤ K) (fitEnsures : tq ≤ K)
    (pre : PreS L m pc fp K d (ce ++ retC lo d cq) ρ reserved)
    (parameterEnv : EnvAt L m fp parameters)
    (base : lo = frei Δ) (separate : lo ≤ d)
    (abi : 3 < lo) (room : lo + 1 < K)
    (entry : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp) :
    ∃ m' w', Counted (ne + (1 + nq + 3)) ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w' ∧
      Enc L τ v w' ∧ m'.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 1 ∧ Agree fp 2 K m m' ∧
      FrameOK m' fp K ∧ m'.rd64 fp = some rp ∧ m'.rd64 (fp + 8) = some cfp ∧
      (∀ σ, LayIn L → fp.toNat + 8 * K ≤ L.lo → WeltAt m L σ → WeltAt m' L σ) := by
  have resultRoom := lowE_top _ _ _ _ lowerResult
  obtain ⟨m1, run, agree, w, read, encoded⟩ := result.sound lowerResult fitResult pre.left
  have next := pre.next agree (Nat.le_refl _) (by omega)
  have retPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K lo
      (retC lo d cq) parameters :=
    ⟨by omega, next.small, next.frame, next.code, next.far,
      envAt_agree parameterEnv agree pre.frame (by omega) (by omega),
      trivial, wstab_true _ _⟩
  have snap : m1.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot := by
    rw [agree_rd_low agree pre.frame.room (by omega) (by omega)]; exact entry
  have rpc : m1.rd64 fp = some rp := by
    have h := agree_rd_low (i := 0) agree pre.frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedPC)
  have rfp : m1.rd64 (fp + 8) = some cfp := by
    have h := agree_rd_low (i := 1) agree pre.frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedFP)
  obtain ⟨m2, tail, value, flag, tailAgree⟩ := retC_counted ensures lowerEnsures fitEnsures
    retPre abi room (by omega) base encoded read snap rpc rfp
  have all : Agree fp 2 K m m2 := (agree.mono (by omega)).trans tailAgree
  have finalPC : m2.rd64 fp = some rp := by
    have h := agree_rd_low (i := 0) all pre.frame.room (by decide) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedPC)
  have finalFP : m2.rd64 (fp + 8) = some cfp := by
    have h := agree_rd_low (i := 1) all pre.frame.room (by decide) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedFP)
  exact ⟨m2, w, run.trans tail, value, encoded, flag, all, pre.frame.agree all, finalPC, finalFP,
    fun σ lay bound initial => weltAt_stab lay bound m m2 initial (all.mono (by decide))⟩

namespace NormalReturnProbe
open FnptrProben

def image : List II := retC 4 6 [ci 1 5 1 0]
def memory : Mem :=
  let base : Mem := {
    b := fun a => ((image.flatMap encII)[a.toNat]?).getD 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write (write (write base 4096 8 2048) 4104 8 8192) 4120 8 64) 4144 8 37

/-- Actual ensures lowering, result move and ABI return hold jointly, with
    nonzero result, saved snapshot and distinct caller PC and frame. -/
theorem retC_counted_zeuge :
    ∃ m', Counted 5 ⟨0, 4096⟩ memory ⟨2048, 8192⟩ m' ∧
      m'.rd64 4112 = some 37 ∧ m'.rd64 4136 = some 1 ∧ Agree 4096 2 16 memory m' := by
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout memory 0 4096 16 4 image (Env.nil : Env FnptrProben.D []) :=
    ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      code, by unfold CodeFar; decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  exact retC_counted (e := Expr.tru (Λ := [])) (snapshot := 64)
    (.ordinary rfl .truth) rfl (by decide) pre (by decide) (by decide)
    (by decide) rfl (show Enc callLayout (.int 37 37) ⟨37, by decide, by decide⟩ 37 from rfl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
end NormalReturnProbe

namespace SourceReturnProbe
open FnptrProben

def image : List II := [ci 1 6 37 0] ++ retC 4 6 [ci 1 5 1 0]
def memory : Mem :=
  let base : Mem := {
    b := fun a => ((image.flatMap encII)[a.toNat]?).getD 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write (write (write base 4096 8 2048) 4104 8 8192) 4120 8 64) 4144 8 37

/-- Actual ensures lowering, result move and ABI return hold jointly, with
    nonzero result, saved snapshot and distinct caller PC and frame. -/
theorem normalRet_counted_zeuge :
    ∃ m' w, Counted 6 ⟨0, 4096⟩ memory ⟨2048, 8192⟩ m' ∧
      m'.rd64 4112 = some w ∧
      Enc callLayout (.int 37 37) ⟨37, by decide, by decide⟩ w ∧ m'.rd64 4136 = some 1 ∧ Agree 4096 2 16 memory m' ∧ FrameOK m' 4096 16 := by
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout memory 0 4096 16 6 image (Env.nil : Env FnptrProben.D []) :=
    ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      code, by unfold CodeFar; decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  obtain ⟨mout, wout, run, read, enc, flag, agree, frame, finalPC, finalFP, world⟩ := normalRet_counted (Δ := []) (reserved := 0) (parameters := Env.nil)
    (v := (⟨37, by decide, by decide⟩ : Wert FnptrProben.D (.int 37 37)))
    (rp := 2048) (cfp := 8192) (ne := 1) (nq := 1)
    (e := Expr.lit (Λ := []) 37)
    (q := Expr.tru (Λ := [])) (snapshot := 64)
    (.literal) (.ordinary rfl .truth) rfl rfl (by decide) (by decide)
    pre (fun _ x => nomatch x) rfl (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨mout, wout, run, read, enc, flag, agree, frame⟩
end SourceReturnProbe

/-- Execute the actual reason-return ABI, including both writes and `ret`. -/
theorem returnWhy_counted {m : Mem} {pc fp rp cfp : W} {K lo r : Nat}
    (code : CodeAt m pc (retWhyC lo r)) (far : CodeFar pc 3 fp K)
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (abi : 2 < lo) (room : lo + 1 < K) (reason : r < 2 ^ 31)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp) :
    ∃ m', Counted 3 ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 0 ∧
      m'.rd64 (slot fp 2) = some (BitVec.ofNat 64 r) := by
  have first := const_step_counted (codeAt_left (a := [ci 1 2 r 0]) code)
    frame (j := 2) (k := r) (by omega) small (by simp [lit32]; omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 2)) 8 (BitVec.ofInt 64 (r : Int)).toNat
  have a1 : Agree fp 2 K m m1 := agree_write frame.room (by omega) (by omega) _
  have far1 := codeFar_tail (a := [ci 1 2 r 0]) (b := [ci 1 (lo + 1) 0 0, ci 21 0 0 0]) far
  have code1 := (codeAt_right (a := [ci 1 2 r 0]) code).agree a1 far1
  have frame1 := frame.agree a1
  have second := const_step_counted (codeAt_left (a := [ci 1 (lo + 1) 0 0]) code1)
    frame1 (j := lo + 1) (k := 0) room small (by decide)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (lo + 1))) 8 0
  have a2 : Agree fp 2 K m1 m2 := (agree_write (lo := lo + 1) frame1.room (by omega) room 0).mono (by omega)
  have far2 := codeFar_tail (a := [ci 1 (lo + 1) 0 0]) (b := [ci 21 0 0 0]) far1
  have code2 := (codeAt_right (a := [ci 1 (lo + 1) 0 0]) code1).agree a2 far2
  have ins := code2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ins
  have rpc : m2.rd64 fp = some rp := by
    have h := agree_rd_low (i := 0) (a1.trans a2) frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedPC)
  have rfp : m2.rd64 (fp + 8) = some cfp := by
    have h := agree_rd_low (i := 1) (a1.trans a2) frame.room (by omega) (by omega)
    simpa [slot] using h.trans (by simpa [slot] using savedFP)
  have last : Counted 1 ⟨pc + 16 + 16, fp⟩ m2 ⟨rp, cfp⟩ m2 :=
    .next (run_step ins (by decide) (run_ret rpc rfp)) (.refl _ _)
  refine ⟨m2, (first.trans (by simpa [m1, m2] using second)).trans last, a1.trans a2, ?_⟩
  refine ⟨rd_same frame1 room 0, ?_⟩
  have keep := agree_write (m := m1) (lo := lo + 1) frame1.room (by omega) room 0
  have read := agree_rd_low (i := 2) keep frame1.room (by omega) (by omega)
  change m2.rd64 (slot fp 2) = _ at read
  rw [read]
  simpa [m1] using rd_same frame (a := 2) (by omega) (BitVec.ofInt 64 (r : Int))

/-- Recursive terminal certificates. Counts are S0IR instructions, independent
    of source passes and G steps. The bases execute normal and reason returns; prefixes
    recursively derive costs from expressions and the changed environment. -/
inductive EndCost (L : Lay D) (reserved : Nat) (V : Vertrag D) (l : Bool) (Δ : Ctx) (snapshot : W) (ens : List II × Nat) (lo : Nat) :
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ →
      World D → Env D Γ → Nat → Type
  | reason {Γ : Ctx} {Λ : List (Res D)} {σ : World D} {ρ : Env D Γ} {r : Fin V.gruende} {proof : Λ.Perm V.ende} :
      EndCost L reserved V l Δ snapshot ens lo (.retWhy r proof) σ ρ 3
  | normal {Γ Λ τ} {e : Expr D Γ Λ τ} {σ : World D} {ρ : Env D Γ}
      {v : Wert D τ} {ne nq : Nat} {Ξ : List (Res D)}
      {q : Expr D (τ :: Δ) Ξ .bool}
      (typed : V.erg = some τ) (proof : Λ.Perm V.ende)
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (post : EnsCost L snapshot q (lo + 1) nq (· = 1))
      (lowerPost : lowEns L q (lo + 1) = some ens) :
      EndCost L reserved V l Δ snapshot ens lo
        (.ret (typed.symm ▸ ErgExpr.val e) proof) σ ρ (ne + (1 + nq + 3))
  | assign {Γ Λ τ} {x : Var Γ τ} {e : Expr D Γ Λ τ}
      {rest : Endblock D V l Γ Λ} {σ : World D} {ρ : Env D Γ}
      {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : EndCost L reserved V l Δ snapshot ens lo rest σ (ρ.set x v) nr) :
      EndCost L reserved V l Δ snapshot ens lo (.cons (.assignVar x e) rest) σ ρ (ne + 1 + nr)
  | bind {Γ Λ τ} {e : Expr D Γ Λ τ} {rest : Endblock D V l (τ :: Γ) Λ}
      {σ : World D} {ρ : Env D Γ} {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : EndCost L reserved V l Δ snapshot ens lo rest σ (.cons v ρ) nr) :
      EndCost L reserved V l Δ snapshot ens lo (.bind e rest) σ ρ (ne + nr)

  | branch {Γ Λ} {c : Expr D Γ Λ .bool} {t e : Endblock D V l Γ Λ}
      {σ : World D} {ρ : Env D Γ} {choice : Bool} {nc nb : Nat}
      (condition : ExprCost L reserved c (frei Γ reserved) nc
        (· = if choice then 1 else 0))
      (jumpFits : ∀ passes A pr ex ct tt,
        lowEnd (reserved := reserved) passes A L lo ens pr ex t = some (ct, tt) →
        16 * (ct.length + 1) < 2 ^ 31)
      (child : EndCost L reserved V l Δ snapshot ens lo
        (if choice then t else e) σ ρ nb) :
      EndCost L reserved V l Δ snapshot ens lo (.ite c t e) σ ρ (nc + 1 + nb)

/-- The source certificate determines the returned value and status at the counted endpoint. -/
def EndCost.Post {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n)
    (fp : W) (m : Mem) : Prop :=
  match certificate with
  | .reason (r := r) =>
      m.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 0 ∧
      m.rd64 (slot fp 2) = some (BitVec.ofNat 64 r.val)
  | .normal (v := v) _ _ _ _ _ =>
      ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ Enc L _ v w ∧
        m.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) = some 1
  | .assign _ tail => tail.Post fp m
  | .bind _ tail => tail.Post fp m
  | .branch _ _ child => child.Post fp m

/-- Preserve the complete source exit, including the reason identity. -/
def EndCost.outcome {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n) :
    Ausgang V l Γ :=
  match certificate with
  | .reason (r := r) => .why σ r
  | .normal (v := v) typed _ _ _ _ => .zurueck σ (typed.symm ▸ v)
  | .assign _ tail => tail.outcome
  | .bind _ tail => tail.outcome.schrumpf
  | .branch _ _ child => child.outcome

/-- Erase only the return type index, retaining its typed value. -/
def terminalValue : (type : Option Ty) → ErgVal D type → Option ((τ : Ty) × Wert D τ)
  | none, _ => none
  | some τ, v => some ⟨τ, v⟩

@[simp] theorem terminalValue_cast {type : Option Ty} {τ : Ty}
    (h : type = some τ) (v : Wert D τ) :
    terminalValue type (h.symm ▸ v) = some ⟨τ, v⟩ := by
  cases h
  rfl

/-- The optional payload is an observation of the canonical outcome. -/
def terminalResult {V : Vertrag D} {l Γ} (outcome : Ausgang V l Γ) :
    Option ((τ : Ty) × Wert D τ) :=
  match outcome with
  | .zurueck _ v => terminalValue V.erg v
  | _ => none

@[simp] theorem terminalResult_shrink {V : Vertrag D} {l Γ τ}
    (outcome : Ausgang V l (τ :: Γ)) :
    terminalResult outcome.schrumpf = terminalResult outcome := by
  cases outcome <;> rfl

/-- Observe a reason without erasing its identity. -/
def terminalReason {V : Vertrag D} {l Γ} (outcome : Ausgang V l Γ) :
    Option (Fin V.gruende) :=
  match outcome with
  | .why _ r => some r
  | _ => none

@[simp] theorem terminalReason_shrink {V : Vertrag D} {l Γ τ}
    (outcome : Ausgang V l (τ :: Γ)) :
    terminalReason outcome.schrumpf = terminalReason outcome := by
  cases outcome <;> rfl

/-- Reason identity is read at the actual counted return endpoint. -/
theorem EndCost.reason_read {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n)
    {r : Fin V.gruende} (result : terminalReason certificate.outcome = some r)
    {fp : W} {m : Mem} (post : certificate.Post fp m) :
    m.rd64 (slot fp 2) = some (BitVec.ofNat 64 r.val) := by
  induction certificate with
  | reason => cases result; exact post.2
  | normal => cases result
  | assign value tail ih => exact ih result post
  | bind value tail ih =>
    exact ih (by simpa only [outcome, terminalReason_shrink] using result) post
  | branch condition jumpFits child ih => exact ih result post

/-- The old payload observation is derived from the complete canonical exit. -/
def EndCost.result {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n) :
    Option ((τ : Ty) × Wert D τ) := terminalResult certificate.outcome

@[simp] theorem EndCost.outcome_result {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n) :
    terminalResult certificate.outcome = certificate.result := rfl

/-- A computed normal result is read at the very same endpoint as the cost proof. -/
theorem EndCost.result_read {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n)
    {τ : Ty} {v : Wert D τ} (result : certificate.result = some ⟨τ, v⟩)
    {fp : W} {m : Mem} (post : certificate.Post fp m) :
    ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ Enc L τ v w := by
  induction certificate with
  | reason => cases result
  | normal typed =>
    cases V
    cases typed
    simp only [EndCost.result, EndCost.outcome, terminalResult, terminalValue, Option.some.injEq] at result
    cases result
    exact ⟨post.choose, post.choose_spec.1, post.choose_spec.2.1⟩
  | assign value tail ih => exact ih result post
  | bind value tail ih => exact ih (by simpa only [EndCost.result, EndCost.outcome, terminalResult_shrink] using result) post
  | branch condition jumpFits child ih => exact ih result post

/-- Normal and reason status belongs to the same endpoint as the result read. -/
theorem EndCost.result_status {Δ snapshot ens lo V l Γ Λ b σ ρ n}
    (certificate : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n)
    {fp : W} {m : Mem} (post : certificate.Post fp m) :
    m.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) =
      some (if certificate.result.isSome then 1 else 0) := by
  induction certificate with
  | reason => exact post.1
  | normal typed =>
    cases V
    cases typed
    exact post.choose_spec.2.2
  | assign value tail ih => exact ih post
  | bind value tail ih =>
    change m.rd64 _ = some (if (terminalResult tail.outcome.schrumpf).isSome then (1 : W) else 0)
    rw [terminalResult_shrink]
    exact ih post
  | branch condition jumpFits child ih => exact ih post

/-- Removing a bound local retains every canonical exit, including pending stops. -/
theorem CountedSim.shrink {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp : W} {l : Bool} {Γ : Ctx} {τ : Ty}
    {n lo K : Nat} {pr : List Nat} {t : T} {m : Mem} {e eL eN : W}
    {outcome : Ausgang (vertragVon D f) l (τ :: Γ)}
    (h : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN outcome reserved) :
    CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN outcome.schrumpf reserved := by
  cases outcome with
  | ok σ ρ | next _ σ ρ | leave _ σ ρ =>
    obtain ⟨m', run, agree, env, world, keep⟩ := h
    exact ⟨m', run, agree, envAt_tail env, world, keep⟩
  | zurueck _ _ | why _ _ | logik _ | hardware _ => exact h

/-- Convert observations at one actual caller endpoint to the canonical simulation.
    The semantic ensures obligation is explicit; an instruction-level true flag
    alone does not establish the source postcondition. -/
theorem EndCost.post_countedSim
    {P : Programm D} {f : D.Fn} {l Γ Λ Δ snapshot ens lo b σ ρ budget}
    (certificate : EndCost L reserved (vertragVon D f) l Δ snapshot ens lo
      (Γ := Γ) (Λ := Λ) b σ ρ budget)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {k K : Nat}
    {fp rp cfp e eL eN : W} {pr : List Nat} {t : T} {m m' : Mem}
    (run : Counted k t m ⟨rp, cfp⟩ m')
    (agree : AgreeW L fp 2 K m m')
    (world : WeltAt m' L σ)
    (post : certificate.Post fp m')
    (base : lo = FB + (D.params f).length)
    (ensures : ∀ σ' v, certificate.outcome = .zurueck σ' v →
      wahr? (eval σ0 (P.ensures f)
        (σ'.lese (vertragVon D f).ende (P.ensures f).orte)
        (ergEnv (D.erg f) v ρ0)) ≠ false) :
    CountedSim k L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN
      certificate.outcome reserved := by
  induction certificate with
  | reason =>
    exact ⟨m', run, agree, post.2, by simpa [ReturnFlag, base] using post.1, world⟩
  | @normal Γ Λ τ e σ ρ v ne nq Ξ q typed proof value cost lower =>
    simp only [CountedSim, EndCost.outcome, CountedRetZ]
    rw [if_neg (ensures _ _ rfl)]
    obtain ⟨w, read, enc, flag⟩ := post
    refine ⟨m', run, agree, ⟨w, read, ?_, ?_⟩, world⟩
    · change EncErg L (vertragVon D f).erg (typed.symm ▸ v) w
      have cast : ∀ {rt : Option Ty} (h : rt = some τ),
          EncErg L rt (h.symm ▸ v) w := by
        intro rt h
        cases h
        exact enc
      exact cast typed
    · simpa [ReturnFlag, base] using flag
  | assign value tail ih => exact ih world post ensures
  | bind value tail ih =>
    have child := ih world post (by
      intro σ' v eq
      apply ensures σ' v
      change tail.outcome.schrumpf = _
      rw [eq]
      rfl)
    exact CountedSim.shrink child
  | branch condition jumpFits child ih => exact ih world post ensures

/-- Structural induction discharges recursive terminal executions. No complete
    body execution or complete body cost is a premise. ABI reads are preserved
    across each prefix by the existing frame agreement theorems. -/
theorem EndCost.sound {Δ : Ctx} {snapshot : W} {ens : List II × Nat} {lo : Nat} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {b : Endblock D V l Γ Λ} {σ : World D} {ρ : Env D Γ} {n : Nat}
    (certificate : EndCost L reserved V l Δ snapshot ens lo b σ ρ n)
    {passes K Ks top : Nat} {A : D.Fn → Nat}
    {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp rp cfp : W}
    (lower : lowEnd (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (abi : 3 < lo) (lowBound : lo ≤ K)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ)
    (parameters : Env D Δ) (parameterEnv : EnvAt L m fp parameters)
    (base : lo = frei Δ)
    (entry : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp) :
    ∃ m', Counted n ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧ certificate.Post fp m' ∧ AgreeW L fp 2 K m m' ∧
      FrameOK m' fp K ∧ m'.rd64 fp = some rp ∧ m'.rd64 (fp + 8) = some cfp ∧ WeltAt m' L σ := by
  have hks := inside.ks
  induction certificate generalizing top code m pc ex with
  | reason =>
    simp only [lowEnd] at lower
    split at lower
    next accepted =>
      cases lower
      obtain ⟨m', run, agree, flag⟩ := returnWhy_counted pre.code pre.far pre.frame pre.small (by omega)
        (by simp only [retTop] at fits; have := inside.ks; omega) accepted savedPC savedFP
      refine ⟨m', run, flag, agreeW_of agree, pre.frame.agree agree, ?_, ?_, ?_⟩
      · have h := agree_rd_low (i := 0) agree pre.frame.room (by decide) (by omega)
        simpa [slot] using h.trans (by simpa [slot] using savedPC)
      · have h := agree_rd_low (i := 1) agree pre.frame.room (by decide) (by omega)
        simpa [slot] using h.trans (by simpa [slot] using savedFP)
      · exact weltAt_stab inside.lay (by have := inside.top; omega) m m' world (agree.mono (by decide))
    next refused => simp at lower
  | @normal Γ Λ τ e σ ρ v ne nq Ξ q typed proof value post lowerPost =>
    have herg : ∀ {rt : Option Ty} (h : rt = some τ),
        lowErg L (h.symm ▸ ErgExpr.val e) (frei Γ reserved) reserved =
          lowE L e (frei Γ reserved) reserved := by
      intro rt h
      cases h
      rfl
    simp only [lowEnd, herg typed, Bind.bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at lower
    obtain ⟨⟨ce, te⟩, he, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    obtain ⟨m', w, run, read, enc, flag, agree, frame, rpc, rfp, hw⟩ := normalRet_counted value post he lowerPost
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) fits) inside.ks)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) fits)) inside.ks)
      pre parameterEnv base low abi
      (by simp only [retTop] at fits; omega) entry savedPC savedFP
    exact ⟨m', run, ⟨w, read, enc, flag⟩, agreeW_of agree, frame, rpc, rfp, hw σ inside.lay (by have := inside.top; omega) world⟩
  | assign value tail ih =>
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    obtain ⟨m1, run1, agree1, env1, world1, keep1⟩ :=
      countedAssignVar_case value hs (Nat.le_trans (Nat.le_max_left _ _) fits)
        inside low hprotected pre.left world
    have far := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
    have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K
        (frei _ reserved) cr _ reserved :=
      ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame agree1,
        codeAt_agreeWIn inside agree1 (codeAt_right pre.code) far,
        far, env1, trivial, wstab_true _ _⟩
    have hK : lo ≤ K := lowBound
    have rpc : m1.rd64 fp = some rp := by
      have h := agreeW_rdW inside agree1 (i := 0) (by omega) hK
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : m1.rd64 (fp + 8) = some cfp := by
      have h := agreeW_rdW inside agree1 (i := 1) (by omega) hK
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨m2, run2, post, finalAgree, frame, rpc, rfp, hw⟩ := ih hr (Nat.le_trans (Nat.le_max_right _ _) fits)
      low hprotected nextPre world1
      (envAt_agreeWIn inside parameterEnv agree1 (by omega) lowBound)
      (by rw [agreeW_rdW inside agree1 (i := 3) (by omega) lowBound]; exact entry) rpc rfp
    exact ⟨m2, run1.trans run2, post, (agree1.mono (by omega)).trans finalAgree, frame, rpc, rfp, hw⟩
  | @bind Γ Λ τ e rest σ ρ v ne nr value tail ih =>
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have room := lowE_top _ _ _ _ he
    have hpw := PreS.welt pre.left inside.ks world inside.lay (by have := inside.lo; omega)
    obtain ⟨m1, run1, a1s, w, read, encoded⟩ :=
      value.sound he (Nat.le_trans (Nat.le_max_left _ _) fits) hpw
    have a1 := Agree.widen a1s inside.ks
    have far := codeFar_right (n := ce.length) (k := cr.length) (by simpa using pre.far)
    have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K
        (frei Γ reserved + 1) cr (Env.cons v ρ) reserved :=
      ⟨by simp only [frei, List.length_cons]; omega, pre.small, pre.frame.agree a1,
        (codeAt_right pre.code).agree a1 far, far,
        envAt_cons (envAt_agree pre.env a1 pre.frame (Nat.le_refl _) (by omega)) read encoded,
        trivial, wstab_true _ _⟩
    have rpc : m1.rd64 fp = some rp := by
      have h := agree_rd_low (i := 0) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : m1.rd64 (fp + 8) = some cfp := by
      have h := agree_rd_low (i := 1) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨m2, run2, post, finalAgree, frame, rpc, rfp, hw⟩ := ih hr (Nat.le_trans (Nat.le_max_right _ _) fits)
      (by simp only [frei, List.length_cons] at low ⊢; omega)
      (fun j hj => by have := hprotected j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      nextPre (hpw.wstab m m1 world (a1s.mono (Nat.zero_le _)))
      (envAt_agree parameterEnv a1 pre.frame (by omega) (by omega))
      (by rw [agree_rd_low a1 pre.frame.room (by omega) (by omega)]; exact entry) rpc rfp
    exact ⟨m2, run1.trans run2, post, (agreeW_of (a1.mono (by omega))).trans finalAgree, frame, rpc, rfp, hw⟩

  | @branch Γ Λ c t e σ ρ choice nc nb condition jumpFits child ih =>
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cc, tc⟩, hc, ⟨ce, te⟩, he, ⟨ct, tt⟩, ht, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have room := lowE_top _ _ _ _ hc
    have hq : PreS L m pc fp K (frei Γ reserved)
        (cc ++ ([ci 19 (frei Γ reserved) (16 * (ct.length + 1)) 0] ++ (ct ++ ce))) ρ reserved := by
      simpa [List.append_assoc] using pre
    have hpw := PreS.welt hq.left inside.ks world inside.lay (by have := inside.lo; omega)
    obtain ⟨m1, run1, a1s, w, read, value⟩ := condition.sound hc (by omega) hpw
    have a1 := Agree.widen a1s inside.ks
    have h1 := hq.next a1 (Nat.le_refl _) (by omega)
    have h2 := h1.next (a := [ci 19 (frei Γ reserved) (16 * (ct.length + 1)) 0])
      (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have ins := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
    have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
      sx_nat (by have := pre.small; omega)
    have world1 := hpw.wstab m m1 world (a1s.mono (Nat.zero_le _))
    have params1 := envAt_agree parameterEnv a1 pre.frame (by omega) (by omega)
    have entry1 : m1.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot := by
      rw [agree_rd_low a1 pre.frame.room (by omega) (by omega)]; exact entry
    have rpc : m1.rd64 fp = some rp := by
      have h := agree_rd_low (i := 0) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : m1.rd64 (fp + 8) = some cfp := by
      have h := agree_rd_low (i := 1) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    cases choice with
    | true =>
      simp only [Bool.true_eq, ↓reduceIte] at value child ih
      subst w
      have sb := counted_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne ins (by rw [hd]; exact read) (by decide))
      obtain ⟨m2, run2, post, agree, frame, rpc, rfp, hw⟩ :=
        ih ht (by omega) low hprotected h2.left world1 params1 entry1 rpc rfp
      have run : Counted (nc + (1 + nb)) ⟨pc, fp⟩ m ⟨rp, cfp⟩ m2 := by
        refine run1.trans (sb.trans ?_)
        simpa [List.length_singleton, pc_add, addr_norm] using run2
      exact ⟨m2, by simpa only [Nat.add_assoc] using run, post,
        (agreeW_of (a1.mono (by omega))).trans agree, frame, rpc, rfp, hw⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at value child ih
      subst w
      have step := run_step (t := ⟨_, fp⟩) ins (by decide)
        (run_brz_zero ins (by rw [hd]; exact read))
      have offset : sx (II.f (16 * ((ct.length : Int) + 1))) =
          BitVec.ofNat 64 (16 * (ct.length + 1)) := by
        have h := sx_nat (d := 16 * (ct.length + 1)) (jumpFits _ _ _ _ _ _ ht)
        simpa using h
      rw [offset] at step
      have sb := Counted.next step (Counted.refl _ _)
      have h4 := h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      obtain ⟨m2, run2, post, agree, frame, rpc, rfp, hw⟩ :=
        ih he (by omega) low hprotected h4 world1 params1 entry1 rpc rfp
      have run : Counted (nc + (1 + nb)) ⟨pc, fp⟩ m ⟨rp, cfp⟩ m2 := by
        refine run1.trans (sb.trans ?_)
        simpa [List.length_singleton, pc_add, addr_norm, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run2
      exact ⟨m2, by simpa only [Nat.add_assoc] using run, post,
        (agreeW_of (a1.mono (by omega))).trans agree, frame, rpc, rfp, hw⟩

/-- Actual source-derived terminal costs imply the canonical return simulation.
    This theorem covers the terminal forms admitted by EndCost; pending stops
    require their own source-derived certificates, not a caller-return premise. -/
theorem EndCost.terminalCountedSim {P : Programm D} {f : D.Fn} {Δ : Ctx} {snapshot : W} {ens : List II × Nat} {lo : Nat} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {b : Endblock D (vertragVon D f) l Γ Λ} {σ : World D} {ρ : Env D Γ} {n : Nat}
    (certificate : EndCost L reserved (vertragVon D f) l Δ snapshot ens lo b σ ρ n)
    {passes K Ks top : Nat} {A : D.Fn → Nat}
    {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp rp cfp : W}
    (lower : lowEnd (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (abi : 3 < lo) (lowBound : lo ≤ K)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ)
    (parameters : Env D Δ) (parameterEnv : EnvAt L m fp parameters)
    (base : lo = frei Δ)
    (entry : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {e eL eN : W}
    (abiBase : lo = FB + (D.params f).length)
    (ensures : ∀ σ' v, certificate.outcome = .zurueck σ' v →
      wahr? (eval σ0 (P.ensures f)
        (σ'.lese (vertragVon D f).ende (P.ensures f).orte)
        (ergEnv (D.erg f) v ρ0)) ≠ false) :
    CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m e eL eN
      certificate.outcome reserved := by
  obtain ⟨m', run, post, agree, frame, rpc, rfp, hw⟩ :=
    certificate.sound lower fits inside low abi lowBound hprotected pre world
      parameters parameterEnv base entry savedPC savedFP
  exact certificate.post_countedSim run agree hw post abiBase ensures

namespace EndCostProbe
open FnptrProben

def contract : Vertrag FnptrProben.D := { vertragVon FnptrProben.D 2 with gruende := 2 }
def body : Endblock FnptrProben.D contract false [] [] :=
  .bind (.lit 2) (.cons (.assignVar .here (.lit 2)) (.retWhy ⟨1, by decide⟩ (by decide)))
def image : List II :=
  [ci 1 4 2 0, ci 1 5 2 0, ci 2 4 5 0] ++ retWhyC 4 1
def memory : Mem :=
  let saved := write (write (write callMem 4096 8 2048) 4104 8 8192) 4120 8 64
  { saved with
  b := fun a => if a.toNat < 96 then
    ((image.flatMap encII)[a.toNat]?).getD 0 else saved.b a }

/-- Binding, assignment and terminal return satisfy all simulation premises
    jointly; the execution includes three prefix and three ABI instructions. -/
theorem endCost_sound_zeuge :
    ∃ m', Counted 6 ⟨0, 4096⟩ memory ⟨2048, 8192⟩ m' ∧
      m'.rd64 (slot 4096 2) = some 1 := by
  have lower : lowEnd 2 addresses callLayout 4 ([], 6) [] (0, 0) body =
      some (image, 13) := by decide +kernel
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout memory 0 4096 256 4 image (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt memory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  let v : Wert FnptrProben.D (.int 2 2) := ⟨2, by decide, by decide⟩
  let cert : EndCost callLayout 0 contract false [] 64 ([], 6) 4 body world .nil 6 :=
    .bind (v := v) .literal (.assign (v := v) .literal .reason)
  obtain ⟨mout, run, post, _⟩ := cert.sound (rp := 2048) (cfp := 8192) lower (by decide) call_win (by decide) (by decide) (by decide)
    (by intro j hj; cases hj) pre hw .nil (fun _ x => nomatch x) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨mout, run, cert.reason_read (r := ⟨1, by decide⟩) rfl post⟩

def branchChild : Endblock FnptrProben.D contract false [] [] :=
  .bind (.lit 2) (.retWhy ⟨0, by decide⟩ (by decide))
def branchChildImage : List II := [ci 1 4 2 0] ++ retWhyC 4 0
def branchBody (choice : Bool) : Endblock FnptrProben.D contract false [] [] :=
  .ite (if choice then .tru else .fls) branchChild branchChild
def branchImage (choice : Bool) : List II :=
  [ci 1 4 (if choice then 1 else 0) 0, ci 19 4 80 0] ++ branchChildImage ++ branchChildImage
def branchMemory (choice : Bool) : Mem :=
  { memory with b := fun a => if a.toNat < 160 then
      (((branchImage choice).flatMap encII)[a.toNat]?).getD 0 else memory.b a }

set_option maxHeartbeats 4000000 in
/-- Both actual branch directions compose with a nonempty lexical binding child. -/
theorem branch_sound_zeuge (choice : Bool) :
    ∃ m', Counted 6 ⟨0, 4096⟩ (branchMemory choice) ⟨2048, 8192⟩ m' := by
  have lower : lowEnd 2 addresses callLayout 4 ([], 6) [] (0, 0) (branchBody choice) =
      some (branchImage choice, 13) := by cases choice <;> decide +kernel
  have code : CodeAt (branchMemory choice) 0 (branchImage choice) := by
    have h : ∀ k : Fin (branchImage choice).length,
        (branchMemory choice).rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 (branchImage choice)[k.val].o) ∧
        (branchMemory choice).rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f (branchImage choice)[k.val].a) ∧
        (branchMemory choice).rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f (branchImage choice)[k.val].b) ∧
        (branchMemory choice).rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f (branchImage choice)[k.val].c) := by
      cases choice <;> apply allFin <;> decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout (branchMemory choice) 0 4096 256 4 (branchImage choice) (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; cases choice <;> decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt (branchMemory choice) callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    cases choice <;> decide +kernel
  let v : Wert FnptrProben.D (.int 2 2) := ⟨2, by decide, by decide⟩
  have leaf : EndCost callLayout 0 contract false [] 64 ([], 6) 4 branchChild world .nil 4 :=
    .bind (v := v) .literal .reason
  have cert : EndCost callLayout 0 contract false [] 64 ([], 6) 4
      (branchBody choice) world .nil 6 := by
    apply EndCost.branch (choice := choice) (nc := 1) (nb := 4)
    · cases choice
      · exact .falsity
      · exact .truth
    · intro passes A pr ex ct tt lower
      change some (branchChildImage, 13) = some (ct, tt) at lower
      cases lower
      decide
    · cases choice <;> exact leaf
  obtain ⟨mout, run, _⟩ := cert.sound (rp := 2048) (cfp := 8192) lower (by decide) call_win (by decide) (by decide) (by decide)
    (by intro j hj; cases hj) pre hw .nil (fun _ x => nomatch x) rfl (by cases choice <;> decide +kernel) (by cases choice <;> decide +kernel) (by cases choice <;> decide +kernel)
  exact ⟨mout, run⟩
end EndCostProbe

namespace NormalEndCostProbe
open FnptrProben

def contract : Vertrag FnptrProben.D := { vertragVon FnptrProben.D 2 with gruende := 1, erg := some (.int 37 37) }
def body : Endblock FnptrProben.D contract false [] [] :=
  .bind (.lit 37) (.cons (.assignVar .here (.lit 37)) (.ret (.val (.lit 37)) (by decide)))
def image : List II :=
  [ci 1 4 37 0, ci 1 5 37 0, ci 2 4 5 0, ci 1 5 37 0] ++ retC 4 5 [ci 1 5 1 0]
def memory : Mem :=
  let saved := write (write (write callMem 4096 8 2048) 4104 8 8192) 4120 8 64
  { saved with
  b := fun a => if a.toNat < 16 * image.length then
    ((image.flatMap encII)[a.toNat]?).getD 0 else saved.b a }

/-- Binding, assignment and terminal return satisfy all simulation premises
    jointly; the execution includes three prefix instructions followed by a six-instruction normal return. -/
theorem endCost_sound_zeuge :
    ∃ m', Counted 9 ⟨0, 4096⟩ memory ⟨2048, 8192⟩ m' ∧
      (∃ w, m'.rd64 4112 = some w ∧ Enc callLayout (.int 37 37)
        (⟨37, by decide, by decide⟩ : Wert FnptrProben.D (.int 37 37)) w ∧ m'.rd64 4136 = some 1) ∧
      FrameOK m' 4096 256 ∧ m'.rd64 4096 = some 2048 ∧
      m'.rd64 4104 = some 8192 ∧ WeltAt m' callLayout world := by
  have lower : lowEnd 2 addresses callLayout 4 ([ci 1 5 1 0], 6) [] (0, 0) body =
      some (image, 13) := by decide +kernel
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS callLayout memory 0 4096 256 4 image (Env.nil : Env FnptrProben.D []) := by
    refine ⟨by decide, by decide, ?_, code, ?_, ?_, trivial, wstab_true _ _⟩
    · exact ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    · unfold CodeFar; decide +kernel
    · intro _ x; nomatch x
  have hw : WeltAt memory callLayout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  let v : Wert FnptrProben.D (.int 37 37) := ⟨37, by decide, by decide⟩
  let cert : EndCost callLayout 0 contract false [] 64 ([ci 1 5 1 0], 6) 4 body world .nil 9 :=
    .bind (v := v) .literal (.assign (v := v) .literal
      (.normal (v := v) (q := Expr.tru (Λ := [])) rfl (by decide)
        .literal (.ordinary rfl .truth) rfl))
  obtain ⟨mout, run, post, _agree, frame, rpc, rfp, hw⟩ := cert.sound (rp := 2048) (cfp := 8192) lower (by decide) call_win (by decide) (by decide) (by decide)
    (by intro j hj; cases hj) pre hw .nil (fun _ x => nomatch x) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨mout, run, by simpa [cert, EndCost.Post, slot] using post, frame, rpc, rfp, hw⟩
end NormalEndCostProbe

/-- Successful full function execution derives its instruction count from
    recursive source certificates and the emitted entry phases. -/
theorem lowFun_counted {P : Programm D} {A : D.Fn → Nat} {L : Lay D} {f : D.Fn}
    {passes top Ks K nq nb declared : Nat} {code : List II}
    {σ : World D} {ρ : Env D (D.params f)} {m : Mem} {pc fp rp cfp depth : W}
    (lower : lowFun passes P A L f = some (code, top)) (fits : top ≤ Ks)
    (inside : WIn L fp Ks K)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, EndCost L ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ ρ nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    (pre : PreS L m pc fp K (FB + (D.params f).length) code ρ)
    (world : WeltAt m L σ) (savedPC : m.rd64 fp = some rp)
    (savedFP : m.rd64 (fp + 8) = some cfp)
    (depthRead : m.rd64 (slot fp 2) = some depth) (positive : depth ≠ 0) :
    ∃ n m', n ≤ declared ∧ Counted n ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
      (∃ ens, ∃ hens : lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens,
        ∃ snapshot, (body ens hens snapshot).Post fp m') ∧
      AgreeW L fp 2 K m m' ∧ FrameOK m' fp K ∧ m'.rd64 fp = some rp ∧ m'.rd64 (fp + 8) = some cfp ∧ WeltAt m' L σ := by
  have hks := inside.ks
  simp only [lowFun] at lower
  split at lower
  next accepted =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨⟨cq, tq⟩, hq, ens, hens, ⟨cb, tb⟩, hb, cs, hcs, hc, ht⟩ := lower
    subst code
    let s := FB + (D.params f).length
    let reserved := (D.params f).length + 2 + 2 * counterDepthE (P.rumpf f)
    have bounds := fits
    rw [← ht] at bounds
    simp only [frei] at bounds
    have hp : PreS L m pc fp K s
        (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ (cs ++
          (relocateC FB reserved (D.params f).length ++ cb))))) ρ := by
      simpa [s, reserved, List.append_assoc] using pre
    have first := guard_pass_counted hp.left.code (by decide) depthRead positive
    have hp1 := hp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have phases : PreS L m (pc + BitVec.ofNat 64 (16 * (guardC 2 105 s).length)) fp K s ((cq ++ guardC s 101 s) ++
        (cs ++ (relocateC FB reserved (D.params f).length ++ cb))) ρ := by
      simpa [List.append_assoc] using hp1
    have hpq := phases.left
    obtain ⟨m1, rq, a1, env1, _⟩ := requirement.guard hq (by omega) hpq
    have hf1 := hp.frame.agree a1
    have rest := phases.next a1 (Nat.le_refl _) (by omega)
    have world1 := weltAt_stab inside.lay (by have := inside.top; omega) m m1 world (a1.mono (Nat.zero_le _))
    obtain ⟨mS, rs, aS, snap, keep⟩ := snapC_counted hcs hf1 pre.small (by omega)
      rest.left.code rest.left.far world1 inside.lay (by have := inside.top; omega)
    have hfS := hf1.agree aS
    have envS : EnvAt L mS fp ρ := by
      intro τ x
      obtain ⟨w, hw, enc⟩ := env1 τ x
      exact ⟨w, (keep (vslot x) (by have := vslot_lt (reserved := 0) x; unfold frei at this; omega)
        (by unfold vslot FB; omega)).trans hw, enc⟩
    have farS := codeFar_tail rest.far
    have rem : PreS L mS _ fp K s (relocateC FB reserved (D.params f).length ++ cb) ρ :=
      ⟨rest.ctx, pre.small, hfS, (codeAt_right rest.code).agree aS farS,
        farS, envS, trivial, wstab_true _ _⟩
    obtain ⟨mR, rr, aR, moved⟩ := relocate_env_counted hfS pre.small
      (by unfold frei reserved; omega)
      envS rem.left.code (by simpa [relocateC_length] using rem.left.far)
    have ar := Gabbro.Stage0.Senke.Agree.widen aR (show frei (D.params f) (0 + reserved) ≤ K by unfold frei reserved; omega)
    have original := envAt_agree envS ar hfS (by unfold frei FB; omega) (by omega)
    have hpB := rem.next (ar.mono (by simp only [s, FB]; omega)) (Nat.le_refl _) (by omega)
    have bodyPre : PreS L mR _ fp K (frei (D.params f) reserved) cb ρ reserved :=
      ⟨Nat.le_refl _, pre.small, hfS.agree ar, hpB.code, hpB.far,
        by simpa using moved, trivial, wstab_true _ _⟩
    have all : Agree fp 3 K m mR := (a1.mono (by simp only [s, FB]; omega)).trans (aS.trans (ar.mono (by unfold FB; omega)))
    have worldR := weltAt_stab inside.lay (by have := inside.top; omega) m mR world (all.mono (by decide))
    have rpc : mR.rd64 fp = some rp := by
      have h := agree_rd_low (i := 0) all pre.frame.room (by decide) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : mR.rd64 (fp + 8) = some cfp := by
      have h := agree_rd_low (i := 1) all pre.frame.room (by decide) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨m', rb, post, bodyAgree, frame, finalPC, finalFP, finalWorld⟩ := (body ens hens (rdW mR fp 3)).sound hb (by omega) inside
      (by simp only [frei]; omega) (by simp only [FB]; omega) (by omega)
      (fun _ h => nomatch h) bodyPre worldR ρ original rfl
      (rd64_rdW (hfS.agree ar) (by omega)) rpc rfp
    simp only [relocateC_length] at rb
    refine ⟨_, m', declaration cs hcs, ?_, ⟨ens, hens, _, post⟩, (agreeW_of (all.mono (by decide))).trans bodyAgree, frame, finalPC, finalFP, finalWorld⟩
    simpa [s, pc_add, relocateC_length, List.length_append, Nat.add_assoc] using
      first.trans (rq.trans (rs.trans (rr.trans rb)))
  next refused => simp at lower
namespace FullFunProbe
open FnptrProben
-- Keep the fixture's carriers, with an exact literal result signature.
def fixtureDecl : Deklaration := { FnptrProben.D with
  sigNr := fun _ => { FnptrProben.D.sigNr 0 with erg := some (.int 37 37), params := [.int 37 37] }
  passt_ok := fun _ _ _ => SigPasst.refl _ _ }
instance (n : Nat) : OfNat fixtureDecl.Fn n := inferInstanceAs (OfNat (Fin 3) n)
def program : Programm fixtureDecl where
  invariante i := nomatch i
  requires _ := .tru
  ensures _ := .tru
  rumpf _ := .ret (.val (.lit 37)) List.Perm.nil

def layout : Lay fixtureDecl where
  fa := addresses
  col t := nomatch t
  ga _ := 8192
  lo := 8192
  hi := 8200
  tor a := nomatch a
  byte t := nomatch t
  sb := 4096
  st := 2048
def world : World fixtureDecl where
  slots t := nomatch t
  globs _ := ⟨0, rfl⟩
  spur := []
def image : List II := ((lowFun 2 program addresses layout 0).getD ([], 0)).1
def memory : Mem :=
  let base : Mem := {
    b := fun a => ((image.flatMap encII)[a.toNat]?).getD 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write (write (write (write base 4096 8 2048) 4104 8 16384) 4112 8 1) 8192 8 64) 4128 8 37

/-- The full lowered function has a nonzero result and distinct caller header. -/
theorem terminalCountedSim_zeuge :
    ∃ n m', n ≤ 12 ∧ Counted n ⟨0, 4096⟩ memory ⟨2048, 16384⟩ m' ∧
      FrameOK m' 4096 256 ∧ WeltAt m' layout world ∧
      CountedSim n layout program 0 world
        (Env.cons (τ := .int 37 37) ⟨37, by decide, by decide⟩ Env.nil)
        2048 16384 4096 5 256 [] ⟨0, 4096⟩ memory 0 0 0
        (Ausgang.zurueck (l := false) (Γ := [.int 37 37]) world
          (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37))) 3 := by
  have lower : lowFun 2 program addresses layout 0 = some (image, 14) := by decide +kernel
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  have pre : PreS layout memory 0 4096 256 5 image (Env.cons (τ := .int 37 37) (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil) :=
    ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
      code, by unfold CodeFar; decide +kernel, (by intro τ x; cases x with
        | here => exact ⟨37, by decide +kernel, rfl⟩
        | there x => nomatch x), trivial, wstab_true _ _⟩
  have inside : WIn layout 4096 128 256 := by
    refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩, ?_, by decide, by decide, by decide⟩
    constructor
    · intro c c' hc hc' h
      cases c with
      | elem t => nomatch t
      | glob g =>
        cases c' with
        | elem t => nomatch t
        | glob g' => cases g; cases g'; rfl
    · intro c hc
      cases c with
      | elem t => nomatch t
      | glob _ => rfl
  have hw : WeltAt memory layout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  have joint := lowFun_counted (declared := 12) (rp := 2048) (cfp := 16384) (nq := 1) (nb := 6) (σ := world) (depth := 1)
    (ρ := Env.cons (τ := .int 37 37) (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil) lower (by decide) inside .truth
    (by
      intro ens hens snapshot
      have eq : ens = ([ci 1 6 1 0], 7) := Option.some.inj hens.symm
      subst ens
      exact .normal (τ := .int 37 37) (v := (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)))
        (q := Expr.tru (Λ := [])) rfl List.Perm.nil .literal (.ordinary rfl .truth) rfl)
    (by
      intro cs hcs
      have eq : cs = [] := Option.some.inj hcs.symm
      subst cs
      decide)
    (by
      exact pre)
    (by
      exact hw)
    (by
      decide +kernel)
    (by
      decide +kernel)
    (by
      decide +kernel)
    (by
      decide)
  obtain ⟨n, mout, bound, run, post, agree, frame, rpc, rfp, hw⟩ := joint
  obtain ⟨ens, hens, snapshot, post⟩ := post
  have eq : ens = ([ci 1 6 1 0], 7) := Option.some.inj hens.symm
  subst ens
  let cert : EndCost layout 3 (vertragVon fixtureDecl 0) false [.int 37 37]
      snapshot ([ci 1 6 1 0], 7) 5 (program.rumpf 0) world
      (Env.cons (τ := .int 37 37) ⟨37, by decide, by decide⟩ Env.nil) 6 :=
    .normal (τ := .int 37 37) (v := ⟨37, by decide, by decide⟩)
      (q := Expr.tru (Λ := [])) rfl List.Perm.nil .literal (.ordinary rfl .truth) rfl
  have sim := cert.post_countedSim (P := program) (f := 0)
    (σ0 := world) (ρ0 := Env.cons (τ := .int 37 37) ⟨37, by decide, by decide⟩ Env.nil)
    (pr := []) (e := 0) (eL := 0) (eN := 0) run agree hw
    (by exact post) rfl (by intros; change true ≠ false; decide)
  exact ⟨n, mout, bound, run, frame, hw, sim⟩

/-- The original execution projection is derived from the joint ABI witness. -/
theorem lowFun_counted_zeuge :
    ∃ n m', n ≤ 12 ∧ Counted n ⟨0, 4096⟩ memory ⟨2048, 16384⟩ m' ∧
      FrameOK m' 4096 256 ∧ WeltAt m' layout world := by
  obtain ⟨n, m', bound, run, frame, world, sim⟩ := terminalCountedSim_zeuge
  exact ⟨n, m', bound, run, frame, world⟩
end FullFunProbe


/-- Actual call arguments and entry compose with the complete source-certified
    callee. The declared bound concerns S0IR instructions only. -/
theorem ArgsCost.fullCall {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {P : Programm D} {passes : Nat}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared : Nat}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {ca : List II} {ta top K Ks : Nat} {m : Mem} {pc fp : W}
    (lowerArgs : lowA L args (frei Γ reserved + FB) reserved = some (ca, ta))
    (fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks)
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31) (positive : dv ≠ 0)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, EndCost L ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    (pre : PreS L m pc fp K (frei Γ reserved) (callC A f (frei Γ reserved) ca) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ) :
    ∃ n m', n ≤ na + 4 + declared ∧ Counted n ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (ca.length + 4)), fp⟩ m' ∧
      (∃ ens, ∃ hens : lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens,
        ∃ snapshot, (body ens hens snapshot).Post (slot fp (BitVec.ofNat 64 (frei Γ reserved))) m') ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧ FrameOK m' fp K ∧
      FrameOK m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) =
        some (pc + BitVec.ofNat 64 (16 * (ca.length + 4))) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved)) + 8) = some fp ∧
      WeltAt m' L σ := by
  have hks := inside.ks
  have bounds := fitsArgs
  simp only [callTop] at bounds
  have hF : frei Γ reserved ≤ Ks := by omega
  obtain ⟨m1, entry, entryAgree, frame, code, rpc, rfp, depth, env, hw, _⟩ :=
    arguments.callEntry lowerArgs fitsArgs address pre surroundings inside world
  have calleePre : PreS L m1 (BitVec.ofNat 64 (A f))
      (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved)
      (FB + (D.params f).length) (C f) (evalArgs σ₀ args σ ρ) :=
    ⟨by simpa [frei] using Nat.le_refl (FB + (D.params f).length),
      by have := pre.small; omega, frame, (code f).1, (code f).2,
      env, trivial, wstab_true _ _⟩
  obtain ⟨n, m2, bound, run, post, calleeAgree, frame, rpc, rfp, hw⟩ := lowFun_counted lowerFun fitsFun
    (inside.sub hF pre.frame.lt) requirement body declaration calleePre hw rpc rfp depth positive
  have callAgree : AgreeW L fp (frei Γ reserved) K m m2 :=
    (agreeW_of entryAgree).trans ((agreeW_sub pre.frame.lt (by omega) calleeAgree).mono (by omega))
  exact ⟨na + 4 + n, m2, by omega, entry.trans run, post, callAgree,
    frameOK_agreeW pre.frame callAgree, frame, rpc, rfp, hw⟩
/-- A real call and its recursive source continuation share one machine endpoint.
    The callee bound is derived from its requirement, body and entry certificates. -/
theorem BlockCost.call {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {P : Programm D} {passes : Nat}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared : Nat}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {ca : List II} {ta top K Ks : Nat} {m : Mem} {pc fp : W}
    (lowerArgs : lowA L args (frei Γ reserved + FB) reserved = some (ca, ta))
    (fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks)
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31) (positive : dv ≠ 0)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, EndCost L ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    {V : Vertrag D} {l : Bool} {Λ' : List (Res D)}
    {rest : Block D V l Γ (nach D f Λ) Λ'} {σ' : World D} {ρ' : Env D Γ}
    {nr tr lo : Nat} {cr : List II} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    (tail : BlockCost L reserved V l rest σ ρ σ' ρ' nr)
    (lowerTail : lowB (reserved := reserved) passes A L lo ens pr ex rest = some (cr, tr))
    (fitsTail : tr ≤ Ks) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) (callC A f (frei Γ reserved) ca ++ cr) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ) :
    ∃ n, n ≤ na + 4 + declared + nr ∧
      CountedReach n L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * (callC A f (frei Γ reserved) ca ++ cr).length))
        σ' ρ' reserved := by
  have hks := inside.ks
  have room : frei Γ reserved ≤ Ks := by
    have h := fitsArgs
    simp only [callTop] at h
    omega
  obtain ⟨n, m1, bound, run, post, agree, frame, childFrame, rpc, rfp, hw⟩ :=
    arguments.fullCall lowerArgs fitsArgs lowerFun fitsFun address positive
      requirement body declaration pre.left surroundings inside world
  have next := pre.nextW inside agree (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have len : (callC A f (frei Γ reserved) ca).length = ca.length + 4 := by
    simp [callC, callTail, callTailN, List.length_append]
  obtain ⟨m2, restRun, restAgree, env, hw2, keep⟩ :=
    tail.sound lowerTail fitsTail inside low hprotected next hw
  refine ⟨n + nr, by omega, m2, ?_, (agree.mono low).trans restAgree, env, hw2,
    (keeps_of_agreeW inside agree hprotected (by omega)).trans keep⟩
  rw [← len] at run
  have joined := run.trans restRun
  simpa only [pc_add1] using joined

/-- Source-facing call constructor: the actual block lowering supplies both children. -/
theorem actualBlockCost.call {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {P : Programm D} {passes : Nat}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared : Nat}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {top K Ks : Nat} {m : Mem} {pc fp : W}
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31) (positive : dv ≠ 0)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, EndCost L ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    {V : Vertrag D} {l : Bool} {Λ' : List (Res D)}
    {rest : Block D V l Γ (nach D f Λ) Λ'} {σ' : World D} {ρ' : Env D Γ}
    {nr lo : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    (tail : BlockCost L reserved V l rest σ ρ σ' ρ' nr)
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    {code : List II} {wholeTop : Nat}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex
      (.cons (.call f args hp hr) rest) = some (code, wholeTop))
    (fits : wholeTop ≤ Ks) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ) :
    ∃ n, n ≤ na + 4 + declared + nr ∧
      CountedReach n L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * code.length))
        σ' ρ' reserved := by
  simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨cr, tr⟩, lowerTail, ⟨cs, ts⟩, lowerStmt, out⟩ := lower
  simp only [lowS, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lowerStmt
  obtain ⟨⟨ca, ta⟩, lowerArgs, stmtOut⟩ := lowerStmt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj stmtOut
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
  change max (callTop f (frei Γ reserved) ta) tr ≤ Ks at fits
  exact BlockCost.call arguments lowerArgs (by omega) lowerFun fitsFun address positive
    requirement body declaration tail lowerTail (by omega) low hprotected pre surroundings inside world


/-- Reconstruct the callee call environment at the actual entry endpoint.
    Its slot-2 convention is one less than the depth installed by callEntry. -/
theorem ArgsCost.recursiveEntry {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na : Nat}
    (certificate : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
    {ca : List II} {ta K Ks : Nat} {m : Mem} {pc fp : Runner.W}
    (lower : lowA L args (frei Γ reserved + FB) reserved = some (ca, ta))
    (fits : callTop f (frei Γ reserved) ta ≤ Ks)
    (address : A f < 2 ^ 31)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (callC A f (frei Γ reserved) ca) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ) :
    ∃ m', Counted (na + 4) ⟨pc, fp⟩ m
        ⟨BitVec.ofNat 64 (A f), slot fp (BitVec.ofNat 64 (frei Γ reserved))⟩ m' ∧
      Agree fp (frei Γ reserved) K m m' ∧
      FrameOK m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved) ∧
      Umf L A C (dv - 1) m' (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (Ks - frei Γ reserved) (K - frei Γ reserved) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) =
        some (pc + BitVec.ofNat 64 (16 * (ca.length + 4))) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved)) + 8) = some fp ∧
      EnvAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (evalArgs σ₀ args σ ρ) ∧
      WeltAt m' L σ := by
  obtain ⟨m', run, agree, frame, code, rpc, rfp, depth, env, hw, sync⟩ :=
    certificate.callEntry lower fits address pre surroundings inside world
  have hks := inside.ks
  have bounds := fits
  simp only [callTop] at bounds
  have room : frei Γ reserved ≤ K := by omega
  have hs : (slot fp (BitVec.ofNat 64 (frei Γ reserved))).toNat =
      fp.toNat + 8 * frei Γ reserved := by
    have := fp.isLt
    have hr := pre.frame.lt
    have h8 : (8 : W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := frei Γ reserved) (by omega)]
    omega
  refine ⟨m', run, agree, frame, ?_, rpc, rfp, env, hw⟩
  refine ⟨code, ?_, ?_, sync, ?_⟩
  · simpa only [BitVec.sub_add_cancel] using depth
  · simp only [callTop, FB] at bounds ⊢
    omega
  · rw [hs]
    have := surroundings.hiK
    omega

/-- Terminal call trees certify actual callee source bodies. The depth index
    decreases at each callee edge; continuations retain the parent's depth.
    Returned values are shared through an index, rather than a callee contract.
    Soundness for these trees is separate from the call-free EndCost theorem. -/
inductive RecursiveEndCost (L : Lay D) (P : Programm D)
    (passes : Nat) (A : D.Fn → Nat) (C : D.Fn → List II)  :
    (depth Ks reserved : Nat) → (V : Vertrag D) → (l : Bool) →
    (Δ : Ctx) → (snapshot : W) → (ens : List II × Nat) → (lo : Nat) →
    {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ →
      World D → Env D Γ → Ausgang V l Γ → Nat → Type
  | source {depth Ks reserved V l Δ snapshot ens lo Γ Λ b σ ρ n}
      (source : EndCost L reserved V l Δ snapshot ens lo (Γ := Γ) (Λ := Λ) b σ ρ n) :
      RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo b σ ρ source.outcome n
  | call {depth Ks reserved V l Δ snapshot ens lo} {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared : Nat} {returned : Ausgang (vertragVon D f) false (D.params f)}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {top : Nat}
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, RecursiveEndCost L P passes A C depth (Ks - frei Γ reserved)
        ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) returned nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    {rest : Endblock D V l Γ (nach D f Λ)}
    {nr : Nat} {output : Ausgang V l Γ}
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    (tail : RecursiveEndCost L P passes A C (depth + 1) Ks reserved V l Δ snapshot ens lo rest σ ρ output nr) :
    RecursiveEndCost L P passes A C (depth + 1) Ks reserved V l Δ snapshot ens lo
      (.cons (.call f args hp hr) rest) σ ρ output (na + 4 + declared + nr)

  | bindCall {depth Ks reserved V l Δ snapshot ens lo} {Γ : Ctx} {τ : Ty} {v : Wert D τ} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared : Nat} {returned : Ausgang (vertragVon D f) false (D.params f)}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {top : Nat}
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, RecursiveEndCost L P passes A C depth (Ks - frei Γ reserved)
        ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) returned nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    (result : terminalResult returned = some ⟨τ, v⟩)
    {he : D.erg f = some τ}
    {rest : Endblock D V l (τ :: Γ) (nach D f Λ)}
    {nr : Nat} {output : Ausgang V l (τ :: Γ)}
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    (tail : RecursiveEndCost L P passes A C (depth + 1) Ks reserved V l Δ snapshot ens lo rest σ (.cons v ρ) output nr) :
    RecursiveEndCost L P passes A C (depth + 1) Ks reserved V l Δ snapshot ens lo
      (.bindCall f args he hp hr rest) σ ρ output.schrumpf (na + 4 + declared + 1 + nr)


  | assign {depth Ks reserved V l Δ snapshot ens lo} {Γ Λ τ} {output : Ausgang V l Γ} {x : Var Γ τ} {e : Expr D Γ Λ τ}
      {rest : Endblock D V l Γ Λ} {σ : World D} {ρ : Env D Γ}
      {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo rest σ (ρ.set x v) output nr) :
      RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo (.cons (.assignVar x e) rest) σ ρ output (ne + 1 + nr)
  | bind {depth Ks reserved V l Δ snapshot ens lo} {Γ Λ τ} {output : Ausgang V l (τ :: Γ)} {e : Expr D Γ Λ τ} {rest : Endblock D V l (τ :: Γ) Λ}
      {σ : World D} {ρ : Env D Γ} {v : Wert D τ} {ne nr : Nat}
      (value : ExprCost L reserved e (frei Γ reserved) ne (Enc L τ v))
      (tail : RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo rest σ (.cons v ρ) output nr) :
      RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo (.bind e rest) σ ρ output.schrumpf (ne + nr)

  | branch {depth Ks reserved V l Δ snapshot ens lo} {Γ Λ} {output : Ausgang V l Γ} {c : Expr D Γ Λ .bool} {t e : Endblock D V l Γ Λ}
      {σ : World D} {ρ : Env D Γ} {choice : Bool} {nc nb : Nat}
      (condition : ExprCost L reserved c (frei Γ reserved) nc
        (· = if choice then 1 else 0))
      (jumpFits : ∀ passes A pr ex ct tt,
        lowEnd (reserved := reserved) passes A L lo ens pr ex t = some (ct, tt) →
        16 * (ct.length + 1) < 2 ^ 31)
      (child : RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo
        (if choice then t else e) σ ρ output nb) :
      RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo (.ite c t e) σ ρ output (nc + 1 + nb)

/-- Execute actual recursive callee bodies with their decreasing child induction hypotheses. -/
theorem RecursiveEndCost.sound
    {passes depth Ks reserved V l Δ snapshot ens lo Γ Λ b σ ρ output budget}
    {A : D.Fn → Nat} {C : D.Fn → List II}
    (certificate : RecursiveEndCost L P passes A C depth Ks reserved V l Δ snapshot ens lo
      (Γ := Γ) (Λ := Λ) b σ ρ output budget)
    {K top : Nat} {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp rp cfp : W}
    (lower : lowEnd (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (low : lo ≤ frei Γ reserved) (abi : 3 < lo) (lowBound : lo ≤ K)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ)
    (parameters : Env D Δ) (parameterEnv : EnvAt L m fp parameters)
    (base : lo = frei Δ)
    (entry : m.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot)
    (savedPC : m.rd64 fp = some rp) (savedFP : m.rd64 (fp + 8) = some cfp)
    (surroundings : Umf L A C (BitVec.ofNat 64 depth) m fp Ks K)
    (depthBound : depth + 1 < 2 ^ 64) :
    ∃ n m', n ≤ budget ∧ Counted n ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
      AgreeW L fp 2 K m m' ∧ FrameOK m' fp K ∧ WeltAt m' L σ ∧
      (∀ τ v, terminalResult output = some ⟨τ, v⟩ →
        ∃ w, m'.rd64 (slot fp 2) = some w ∧ Enc L τ v w) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (lo + 1))) =
        some (if (terminalResult output).isSome then 1 else 0) ∧
      (∀ r, terminalReason output = some r →
        m'.rd64 (slot fp 2) = some (BitVec.ofNat 64 r.val)) := by
  induction certificate generalizing K top code m pc fp rp cfp pr ex with
  | source cert =>
    obtain ⟨m', run, post, agree, frame, rpc, rfp, hw⟩ :=
      cert.sound lower fits inside low abi lowBound hprotected pre world
        parameters parameterEnv base entry savedPC savedFP
    exact ⟨_, m', Nat.le_refl _, run, agree, frame, hw, (fun τ v result => cert.result_read (by simpa using result) post), ⟨cert.result_status post, fun _ result => cert.reason_read result post⟩⟩
  | @call depth Ks reserved V l Δ snapshot ens lo Γ Λ f args σ₀ σ ρ na nq nb declared returned
      arguments topF lowerFun fitsFun address requirement body declaration rest nr output hp hr tail body_ih tail_ih =>
    let childKs := Ks - frei Γ reserved
    have calleeRun {m : Mem} {pc fp rp cfp : W} {K : Nat}
        (fits : topF ≤ childKs)
        (inside : WIn L fp childKs K)
        (pre : PreS L m pc fp K (FB + (D.params f).length) (C f)
          (evalArgs σ₀ args σ ρ))
        (world : WeltAt m L σ) (savedPC : m.rd64 fp = some rp)
        (savedFP : m.rd64 (fp + 8) = some cfp)
        (childUmf : Umf L A C (BitVec.ofNat 64 depth) m fp childKs K) :
        ∃ n m', n ≤ declared ∧ Counted n ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
          AgreeW L fp 2 K m m' ∧ FrameOK m' fp K ∧ WeltAt m' L σ ∧
          (∀ τ v, terminalResult returned = some ⟨τ, v⟩ →
            ∃ w, m'.rd64 (slot fp 2) = some w ∧ Enc L τ v w) := by
      have depthRead := childUmf.depth
      have positive : (BitVec.ofNat 64 depth : W) + 1 ≠ 0 := by
        bv_omega
      have hks := inside.ks
      have lower := lowerFun
      simp only [lowFun] at lower
      split at lower
      next accepted =>
        simp only [Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
        obtain ⟨⟨cq, tq⟩, hq, ens, hens, ⟨cb, tb⟩, hb, cs, hcs, hc, ht⟩ := lower
        rw [← hc] at pre
        let s := FB + (D.params f).length
        let reserved := (D.params f).length + 2 + 2 * counterDepthE (P.rumpf f)
        have bounds := fits
        rw [← ht] at bounds
        simp only [frei] at bounds
        have hp : PreS L m pc fp K s
            (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ (cs ++
              (relocateC FB reserved (D.params f).length ++ cb))))) (evalArgs σ₀ args σ ρ) := by
          simpa [s, reserved, List.append_assoc] using pre
        have first := guard_pass_counted hp.left.code (by decide) depthRead positive
        have hp1 := hp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
        have phases : PreS L m (pc + BitVec.ofNat 64 (16 * (guardC 2 105 s).length)) fp K s ((cq ++ guardC s 101 s) ++
            (cs ++ (relocateC FB reserved (D.params f).length ++ cb))) (evalArgs σ₀ args σ ρ) := by
          simpa [List.append_assoc] using hp1
        have hpq := phases.left
        obtain ⟨m1, rq, a1, env1, _⟩ := requirement.guard hq (by omega) hpq
        have hf1 := hp.frame.agree a1
        have rest := phases.next a1 (Nat.le_refl _) (by omega)
        have world1 := weltAt_stab inside.lay (by have := inside.top; omega) m m1 world (a1.mono (Nat.zero_le _))
        obtain ⟨mS, rs, aS, snap, keep⟩ := snapC_counted hcs hf1 pre.small (by omega)
          rest.left.code rest.left.far world1 inside.lay (by have := inside.top; omega)
        have hfS := hf1.agree aS
        have envS : EnvAt L mS fp (evalArgs σ₀ args σ ρ) := by
          intro τ x
          obtain ⟨w, hw, enc⟩ := env1 τ x
          exact ⟨w, (keep (vslot x) (by have := vslot_lt (reserved := 0) x; unfold frei at this; omega)
            (by unfold vslot FB; omega)).trans hw, enc⟩
        have farS := codeFar_tail rest.far
        have rem : PreS L mS _ fp K s (relocateC FB reserved (D.params f).length ++ cb) (evalArgs σ₀ args σ ρ) :=
          ⟨rest.ctx, pre.small, hfS, (codeAt_right rest.code).agree aS farS,
            farS, envS, trivial, wstab_true _ _⟩
        obtain ⟨mR, rr, aR, moved⟩ := relocate_env_counted hfS pre.small
          (by unfold frei reserved; omega)
          envS rem.left.code (by simpa [relocateC_length] using rem.left.far)
        have ar := Gabbro.Stage0.Senke.Agree.widen aR (show frei (D.params f) (0 + reserved) ≤ K by unfold frei reserved; omega)
        have original := envAt_agree envS ar hfS (by unfold frei FB; omega) (by omega)
        have hpB := rem.next (ar.mono (by simp only [s, FB]; omega)) (Nat.le_refl _) (by omega)
        have bodyPre : PreS L mR _ fp K (frei (D.params f) reserved) cb (evalArgs σ₀ args σ ρ) reserved :=
          ⟨Nat.le_refl _, pre.small, hfS.agree ar, hpB.code, hpB.far,
            by simpa using moved, trivial, wstab_true _ _⟩
        have all : Agree fp 3 K m mR := (a1.mono (by simp only [s, FB]; omega)).trans (aS.trans (ar.mono (by unfold FB; omega)))
        have worldR := weltAt_stab inside.lay (by have := inside.top; omega) m mR world (all.mono (by decide))
        have rpc : mR.rd64 fp = some rp := by
          have h := agree_rd_low (i := 0) all pre.frame.room (by decide) (by omega)
          simpa [slot] using h.trans (by simpa [slot] using savedPC)
        have rfp : mR.rd64 (fp + 8) = some cfp := by
          have h := agree_rd_low (i := 1) all pre.frame.room (by decide) (by omega)
          simpa [slot] using h.trans (by simpa [slot] using savedFP)
        have bodyUmf : Umf L A C (BitVec.ofNat 64 depth) mR fp childKs K := by
          refine ⟨pcode_agree childUmf.code all, ?_, childUmf.big,
            childUmf.sync.agree all childUmf.hiK, childUmf.hiK⟩
          rw [agree_rd_low (i := 2) all pre.frame.room (by decide) (by omega)]
          exact childUmf.depth
        obtain ⟨nBody, m', boundBody, rb, bodyAgree, frame, finalWorld, resultRead, _status⟩ :=
          body_ih ens hens (rdW mR fp 3) hb (by omega) inside
          (by simp only [frei]; omega) (by simp only [FB]; omega) (by omega)
          (fun _ h => nomatch h) bodyPre worldR (evalArgs σ₀ args σ ρ) original rfl
          (rd64_rdW (hfS.agree ar) (by omega)) rpc rfp bodyUmf (by omega)
        simp only [relocateC_length] at rb
        refine ⟨2 + nq + 2 + cs.length + (D.params f).length + nBody, m', by have := declaration cs hcs; omega, ?_, (agreeW_of (all.mono (by decide))).trans bodyAgree, frame, finalWorld, resultRead⟩
        simpa [s, pc_add, relocateC_length, List.length_append, Nat.add_assoc] using
          first.trans (rq.trans (rs.trans (rr.trans rb)))
      next refused => simp at lower
    simp only [lowEnd, lowS, Bind.bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, rfl, rfl⟩ := lower
    obtain ⟨⟨ca, ta⟩, ha, out⟩ := hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    simp only [Prod.fst, Prod.snd] at fits pre
    have fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks := by omega
    have hks := inside.ks
    have room : frei Γ reserved ≤ Ks := by
      have h := fitsArgs
      simp only [callTop] at h
      omega
    have len : (callC A f (frei Γ reserved) ca).length = ca.length + 4 := by
      simp [callC, callTail, callTailN, List.length_append]
    obtain ⟨m1, entryRun, entryAgree, childFrame, childUmf, rpc, rfp, env, hw⟩ :=
      arguments.recursiveEntry ha fitsArgs address pre.left surroundings inside world
    have childUmf' : Umf L A C (BitVec.ofNat 64 depth) m1
        (slot fp (BitVec.ofNat 64 (frei Γ reserved))) childKs (K - frei Γ reserved) := by
      have deq : (BitVec.ofNat 64 (depth + 1) : W) - 1 = BitVec.ofNat 64 depth := by bv_omega
      simpa only [deq] using childUmf
    have calleePre : PreS L m1 (BitVec.ofNat 64 (A f))
        (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved)
        (FB + (D.params f).length) (C f) (evalArgs σ₀ args σ ρ) :=
      ⟨by simp [frei], by have := pre.small; omega, childFrame,
        (childUmf'.code f).1, (childUmf'.code f).2, env, trivial, wstab_true _ _⟩
    obtain ⟨nCall, m2, boundCall, callRun, calleeAgree, frame, hw, resultRead⟩ :=
      calleeRun fitsFun (inside.sub room pre.frame.lt) calleePre hw rpc rfp childUmf'
    have agree : AgreeW L fp (frei Γ reserved) K m m2 :=
      (agreeW_of entryAgree).trans
        ((agreeW_sub pre.frame.lt (by omega) calleeAgree).mono (by omega))
    have nextPre := pre.nextW inside agree (Nat.le_refl _) (Nat.le_refl _) (by omega)
    have rpc2 : m2.rd64 fp = some rp := by
      have h := agreeW_rdW inside agree (i := 0) (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp2 : m2.rd64 (fp + 8) = some cfp := by
      have h := agreeW_rdW inside agree (i := 1) (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨nRest, m3, boundRest, restRun, finalAgree, frame, hw, resultRead, status⟩ :=
      tail_ih hr (by omega) inside low abi lowBound hprotected nextPre hw parameters
        (envAt_agreeWIn inside parameterEnv agree (by omega) (by omega)) base
        (by rw [agreeW_rdW inside agree (i := 3) (by omega) (by omega)]; exact entry)
        rpc2 rfp2 (Umf.agreeW inside surroundings agree (by unfold frei FB; omega)) depthBound
    refine ⟨na + 4 + nCall + nRest, m3, by omega, ?_,
      (agree.mono (by omega)).trans finalAgree, frame, hw, (by simpa using resultRead), (by simpa using status)⟩
    rw [← len] at rpc
    have joined := entryRun.trans callRun
    rw [← len] at joined
    exact joined.trans restRun
  | @assign depth Ks reserved V l Δ snapshot ens lo Γ Λ τ output x e rest σ ρ v ne nr value tail ih =>
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    obtain ⟨m1, run1, agree1, env1, world1, keep1⟩ :=
      countedAssignVar_case value hs (Nat.le_trans (Nat.le_max_left _ _) fits)
        inside low hprotected pre.left world
    have far := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
    have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K
        (frei _ reserved) cr _ reserved :=
      ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame agree1,
        codeAt_agreeWIn inside agree1 (codeAt_right pre.code) far,
        far, env1, trivial, wstab_true _ _⟩
    have hK : lo ≤ K := lowBound
    have rpc : m1.rd64 fp = some rp := by
      have h := agreeW_rdW inside agree1 (i := 0) (by omega) hK
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : m1.rd64 (fp + 8) = some cfp := by
      have h := agreeW_rdW inside agree1 (i := 1) (by omega) hK
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨n2, m2, bound2, run2, finalAgree, frame, hw, result2, status⟩ := ih hr (Nat.le_trans (Nat.le_max_right _ _) fits) inside
      low abi lowBound hprotected nextPre world1
      parameters (envAt_agreeWIn inside parameterEnv agree1 (by omega) lowBound) base
      (by rw [agreeW_rdW inside agree1 (i := 3) (by omega) lowBound]; exact entry) rpc rfp
      (Umf.agreeW inside surroundings agree1 (by unfold FB; omega)) depthBound
    exact ⟨_, m2, by omega, run1.trans run2, (agree1.mono (by omega)).trans finalAgree, frame, hw, (by simpa using result2), (by simpa using status)⟩
  | @bind depth Ks reserved V l Δ snapshot ens lo Γ Λ τ output e rest σ ρ v ne nr value tail ih =>
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have hks := inside.ks
    have room := lowE_top _ _ _ _ he
    have hpw := PreS.welt pre.left inside.ks world inside.lay (by have := inside.lo; omega)
    obtain ⟨m1, run1, a1s, w, read, encoded⟩ :=
      value.sound he (Nat.le_trans (Nat.le_max_left _ _) fits) hpw
    have a1 := Agree.widen a1s inside.ks
    have far := codeFar_right (n := ce.length) (k := cr.length) (by simpa using pre.far)
    have nextPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K
        (frei Γ reserved + 1) cr (Env.cons v ρ) reserved :=
      ⟨by simp only [frei, List.length_cons]; omega, pre.small, pre.frame.agree a1,
        (codeAt_right pre.code).agree a1 far, far,
        envAt_cons (envAt_agree pre.env a1 pre.frame (Nat.le_refl _) (by omega)) read encoded,
        trivial, wstab_true _ _⟩
    have rpc : m1.rd64 fp = some rp := by
      have h := agree_rd_low (i := 0) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : m1.rd64 (fp + 8) = some cfp := by
      have h := agree_rd_low (i := 1) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨n2, m2, bound2, run2, finalAgree, frame, hw, result2, status⟩ := ih hr (Nat.le_trans (Nat.le_max_right _ _) fits) inside
      (by simp only [frei, List.length_cons] at low ⊢; omega)
      abi lowBound (fun j hj => by have := hprotected j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      nextPre (hpw.wstab m m1 world (a1s.mono (Nat.zero_le _)))
      parameters (envAt_agree parameterEnv a1 pre.frame (by omega) (by omega)) base
      (by rw [agree_rd_low a1 pre.frame.room (by omega) (by omega)]; exact entry) rpc rfp
      (surroundings.agree a1 pre.frame (by unfold frei FB; omega)) depthBound
    exact ⟨_, m2, by omega, run1.trans run2, (agreeW_of (a1.mono (by omega))).trans finalAgree, frame, hw, (by simpa using result2), (by simpa using status)⟩

  | @branch depth Ks reserved V l Δ snapshot ens lo Γ Λ output c t e σ ρ choice nc nb condition jumpFits child ih =>
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cc, tc⟩, hc, ⟨ce, te⟩, he, ⟨ct, tt⟩, ht, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have hks := inside.ks
    have room := lowE_top _ _ _ _ hc
    have hq : PreS L m pc fp K (frei Γ reserved)
        (cc ++ ([ci 19 (frei Γ reserved) (16 * (ct.length + 1)) 0] ++ (ct ++ ce))) ρ reserved := by
      simpa [List.append_assoc] using pre
    have hpw := PreS.welt hq.left inside.ks world inside.lay (by have := inside.lo; omega)
    obtain ⟨m1, run1, a1s, w, read, value⟩ := condition.sound hc (by omega) hpw
    have a1 := Agree.widen a1s inside.ks
    have h1 := hq.next a1 (Nat.le_refl _) (by omega)
    have h2 := h1.next (a := [ci 19 (frei Γ reserved) (16 * (ct.length + 1)) 0])
      (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have ins := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
    have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
      sx_nat (by have := pre.small; omega)
    have world1 := hpw.wstab m m1 world (a1s.mono (Nat.zero_le _))
    have params1 := envAt_agree parameterEnv a1 pre.frame (by omega) (by omega)
    have entry1 : m1.rd64 (slot fp (BitVec.ofNat 64 3)) = some snapshot := by
      rw [agree_rd_low a1 pre.frame.room (by omega) (by omega)]; exact entry
    have rpc : m1.rd64 fp = some rp := by
      have h := agree_rd_low (i := 0) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp : m1.rd64 (fp + 8) = some cfp := by
      have h := agree_rd_low (i := 1) a1 pre.frame.room (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    cases choice with
    | true =>
      simp only [Bool.true_eq, ↓reduceIte] at value child ih
      subst w
      have sb := counted_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne ins (by rw [hd]; exact read) (by decide))
      obtain ⟨n2, m2, bound2, run2, agree, frame, hw, result2, status⟩ :=
        ih ht (by omega) inside low abi lowBound hprotected h2.left world1 parameters params1 base entry1 rpc rfp
          (surroundings.agree a1 pre.frame (by unfold frei FB; omega)) depthBound
      have run : Counted (nc + (1 + n2)) ⟨pc, fp⟩ m ⟨rp, cfp⟩ m2 := by
        refine run1.trans (sb.trans ?_)
        simpa [List.length_singleton, pc_add, addr_norm] using run2
      exact ⟨nc + (1 + n2), m2, by omega, by simpa only [Nat.add_assoc] using run,
        (agreeW_of (a1.mono (by omega))).trans agree, frame, hw, (by simpa using result2), (by simpa using status)⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at value child ih
      subst w
      have step := run_step (t := ⟨_, fp⟩) ins (by decide)
        (run_brz_zero ins (by rw [hd]; exact read))
      have offset : sx (II.f (16 * ((ct.length : Int) + 1))) =
          BitVec.ofNat 64 (16 * (ct.length + 1)) := by
        have h := sx_nat (d := 16 * (ct.length + 1)) (jumpFits _ _ _ _ _ _ ht)
        simpa using h
      rw [offset] at step
      have sb := Counted.next step (Counted.refl _ _)
      have h4 := h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      obtain ⟨n2, m2, bound2, run2, agree, frame, hw, result2, status⟩ :=
        ih he (by omega) inside low abi lowBound hprotected h4 world1 parameters params1 base entry1 rpc rfp
          (surroundings.agree a1 pre.frame (by unfold frei FB; omega)) depthBound
      have run : Counted (nc + (1 + n2)) ⟨pc, fp⟩ m ⟨rp, cfp⟩ m2 := by
        refine run1.trans (sb.trans ?_)
        simpa [List.length_singleton, pc_add, addr_norm, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run2
      exact ⟨nc + (1 + n2), m2, by omega, by simpa only [Nat.add_assoc] using run,
        (agreeW_of (a1.mono (by omega))).trans agree, frame, hw, (by simpa using result2), (by simpa using status)⟩

  | @bindCall depth Ks reserved V l Δ snapshot ens lo Γ τ v Λ f args σ₀ σ ρ na nq nb declared returned
      arguments topF lowerFun fitsFun address requirement body declaration result he rest nr output hp hr tail body_ih tail_ih =>
    let childKs := Ks - frei Γ reserved
    have calleeRun {m : Mem} {pc fp rp cfp : W} {K : Nat}
        (fits : topF ≤ childKs)
        (inside : WIn L fp childKs K)
        (pre : PreS L m pc fp K (FB + (D.params f).length) (C f)
          (evalArgs σ₀ args σ ρ))
        (world : WeltAt m L σ) (savedPC : m.rd64 fp = some rp)
        (savedFP : m.rd64 (fp + 8) = some cfp)
        (childUmf : Umf L A C (BitVec.ofNat 64 depth) m fp childKs K) :
        ∃ n m', n ≤ declared ∧ Counted n ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
          AgreeW L fp 2 K m m' ∧ FrameOK m' fp K ∧ WeltAt m' L σ ∧
          (∀ τ v, terminalResult returned = some ⟨τ, v⟩ →
            ∃ w, m'.rd64 (slot fp 2) = some w ∧ Enc L τ v w) := by
      have depthRead := childUmf.depth
      have positive : (BitVec.ofNat 64 depth : W) + 1 ≠ 0 := by
        bv_omega
      have hks := inside.ks
      have lower := lowerFun
      simp only [lowFun] at lower
      split at lower
      next accepted =>
        simp only [Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
        obtain ⟨⟨cq, tq⟩, hq, ens, hens, ⟨cb, tb⟩, hb, cs, hcs, hc, ht⟩ := lower
        rw [← hc] at pre
        let s := FB + (D.params f).length
        let reserved := (D.params f).length + 2 + 2 * counterDepthE (P.rumpf f)
        have bounds := fits
        rw [← ht] at bounds
        simp only [frei] at bounds
        have hp : PreS L m pc fp K s
            (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ (cs ++
              (relocateC FB reserved (D.params f).length ++ cb))))) (evalArgs σ₀ args σ ρ) := by
          simpa [s, reserved, List.append_assoc] using pre
        have first := guard_pass_counted hp.left.code (by decide) depthRead positive
        have hp1 := hp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
        have phases : PreS L m (pc + BitVec.ofNat 64 (16 * (guardC 2 105 s).length)) fp K s ((cq ++ guardC s 101 s) ++
            (cs ++ (relocateC FB reserved (D.params f).length ++ cb))) (evalArgs σ₀ args σ ρ) := by
          simpa [List.append_assoc] using hp1
        have hpq := phases.left
        obtain ⟨m1, rq, a1, env1, _⟩ := requirement.guard hq (by omega) hpq
        have hf1 := hp.frame.agree a1
        have rest := phases.next a1 (Nat.le_refl _) (by omega)
        have world1 := weltAt_stab inside.lay (by have := inside.top; omega) m m1 world (a1.mono (Nat.zero_le _))
        obtain ⟨mS, rs, aS, snap, keep⟩ := snapC_counted hcs hf1 pre.small (by omega)
          rest.left.code rest.left.far world1 inside.lay (by have := inside.top; omega)
        have hfS := hf1.agree aS
        have envS : EnvAt L mS fp (evalArgs σ₀ args σ ρ) := by
          intro τ x
          obtain ⟨w, hw, enc⟩ := env1 τ x
          exact ⟨w, (keep (vslot x) (by have := vslot_lt (reserved := 0) x; unfold frei at this; omega)
            (by unfold vslot FB; omega)).trans hw, enc⟩
        have farS := codeFar_tail rest.far
        have rem : PreS L mS _ fp K s (relocateC FB reserved (D.params f).length ++ cb) (evalArgs σ₀ args σ ρ) :=
          ⟨rest.ctx, pre.small, hfS, (codeAt_right rest.code).agree aS farS,
            farS, envS, trivial, wstab_true _ _⟩
        obtain ⟨mR, rr, aR, moved⟩ := relocate_env_counted hfS pre.small
          (by unfold frei reserved; omega)
          envS rem.left.code (by simpa [relocateC_length] using rem.left.far)
        have ar := Gabbro.Stage0.Senke.Agree.widen aR (show frei (D.params f) (0 + reserved) ≤ K by unfold frei reserved; omega)
        have original := envAt_agree envS ar hfS (by unfold frei FB; omega) (by omega)
        have hpB := rem.next (ar.mono (by simp only [s, FB]; omega)) (Nat.le_refl _) (by omega)
        have bodyPre : PreS L mR _ fp K (frei (D.params f) reserved) cb (evalArgs σ₀ args σ ρ) reserved :=
          ⟨Nat.le_refl _, pre.small, hfS.agree ar, hpB.code, hpB.far,
            by simpa using moved, trivial, wstab_true _ _⟩
        have all : Agree fp 3 K m mR := (a1.mono (by simp only [s, FB]; omega)).trans (aS.trans (ar.mono (by unfold FB; omega)))
        have worldR := weltAt_stab inside.lay (by have := inside.top; omega) m mR world (all.mono (by decide))
        have rpc : mR.rd64 fp = some rp := by
          have h := agree_rd_low (i := 0) all pre.frame.room (by decide) (by omega)
          simpa [slot] using h.trans (by simpa [slot] using savedPC)
        have rfp : mR.rd64 (fp + 8) = some cfp := by
          have h := agree_rd_low (i := 1) all pre.frame.room (by decide) (by omega)
          simpa [slot] using h.trans (by simpa [slot] using savedFP)
        have bodyUmf : Umf L A C (BitVec.ofNat 64 depth) mR fp childKs K := by
          refine ⟨pcode_agree childUmf.code all, ?_, childUmf.big,
            childUmf.sync.agree all childUmf.hiK, childUmf.hiK⟩
          rw [agree_rd_low (i := 2) all pre.frame.room (by decide) (by omega)]
          exact childUmf.depth
        obtain ⟨nBody, m', boundBody, rb, bodyAgree, frame, finalWorld, resultRead, _status⟩ :=
          body_ih ens hens (rdW mR fp 3) hb (by omega) inside
          (by simp only [frei]; omega) (by simp only [FB]; omega) (by omega)
          (fun _ h => nomatch h) bodyPre worldR (evalArgs σ₀ args σ ρ) original rfl
          (rd64_rdW (hfS.agree ar) (by omega)) rpc rfp bodyUmf (by omega)
        simp only [relocateC_length] at rb
        refine ⟨2 + nq + 2 + cs.length + (D.params f).length + nBody, m', by have := declaration cs hcs; omega, ?_, (agreeW_of (all.mono (by decide))).trans bodyAgree, frame, finalWorld, resultRead⟩
        simpa [s, pc_add, relocateC_length, List.length_append, Nat.add_assoc] using
          first.trans (rq.trans (rs.trans (rr.trans rb)))
      next refused => simp at lower
    simp only [lowEnd, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ca, ta⟩, ha, ⟨cr, tr⟩, hr, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    change max (callTop f (frei Γ reserved) ta) tr ≤ Ks at fits
    have fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks := by omega
    have hks := inside.ks
    have room : frei Γ reserved ≤ Ks := by
      have h := fitsArgs
      simp only [callTop] at h
      omega
    have len : (callC A f (frei Γ reserved) ca).length = ca.length + 4 := by
      simp [callC, callTail, callTailN, List.length_append]
    obtain ⟨m1, entryRun, entryAgree, childFrame, childUmf, rpc, rfp, env, hw⟩ :=
      arguments.recursiveEntry ha fitsArgs address pre.left.left surroundings inside world
    have childUmf' : Umf L A C (BitVec.ofNat 64 depth) m1
        (slot fp (BitVec.ofNat 64 (frei Γ reserved))) childKs (K - frei Γ reserved) := by
      have deq : (BitVec.ofNat 64 (depth + 1) : W) - 1 = BitVec.ofNat 64 depth := by bv_omega
      simpa only [deq] using childUmf
    have calleePre : PreS L m1 (BitVec.ofNat 64 (A f))
        (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved)
        (FB + (D.params f).length) (C f) (evalArgs σ₀ args σ ρ) :=
      ⟨by simp [frei], by have := pre.small; omega, childFrame,
        (childUmf'.code f).1, (childUmf'.code f).2, env, trivial, wstab_true _ _⟩
    obtain ⟨nCall, m2, boundCall, callRun, calleeAgree, frame, hw, resultRead⟩ :=
      calleeRun fitsFun (inside.sub room pre.frame.lt) calleePre hw rpc rfp childUmf'
    have agree : AgreeW L fp (frei Γ reserved) K m m2 :=
      (agreeW_of entryAgree).trans
        ((agreeW_sub pre.frame.lt (by omega) calleeAgree).mono (by omega))
    obtain ⟨w, read, enc⟩ := resultRead τ v result
    change m2.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (BitVec.ofNat 64 2)) = some w at read
    rw [slot_slot] at read
    have parentFrame := frameOK_agreeW pre.frame agree
    have hp1 := pre.left.nextW inside agree (Nat.le_refl _) (Nat.le_refl _) (by omega)
    have move := mov_to_counted hp1.code parentFrame (j := frei Γ reserved) (s := frei Γ reserved + 2)
      (by have h := fitsArgs; simp only [callTop, FB] at h; omega)
      (by have h := fitsArgs; simp only [callTop, FB] at h; omega) pre.small read
    let mMoved := write m2 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) 8 w.toNat
    have moveAgree : Agree fp (frei Γ reserved) K m2 mMoved :=
      agree_write parentFrame.room (Nat.le_refl _) (by have h := fitsArgs; simp only [callTop, FB] at h; omega) _
    have joinedAgree := agree.trans (agreeW_of moveAgree)
    have next := pre.nextW inside joinedAgree (d' := frei Γ reserved + 1)
      (by have := pre.ctx; omega) (by omega)
      (by have h := fitsArgs; simp only [callTop, FB] at h; omega)
    have nextPre : PreS L mMoved _ fp K (frei (τ :: Γ) reserved) cr (.cons v ρ) reserved :=
      ⟨by simp [frei], next.small, next.frame, next.code, next.far,
        envAt_cons next.env (rd_same parentFrame (by have h := fitsArgs; simp only [callTop, FB] at h; omega) w) enc,
        trivial, wstab_true _ _⟩
    have hwMoved : WeltAt mMoved L σ :=
      weltAt_stab inside.lay (by have := inside.top; omega) m2 mMoved hw (moveAgree.mono (Nat.zero_le _))
    have rpc2 : mMoved.rd64 fp = some rp := by
      have h := agreeW_rdW inside joinedAgree (i := 0) (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedPC)
    have rfp2 : mMoved.rd64 (fp + 8) = some cfp := by
      have h := agreeW_rdW inside joinedAgree (i := 1) (by omega) (by omega)
      simpa [slot] using h.trans (by simpa [slot] using savedFP)
    obtain ⟨nRest, m3, boundRest, restRun, finalAgree, frame, hw, resultRead, status⟩ :=
      tail_ih hr (by omega) inside (by simp [frei] at low ⊢; omega) abi lowBound
        (fun j hj => by have := hprotected j hj; simp [frei] at this ⊢; omega) nextPre hwMoved parameters
        (envAt_agreeWIn inside parameterEnv joinedAgree (by omega) (by omega)) base
        (by rw [agreeW_rdW inside joinedAgree (i := 3) (by omega) (by omega)]; exact entry)
        rpc2 rfp2 (Umf.agreeW inside surroundings joinedAgree (by unfold frei FB; omega)) depthBound
    refine ⟨na + 4 + nCall + 1 + nRest, m3, by omega, ?_,
      (joinedAgree.mono (by omega)).trans finalAgree, frame, hw, (by simpa using resultRead), (by simpa using status)⟩
    rw [← len] at rpc
    have joined := entryRun.trans callRun
    rw [← len] at joined
    simp only [pc_add1] at restRun
    have combined := (joined.trans move).trans restRun
    simpa only [pc_add1] using combined

/-- Execute the actual recursive source callee and retain its common return endpoint. -/
theorem ArgsCost.fullRecursiveCall {P : Programm D} {passes : Nat} {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared depth : Nat} {returned : Ausgang (vertragVon D f) false (D.params f)}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {top : Nat}
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31) (depthEq : dv = BitVec.ofNat 64 (depth + 1))
    (depthBound : depth + 2 < 2 ^ 64)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, RecursiveEndCost L P passes A C depth (Ks - frei Γ reserved)
        ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) returned nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    {ca : List II} {ta K : Nat} {m : Mem} {pc fp : W}
    (lowerArgs : lowA L args (frei Γ reserved + FB) reserved = some (ca, ta))
    (fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks)
    (pre : PreS L m pc fp K (frei Γ reserved) (callC A f (frei Γ reserved) ca) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ) :
    ∃ n m', n ≤ declared ∧ Counted (na + 4 + n) ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (ca.length + 4)), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧ WeltAt m' L σ ∧
      (∀ τ v, terminalResult returned = some ⟨τ, v⟩ → ∃ w,
        m'.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved))) 2) = some w ∧ Enc L τ v w) := by
  let childKs := Ks - frei Γ reserved
  have calleeRun {m : Mem} {pc fp rp cfp : W} {K : Nat}
      (fits : top ≤ childKs)
      (inside : WIn L fp childKs K)
      (pre : PreS L m pc fp K (FB + (D.params f).length) (C f)
        (evalArgs σ₀ args σ ρ))
      (world : WeltAt m L σ) (savedPC : m.rd64 fp = some rp)
      (savedFP : m.rd64 (fp + 8) = some cfp)
      (childUmf : Umf L A C (BitVec.ofNat 64 depth) m fp childKs K) :
      ∃ n m', n ≤ declared ∧ Counted n ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧
        AgreeW L fp 2 K m m' ∧ FrameOK m' fp K ∧ WeltAt m' L σ ∧
        (∀ τ v, terminalResult returned = some ⟨τ, v⟩ →
          ∃ w, m'.rd64 (slot fp 2) = some w ∧ Enc L τ v w) := by
    have depthRead := childUmf.depth
    have positive : (BitVec.ofNat 64 depth : W) + 1 ≠ 0 := by
      bv_omega
    have hks := inside.ks
    have lower := lowerFun
    simp only [lowFun] at lower
    split at lower
    next accepted =>
      simp only [Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨⟨cq, tq⟩, hq, ens, hens, ⟨cb, tb⟩, hb, cs, hcs, hc, ht⟩ := lower
      rw [← hc] at pre
      let s := FB + (D.params f).length
      let reserved := (D.params f).length + 2 + 2 * counterDepthE (P.rumpf f)
      have bounds := fits
      rw [← ht] at bounds
      simp only [frei] at bounds
      have hp : PreS L m pc fp K s
          (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ (cs ++
            (relocateC FB reserved (D.params f).length ++ cb))))) (evalArgs σ₀ args σ ρ) := by
        simpa [s, reserved, List.append_assoc] using pre
      have first := guard_pass_counted hp.left.code (by decide) depthRead positive
      have hp1 := hp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      have phases : PreS L m (pc + BitVec.ofNat 64 (16 * (guardC 2 105 s).length)) fp K s ((cq ++ guardC s 101 s) ++
          (cs ++ (relocateC FB reserved (D.params f).length ++ cb))) (evalArgs σ₀ args σ ρ) := by
        simpa [List.append_assoc] using hp1
      have hpq := phases.left
      obtain ⟨m1, rq, a1, env1, _⟩ := requirement.guard hq (by omega) hpq
      have hf1 := hp.frame.agree a1
      have rest := phases.next a1 (Nat.le_refl _) (by omega)
      have world1 := weltAt_stab inside.lay (by have := inside.top; omega) m m1 world (a1.mono (Nat.zero_le _))
      obtain ⟨mS, rs, aS, snap, keep⟩ := snapC_counted hcs hf1 pre.small (by omega)
        rest.left.code rest.left.far world1 inside.lay (by have := inside.top; omega)
      have hfS := hf1.agree aS
      have envS : EnvAt L mS fp (evalArgs σ₀ args σ ρ) := by
        intro τ x
        obtain ⟨w, hw, enc⟩ := env1 τ x
        exact ⟨w, (keep (vslot x) (by have := vslot_lt (reserved := 0) x; unfold frei at this; omega)
          (by unfold vslot FB; omega)).trans hw, enc⟩
      have farS := codeFar_tail rest.far
      have rem : PreS L mS _ fp K s (relocateC FB reserved (D.params f).length ++ cb) (evalArgs σ₀ args σ ρ) :=
        ⟨rest.ctx, pre.small, hfS, (codeAt_right rest.code).agree aS farS,
          farS, envS, trivial, wstab_true _ _⟩
      obtain ⟨mR, rr, aR, moved⟩ := relocate_env_counted hfS pre.small
        (by unfold frei reserved; omega)
        envS rem.left.code (by simpa [relocateC_length] using rem.left.far)
      have ar := Gabbro.Stage0.Senke.Agree.widen aR (show frei (D.params f) (0 + reserved) ≤ K by unfold frei reserved; omega)
      have original := envAt_agree envS ar hfS (by unfold frei FB; omega) (by omega)
      have hpB := rem.next (ar.mono (by simp only [s, FB]; omega)) (Nat.le_refl _) (by omega)
      have bodyPre : PreS L mR _ fp K (frei (D.params f) reserved) cb (evalArgs σ₀ args σ ρ) reserved :=
        ⟨Nat.le_refl _, pre.small, hfS.agree ar, hpB.code, hpB.far,
          by simpa using moved, trivial, wstab_true _ _⟩
      have all : Agree fp 3 K m mR := (a1.mono (by simp only [s, FB]; omega)).trans (aS.trans (ar.mono (by unfold FB; omega)))
      have worldR := weltAt_stab inside.lay (by have := inside.top; omega) m mR world (all.mono (by decide))
      have rpc : mR.rd64 fp = some rp := by
        have h := agree_rd_low (i := 0) all pre.frame.room (by decide) (by omega)
        simpa [slot] using h.trans (by simpa [slot] using savedPC)
      have rfp : mR.rd64 (fp + 8) = some cfp := by
        have h := agree_rd_low (i := 1) all pre.frame.room (by decide) (by omega)
        simpa [slot] using h.trans (by simpa [slot] using savedFP)
      have bodyUmf : Umf L A C (BitVec.ofNat 64 depth) mR fp childKs K := by
        refine ⟨pcode_agree childUmf.code all, ?_, childUmf.big,
          childUmf.sync.agree all childUmf.hiK, childUmf.hiK⟩
        rw [agree_rd_low (i := 2) all pre.frame.room (by decide) (by omega)]
        exact childUmf.depth
      obtain ⟨nBody, m', boundBody, rb, bodyAgree, frame, finalWorld, resultRead, _status⟩ :=
        (body ens hens (rdW mR fp 3)).sound hb (by omega) inside
        (by simp only [frei]; omega) (by simp only [FB]; omega) (by omega)
        (fun _ h => nomatch h) bodyPre worldR (evalArgs σ₀ args σ ρ) original rfl
        (rd64_rdW (hfS.agree ar) (by omega)) rpc rfp bodyUmf (by omega)
      simp only [relocateC_length] at rb
      refine ⟨2 + nq + 2 + cs.length + (D.params f).length + nBody, m', by have := declaration cs hcs; omega, ?_, (agreeW_of (all.mono (by decide))).trans bodyAgree, frame, finalWorld, resultRead⟩
      simpa [s, pc_add, relocateC_length, List.length_append, Nat.add_assoc] using
        first.trans (rq.trans (rs.trans (rr.trans rb)))
    next refused => simp at lower
  have hks := inside.ks
  have room : frei Γ reserved ≤ Ks := by
    have h := fitsArgs
    simp only [callTop] at h
    omega
  obtain ⟨m1, entryRun, entryAgree, childFrame, childUmf, rpc, rfp, env, hw⟩ :=
    arguments.recursiveEntry lowerArgs fitsArgs address pre surroundings inside world
  have childUmf' : Umf L A C (BitVec.ofNat 64 depth) m1
      (slot fp (BitVec.ofNat 64 (frei Γ reserved))) childKs (K - frei Γ reserved) := by
    rw [depthEq] at childUmf
    have deq : (BitVec.ofNat 64 (depth + 1) : W) - 1 = BitVec.ofNat 64 depth := by bv_omega
    simpa only [deq] using childUmf
  have calleePre : PreS L m1 (BitVec.ofNat 64 (A f))
      (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved)
      (FB + (D.params f).length) (C f) (evalArgs σ₀ args σ ρ) :=
    ⟨by simp [frei], by have := pre.small; omega, childFrame,
      (childUmf'.code f).1, (childUmf'.code f).2, env, trivial, wstab_true _ _⟩
  obtain ⟨nCall, m2, boundCall, callRun, calleeAgree, frame, hw, resultRead⟩ :=
    calleeRun fitsFun (inside.sub room pre.frame.lt) calleePre hw rpc rfp childUmf'
  have agree : AgreeW L fp (frei Γ reserved) K m m2 :=
    (agreeW_of entryAgree).trans
      ((agreeW_sub pre.frame.lt (by omega) calleeAgree).mono (by omega))
  exact ⟨nCall, m2, boundCall, entryRun.trans callRun, agree, hw, resultRead⟩

/-- Accepted next/leave lowering executes one jump, preserving the same
    source world, environment and protected cells at its actual exit ABI. -/
theorem loopJump_counted (next : Bool)
    {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    {passes lo K top : Nat} {A : D.Fn → Nat} {ens : List II × Nat}
    {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp : W} {σ : World D} {ρ : Env D Γ}
    (lower : lowS (reserved := reserved) passes A L lo ens pr ex
      (show Stmt D V true Γ Λ Λ from
        if next then .next rfl else .leave rfl) = some (code, top))
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach 1 L fp lo K pr ⟨pc, fp⟩ m
      (pc + 16 + BitVec.ofInt 64 (if next then ex.2 else ex.1)) σ ρ reserved := by
  cases next <;> simp only [Bool.false_eq_true, ↓reduceIte, lowS] at lower ⊢
  all_goals
    split at lower
    · next fits =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj lower
      exact jmp_counted_reach pre.code fits pre.env world
    · cases lower


/-- A jump at the head exits across the entire actual lowered block. -/
theorem loopJumpBlock_counted (next : Bool)
    {V : Vertrag D} {Γ : Ctx} {Λ Ξ : List (Res D)}
    {rest : Block D V true Γ Λ Ξ}
    {passes lo K top : Nat} {A : D.Fn → Nat} {ens : List II × Nat}
    {pr : List Nat} {ex : Int × Int} {code : List II}
    {m : Mem} {pc fp : W} {σ : World D} {ρ : Env D Γ}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex
      (.cons (if next then .next rfl else .leave rfl) rest) = some (code, top))
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (world : WeltAt m L σ) :
    CountedReach 1 L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length) +
        BitVec.ofInt 64 (if next then ex.2 else ex.1)) σ ρ reserved := by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs, hc⟩ := lower
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  have result := loopJump_counted next hs pre.left world
  have shape : cs.length = 1 := by
    cases next <;> simp only [Bool.false_eq_true, ↓reduceIte, lowS] at hs
    all_goals
      split at hs
      · obtain ⟨rfl, rfl⟩ := Option.some.inj hs; rfl
      · cases hs
  have target : pc + 16 + BitVec.ofInt 64
      (if next then (exPlus ex cr.length).2 else (exPlus ex cr.length).1) =
      pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) +
        BitVec.ofInt 64 (if next then ex.2 else ex.1) := by
    cases next <;> simp only [Bool.false_eq_true, ↓reduceIte, exPlus, List.length_append, shape]
    all_goals
      change pc + BitVec.ofNat 64 (16 * 1) + _ = _
      exact tgt_eq (by omega)
  rw [target] at result
  exact result

/-- Reserved initialization retains the source state without requiring a return
    header: a hardware stop does not return to that header. -/
theorem reserved_literal_source_entry
    {Γ : Ctx} {fp pc : W} {K Ks reserved cell : Nat}
    {σ : World D} {ρ : Env D Γ} {m : Mem} {code : List II} {value : Int}
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved) ([ci 1 cell value 0] ++ code) ρ reserved)
    (world : WeltAt m L σ)
    (lowerCell : FB ≤ cell) (allocated : cell < FB + reserved) (bound : frei Γ reserved ≤ K)
    (literal : lit32 value = true) :
    ∃ m', Counted 1 ⟨pc, fp⟩ m ⟨pc + 16, fp⟩ m' ∧
      PreS L m' (pc + 16) fp K (frei Γ reserved) code ρ reserved ∧
      WeltAt m' L σ ∧ Agree fp cell K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 cell)) = some (BitVec.ofInt 64 value) := by
  have inside : cell < K := by unfold frei at bound; omega
  have run := const_step_counted (codeAt_left pre.code) pre.frame inside pre.small literal
  obtain ⟨write, stored, frame⟩ := wr_slot pre.frame inside (BitVec.ofInt 64 value)
  have env := (reserved_write_preserves (L := L) (j := cell - FB)
    (BitVec.ofInt 64 value).toNat pre.frame.room bound (by omega) pre.env).1
  have eq : FB + (cell - FB) = cell := by
    have := layout.lo
    omega
  rw [eq] at env
  have far := codeFar_right (n := 1) (k := code.length)
    (by simpa [Nat.add_comm] using pre.far)
  refine ⟨_, run, ?_, ?_, frame, stored⟩
  · exact ⟨pre.ctx, pre.small, pre.frame.agree frame,
      (codeAt_right pre.code).agree frame far, far, env, trivial, wstab_true _ _⟩
  · exact weltAt_stab layout.lay layout.top m _ world (frame.mono (Nat.zero_le _))

/-- A positive header consumes two S0IR instructions and decrements the
    counter once. The child starts in the same world and lexical environment, with the
    decremented counter and immutable one jointly available in its memory. -/
theorem counter_positive_source_counted
    {Γ : Ctx} {fp pc : W} {K Ks reserved counter one : Nat}
    {σ : World D} {ρ : Env D Γ} {m : Mem} {code : List II}
    {jump : Int} {fuel : W}
    (layout : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounter counter one jump ++ code) ρ reserved)
    (world : WeltAt m L σ)
    (lowerCell : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (bound : frei Γ reserved ≤ K)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some fuel)
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (positive : fuel ≠ 0) :
    ∃ m', Counted 2 ⟨pc, fp⟩ m ⟨pc + 16 + 16, fp⟩ m' ∧
      PreS L m' (pc + 16 + 16) fp K (frei Γ reserved) code ρ reserved ∧
      WeltAt m' L σ ∧ Agree fp counter K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (fuel - 1) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1 := by
  have cellBound : counter < K := by unfold frei at bound; omega
  have oneBound : one < K := by unfold frei at bound; omega
  have counterSmall : counter < 2 ^ 31 := by have := pre.small; omega
  have oneSmall : one < 2 ^ 31 := by have := pre.small; omega
  have first := pre.code 0 (by simp [foreverCounter])
  simp only [foreverCounter, List.cons_append, List.getElem_cons_zero,
    ci, Nat.mul_zero, BitVec.add_zero] at first
  have test := counter_positive (t := ⟨pc, fp⟩) first
    (by rw [sx_nat counterSmall]; exact read) positive
  have rest : PreS L m (pc + 16) fp K (frei Γ reserved)
      ([ci 4 counter counter one] ++ code) ρ reserved := by
    have h := pre.next (a := [ci 19 counter jump 0])
      (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    simpa [foreverCounter] using h
  obtain ⟨write, stored, agree⟩ := wr_slot rest.frame cellBound (fuel - 1)
  have ins : InsAt m (pc + 16) 4 (II.f (counter : Int))
      (II.f (counter : Int)) (II.f (one : Int)) := by
    simpa [ci] using rest.code 0 (by simp)
  have decrement := counter_decrement (t := ⟨pc + 16, fp⟩) ins
    (by rw [sx_nat counterSmall]; exact read)
    (by rw [sx_nat oneSmall]; exact readOne)
    (by rw [sx_nat counterSmall]; exact write)
  have env := (reserved_write_preserves (L := L) (j := counter - FB)
    (fuel - 1).toNat pre.frame.room bound (by omega) pre.env).1
  have cellEq : FB + (counter - FB) = counter := by omega
  rw [cellEq] at env
  have far := codeFar_right (n := 1) (k := code.length)
    (by simpa [Nat.add_comm] using rest.far)
  refine ⟨_, (Counted.next test (.refl _ _)).trans
    (Counted.next decrement (.refl _ _)), ?_, ?_, agree, stored, ?_⟩
  · exact ⟨pre.ctx, pre.small, pre.frame.agree agree,
      (codeAt_right rest.code).agree agree far, far, env, trivial, wstab_true _ _⟩
  · exact weltAt_stab layout.lay layout.top m _ world (agree.mono (Nat.zero_le _))
  · rw [Mem.rd64_write_far (slot_far pre.frame.room cellBound oneBound (by omega))]
    exact readOne

/-- The progress exit executes its real zero test and two stop constants.
    The syscall remains pending: neither hardware completion nor latency is
    inferred. All joint source-state facts refer to that same final memory. -/
theorem counter_budget_stop_counted
    {Γ : Ctx} {m : Mem} {pc fp : W} {K Ks lo scratch : Nat}
    {pr : List Nat} {σ : World D} {ρ : Env D Γ}
    {d jump : BitVec 32}
    (test : InsAt m pc 19 d jump 0)
    (zero : m.rd64 (slot fp (sx d)) = some 0)
    (pre : PreS L m (pc + sx jump) fp K (frei Γ reserved)
      (stopC 111 scratch) ρ reserved)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ)
    (low : lo ≤ scratch) (locals : frei Γ reserved ≤ scratch)
    (room : scratch + 8 ≤ K) (hprotected : ∀ j ∈ pr, j < scratch) :
    ∃ t m' q, Counted 3 ⟨pc, fp⟩ m t m' ∧ StopAt t m' q ∧
      q.nr = 231 ∧ q.a1 = 111 ∧ AgreeW L fp lo K m m' ∧
      EnvAt L m' fp ρ reserved ∧ WeltAt m' L σ ∧ Keeps fp pr m m' := by
  obtain ⟨t, m', q, run, stop, nr, arg, agree⟩ :=
    sys_counted_frame pre.code pre.far pre.frame room pre.small (by decide) (by decide)
  have aw : AgreeW L fp lo K m m' := agreeW_of (agree.mono low)
  have first : Counted 1 ⟨pc, fp⟩ m ⟨pc + sx jump, fp⟩ m :=
    .next (counter_zero test zero) (.refl _ _)
  refine ⟨t, m', q, first.trans run,
    stop, nr, arg, aw, ?_, ?_, ?_⟩
  · exact envAt_agree pre.env agree pre.frame locals (by omega)
  · exact weltAt_stab inside.lay inside.top m m' world
      (agree.mono (Nat.zero_le _))
  · exact keeps_of_agreeW inside (agreeW_of agree) hprotected (by omega)


/-- The complete emitted zero-budget loop executes five S0IR instructions.
    Neither the invariant nor the body is run or assumed to terminate. -/
theorem forever_zero_source_counted
    {Γ : Ctx} {fp pc : W} {K Ks counter one scratch : Nat}
    {σ : World D} {ρ : Env D Γ} {m : Mem} {cc cb : List II}
    (inside : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCode counter one scratch 0 cc cb) ρ reserved)
    (world : WeltAt m L σ)
    (counterLow : FB ≤ counter) (counterOne : counter < one)
    (oneAllocated : one < FB + reserved)
    (locals : frei Γ reserved ≤ K) (room : scratch + 8 ≤ K)
    (jumpFits : 16 * (cc.length + cb.length + 8) < 2 ^ 31) :
    CountedStops 5 ⟨pc, fp⟩ m 111 := by
  obtain ⟨m1, run1, pre1, world1, agree1, read1⟩ :=
    reserved_literal_source_entry inside pre world counterLow (by omega) locals (by decide)
  obtain ⟨m2, run2, pre2, world2, agree2, read2⟩ :=
    reserved_literal_source_entry inside pre1 world1 (by omega) oneAllocated locals (by decide)
  have zero : m2.rd64 (slot fp (BitVec.ofNat 64 counter)) = some 0 := by
    rw [agree_rd_low agree2 pre1.frame.room counterOne (by unfold frei at locals; omega)]
    exact read1
  have ins := pre2.code 0 (by simp [foreverCounter])
  simp only [foreverCounter, ci, List.getElem_cons_zero, List.cons_append,
    List.getElem_append_left, Nat.mul_zero, BitVec.add_zero] at ins
  have counterSmall : counter < 2 ^ 31 := by have := pre.small; unfold frei at locals; omega
  have branch := counter_zero (t := ⟨pc + 16 + 16, fp⟩) ins (by rw [sx_nat counterSmall]; exact zero)
  have header : PreS L m2 (pc + 16 + 16) fp K (frei Γ reserved)
      ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 scratch ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 scratch) ρ reserved := by
    simpa [foreverCounter, List.append_assoc, List.append] using pre2
  have tail := header.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have address : (pc + 16 + 16) + sx (II.f (16 * (cc.length + cb.length + 8) : Int)) =
      (pc + 16 + 16) + BitVec.ofNat 64 (16 *
        (foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 scratch ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]).length) := by
    have castEq : (16 * ((cc.length : Int) + cb.length + 8)) =
        ((16 * (cc.length + cb.length + 8) : Nat) : Int) := by omega
    rw [castEq, sx_nat jumpFits]
    simp [foreverCounter, stopC, sysC, List.length_append, Nat.add_assoc]
  obtain ⟨u, a, q, stopRun, stop, nr, arg⟩ :=
    sys_counted tail.code tail.far tail.frame room pre.small (by decide) (by decide)
  rw [← address] at stopRun
  refine ⟨u, a, q, ?_, stop, nr, arg⟩
  exact (run1.trans run2).trans ((Counted.next branch (Counted.refl _ _)).trans stopRun)




/-- Zero-counter base at reentry, without executing the initial literals again. -/
theorem forever_zero_header_counted
    {Γ : Ctx} {fp pc : W} {K Ks counter one scratch : Nat}
    {σ : World D} {ρ : Env D Γ} {m : Mem} {cc cb : List II}
    (inside : WIn L fp Ks K)
    (pre : PreS L m pc fp K (frei Γ reserved)
      ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 scratch ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 scratch) ρ reserved)
    (world : WeltAt m L σ)
    (locals : frei Γ reserved ≤ K) (room : scratch + 8 ≤ K)
    (jumpFits : 16 * (cc.length + cb.length + 8) < 2 ^ 31)
    (zero : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some 0)
    (counterBound : counter < frei Γ reserved) :
    CountedStops 3 ⟨pc, fp⟩ m 111 := by
  have ins := pre.code 0 (by simp [foreverCounter])
  simp only [foreverCounter, ci, List.getElem_cons_zero, List.cons_append,
    List.getElem_append_left, Nat.mul_zero, BitVec.add_zero] at ins
  have counterSmall : counter < 2 ^ 31 := by have := pre.small; omega
  have branch := counter_zero (t := ⟨pc, fp⟩) ins (by rw [sx_nat counterSmall]; exact zero)
  have header : PreS L m pc fp K (frei Γ reserved)
      ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 scratch ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 scratch) ρ reserved := by
    simpa [foreverCounter, List.append_assoc, List.append] using pre
  have tail := header.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have address : pc + sx (II.f (16 * (cc.length + cb.length + 8) : Int)) =
      pc + BitVec.ofNat 64 (16 *
        (foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 scratch ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]).length) := by
    have castEq : (16 * ((cc.length : Int) + cb.length + 8)) =
        ((16 * (cc.length + cb.length + 8) : Nat) : Int) := by omega
    rw [castEq, sx_nat jumpFits]
    simp [foreverCounter, stopC, sysC, List.length_append, Nat.add_assoc]
  obtain ⟨u, a, q, stopRun, stop, nr, arg⟩ :=
    sys_counted tail.code tail.far tail.frame room pre.small (by decide) (by decide)
  rw [← address] at stopRun
  refine ⟨u, a, q, ?_, stop, nr, arg⟩
  exact (Counted.next branch (Counted.refl _ _)).trans stopRun


/-- Recursive source call certificates. Every node stores source-derived callee
    costs and a recursive continuation, never an assumed execution of the whole block. -/
inductive recursiveBlockCost (L : Lay D) (reserved : Nat) (P : Programm D)
    (passes : Nat) (A : D.Fn → Nat) (C : D.Fn → List II) (dv : W) (Ks : Nat)
    (V : Vertrag D) (l : Bool) :
    {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' →
      World D → Env D Γ → Ausgang V l Γ → Nat → Type
  | source {Γ Λ Λ'} {b : Block D V l Γ Λ Λ'} {σ σ' : World D}
      {ρ ρ' : Env D Γ} {n : Nat}
      (source : BlockCost L reserved V l b σ ρ σ' ρ' n) :
      recursiveBlockCost L reserved P passes A C dv Ks V l b σ ρ (.ok σ' ρ') n
  | call {Γ : Ctx} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared depth : Nat} {returned : Ausgang (vertragVon D f) false (D.params f)}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {top : Nat}
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31) (depthEq : dv = BitVec.ofNat 64 (depth + 1))
    (depthBound : depth + 2 < 2 ^ 64)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, RecursiveEndCost L P passes A C depth (Ks - frei Γ reserved)
        ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) returned nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    {Λ' : List (Res D)}
    {rest : Block D V l Γ (nach D f Λ) Λ'} {outcome : Ausgang V l Γ}
    {nr : Nat}
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    (tail : recursiveBlockCost L reserved P passes A C dv Ks V l rest σ ρ outcome nr) :
    recursiveBlockCost L reserved P passes A C dv Ks V l
      (.cons (.call f args hp hr) rest) σ ρ outcome (na + 4 + declared + nr)

  | bindCall {Γ : Ctx} {τ : Ty} {v : Wert D τ} {Λ : List (Res D)} {f : D.Fn}
    {args : Args D Γ Λ (D.params f)} {σ₀ σ : World D} {ρ : Env D Γ} {na nq nb declared depth : Nat} {returned : Ausgang (vertragVon D f) false (D.params f)}
    (arguments : ArgsCost L reserved (frei Γ reserved) args σ₀ σ ρ na)
    {top : Nat}
    (lowerFun : lowFun passes P A L f = some (C f, top))
    (fitsFun : top ≤ Ks - frei Γ reserved)
    (address : A f < 2 ^ 31) (depthEq : dv = BitVec.ofNat 64 (depth + 1))
    (depthBound : depth + 2 < 2 ^ 64)
    (requirement : ExprCost L 0 (P.requires f) (FB + (D.params f).length) nq (· = 1))
    (body : ∀ ens, lowEns L (P.ensures f) (FB + (D.params f).length + 1) = some ens →
      ∀ snapshot, RecursiveEndCost L P passes A C depth (Ks - frei Γ reserved)
        ((D.params f).length + 2 + 2 * counterDepthE (P.rumpf f))
        (vertragVon D f) false (D.params f) snapshot ens (FB + (D.params f).length)
        (P.rumpf f) σ (evalArgs σ₀ args σ ρ) returned nb)
    (declaration : ∀ cs, snapC L (oldCells (P.ensures f)) = some cs →
      2 + nq + 2 + cs.length + (D.params f).length + nb ≤ declared)
    (result : terminalResult returned = some ⟨τ, v⟩)
    {he : D.erg f = some τ}
    {Λ' : List (Res D)}
    {rest : Block D V l (τ :: Γ) (nach D f Λ) Λ'} {outcome : Ausgang V l (τ :: Γ)}
    {nr : Nat}
    {hp : RufPasst D V (D.signatur f) Λ} {hr : D.gruende f = 0}
    (tail : recursiveBlockCost L reserved P passes A C dv Ks V l rest σ (.cons v ρ) outcome nr) :
    recursiveBlockCost L reserved P passes A C dv Ks V l
      (.bindCall f args he hp hr rest) σ ρ outcome.schrumpf (na + 4 + declared + 1 + nr)

  | jump {Γ Λ Ξ} {rest : Block D V l Γ Λ Ξ} {σ : World D} {ρ : Env D Γ}
      (h : l = true) (next : Bool) :
      recursiveBlockCost L reserved P passes A C dv Ks V l
        (.cons (if next then .next h else .leave h) rest) σ ρ
        (if next then .next h σ ρ else .leave h σ ρ) 1

  | sourceStop {Γ Λ Ξ} {assumption : D.Annahme}
      {inv : Expr D Γ Λ .bool} {body : Block D V true Γ Λ Λ}
      {rest : Block D V l Γ Λ Ξ} {σ : World D} {ρ : Env D Γ}
      (zero : passes = 0)
      (imageFits : ∀ lo ens pr ex code top,
        lowS (l := l) (reserved := reserved) passes A L lo ens pr ex
          (.forever assumption inv body) = some (code, top) →
        16 * code.length < 2 ^ 31) :
      recursiveBlockCost L reserved P passes A C dv Ks V l
        (.cons (.forever assumption inv body) rest) σ ρ
        (.hardware (.fortschritt assumption)) 5

/-- Induction composes each full call and its child certificate at the identical
    counted endpoint, retaining world, environment, frame and protected cells. -/
theorem recursiveBlockCost.sound {P : Programm D} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {f0 : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {b : Block D (vertragVon D f0) l Γ Λ Λ'} {σ σ0 : World D} {ρ : Env D Γ}
    {ρ0 : Env D (D.params f0)} {rp cfp : W} {outcome : Ausgang (vertragVon D f0) l Γ} {budget : Nat}
    (certificate : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f0) l b σ ρ outcome budget)
    {lo K top : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ) :
    ∃ n, n ≤ budget ∧ CountedSim n L P f0 σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length))
      (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2) outcome reserved := by
  induction certificate generalizing lo top code m pc ex with
  | source cert => exact ⟨_, Nat.le_refl _, cert.sound lower fits inside low hprotected pre world⟩
  | @sourceStop Γ Λ Ξ assumption inv body rest σ ρ zero imageFits =>
    subst passes
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cr, tr⟩, lowerTail, ⟨cs, ts⟩, lowerStmt, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    have imageBound := imageFits _ _ _ _ _ _ lowerStmt
    dsimp only [lowS] at lowerStmt
    split at lowerStmt
    next allowed =>
      obtain ⟨cc, hcc, emitted⟩ := Option.bind_eq_some_iff.mp lowerStmt
      obtain ⟨cb, tb, hcb, rfl, htc, htb, hcounter, hone, hscratch⟩ := foreverC_actual emitted
      have hks := inside.ks
      have pairStep : (counterPair reserved (counterDepthB body)).2 =
          (counterPair reserved (counterDepthB body)).1 + 1 := rfl
      have run := forever_zero_source_counted inside pre.left world
        (by have := allowed.1; unfold FB at *; omega) (by omega)
        allowed.2.1 (by have := pre.ctx; omega) (by omega) (by
          simp only [foreverCode_length] at imageBound
          omega)
      exact ⟨5, Nat.le_refl _, run⟩
    next refused => simp at lowerStmt
  | jump h next =>
    cases h
    refine ⟨1, Nat.le_refl _, ?_⟩
    have run := loopJumpBlock_counted next lower pre world
    cases next <;> exact run
  | @call Γ Λ f args σ₀ σ ρ na nq nb declared depth returned arguments topFun lowerFun fitsFun address depthEq depthBound requirement body declaration Λ' rest outcome nr hp hr tail ih =>
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨cr, tr⟩, lowerTail, ⟨cs, ts⟩, lowerStmt, out⟩ := lower
    simp only [lowS, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lowerStmt
    obtain ⟨⟨ca, ta⟩, lowerArgs, stmtOut⟩ := lowerStmt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj stmtOut
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    change max (callTop f (frei Γ reserved) ta) tr ≤ Ks at fits
    have fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks := by omega
    have room : frei Γ reserved ≤ Ks := by
      have h := fitsArgs
      simp only [callTop] at h
      omega
    obtain ⟨n, m1, bound, run, agree, hw, resultRead⟩ :=
      arguments.fullRecursiveCall lowerFun fitsFun address depthEq depthBound
        requirement body declaration lowerArgs fitsArgs pre.left surroundings inside world
    have hks := inside.ks
    have next := pre.nextW inside agree (Nat.le_refl _) (Nat.le_refl _) (by omega)
    have len : (callC A f (frei Γ reserved) ca).length = ca.length + 4 := by
      simp [callC, callTail, callTailN, List.length_append]
    obtain ⟨nt, boundTail, restRun⟩ :=
      ih lowerTail (by omega) abi low hprotected next
        (Umf.agreeW inside surroundings agree (by simp [frei]; omega)) hw
    rw [← len] at run
    refine ⟨na + 4 + n + nt, by omega, ?_⟩
    have result := CountedSim.prefix abi run (agree.mono low)
      (keeps_of_agreeW inside agree hprotected (by omega)) restRun
    simpa only [pc_add1, pc_add, List.length_append, len, exPlus, tgt_eq] using result

  | @bindCall Γ τ v Λ f args σ₀ σ ρ na nq nb declared depth returned arguments topFun lowerFun fitsFun address depthEq depthBound requirement body declaration result he Λ' rest outcome nr hp hr tail ih =>
    simp only [lowB, Bind.bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at lower
    obtain ⟨⟨ca, ta⟩, lowerArgs, ⟨cr, tr⟩, lowerTail, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj out
    change max (callTop f (frei Γ reserved) ta) tr ≤ Ks at fits
    have fitsArgs : callTop f (frei Γ reserved) ta ≤ Ks := by omega
    have room : frei Γ reserved + 2 < Ks := by
      have h := fitsArgs
      simp only [callTop, FB] at h
      omega
    obtain ⟨n, m1, bound, run, agree, hw, resultRead⟩ :=
      arguments.fullRecursiveCall lowerFun fitsFun address depthEq depthBound
        requirement body declaration lowerArgs fitsArgs pre.left.left surroundings inside world
    obtain ⟨w, read, enc⟩ := resultRead _ _ result
    have frame := frameOK_agreeW pre.frame agree
    change m1.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (BitVec.ofNat 64 2)) = some w at read
    rw [slot_slot] at read
    have hks := inside.ks
    have hp1 := pre.left.nextW inside agree (Nat.le_refl _) (Nat.le_refl _) (by omega)
    have move := mov_to_counted hp1.code frame (j := frei Γ reserved) (s := frei Γ reserved + 2)
      (by omega) (by omega) pre.small read
    let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) 8 w.toNat
    have a2 : Agree fp (frei Γ reserved) K m1 m2 :=
      agree_write frame.room (Nat.le_refl _) (by omega) _
    have joinedAgree := agree.trans (agreeW_of a2)
    have next := pre.nextW inside joinedAgree (d' := frei Γ reserved + 1)
      (by have := pre.ctx; omega) (by omega) (by omega)
    have nextPre : PreS L m2 _ fp K (frei (τ :: Γ) reserved) cr (.cons v ρ) reserved :=
      ⟨by simp [frei], next.small, next.frame, next.code, next.far,
        envAt_cons next.env (rd_same frame (by omega) w) enc, trivial, wstab_true _ _⟩
    have hw2 : WeltAt m2 L σ :=
      weltAt_stab inside.lay (by have := inside.top; omega) m1 m2 hw (a2.mono (Nat.zero_le _))
    obtain ⟨nt, bt, rr⟩ :=
      ih lowerTail (by omega) abi (by simp [frei] at *; omega)
        (fun j hj => by have := hprotected j hj; simp [frei] at *; omega) nextPre
        (Umf.agreeW inside surroundings joinedAgree (by simp [frei]; omega)) hw2
    have len : (callC A f (frei Γ reserved) ca).length = ca.length + 4 := by
      simp [callC, callTail, callTailN, List.length_append]
    rw [← len] at run
    refine ⟨na + 4 + n + 1 + nt, by omega, ?_⟩
    have shrunk := CountedSim.shrink (outcome := outcome) rr
    simp only [pc_add1] at shrunk
    have result := CountedSim.prefix abi (run.trans move) (joinedAgree.mono low)
      (keeps_of_agreeW inside joinedAgree hprotected (by omega)) shrunk
    simpa only [pc_add1, pc_add, List.length_append, len, exPlus, tgt_eq, Nat.add_assoc] using result

/-- Normal fallthrough is a specialization of canonical outcome soundness. -/
theorem recursiveBlockCost.sound_normal {P : Programm D} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {f0 : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {b : Block D (vertragVon D f0) l Γ Λ Λ'} {σ σ0 : World D} {ρ : Env D Γ}
    {ρ0 : Env D (D.params f0)} {rp cfp : W} {σ' : World D} {ρ' : Env D Γ} {budget : Nat}
    (certificate : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f0) l b σ ρ (.ok σ' ρ') budget)
    {lo K top : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ) :
    ∃ n, n ≤ budget ∧ CountedReach n L fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length)) σ' ρ' reserved := by
  exact certificate.sound (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp)
    lower fits inside abi low hprotected pre surroundings world

/-- The actual positive forever pass, with a source invariant certificate and
    a recursive body certificate. The body may execute full recursive calls.
    This establishes the normal/backedge endpoint only; early source outcomes
    require their own indexed certificates before a whole-loop constructor can
    use this result. No bound on an entire loop execution is a premise. -/
theorem recursiveBlockCost.forever_pass
    {P : Programm D} {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II}
    {dv : W} {Ks : Nat} {f0 : D.Fn} {Γ : Ctx} {Λ : List (Res D)}
    {inv : Expr D Γ Λ .bool} {body : Block D (vertragVon D f0) true Γ Λ Λ}
    {σ σ' σ0 : World D} {ρ0 : Env D (D.params f0)} {rp cfp : W} {ρ ρ' : Env D Γ} {ni nb : Nat}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
    (child : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f0) true body
      (σ.lese Λ inv.orte) ρ (.ok σ' ρ') nb)
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {cc cb : List II} {m : Mem} {pc fp : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr (exPlus ex 4) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ) :
    ∃ n, n ≤ ni + 1 + nb + 1 ∧
      CountedReach n L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * (cc.length + 1 + cb.length + 4))) σ' ρ' reserved := by
  have hks := inside.ks
  have normalize (x y : Nat) : 16 + (16 * x + (16 * y + 64)) =
      16 * x + (16 * y + 80) := by omega
  have room := lowE_top _ _ _ _ lowerInv
  have hpw := PreS.welt pre.left inside.ks world inside.lay (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, w, read, value⟩ := invariant.sound lowerInv (by omega) hpw
  subst w
  have a1 := Agree.widen a1s inside.ks
  have h1 := pre.next a1 (Nat.le_refl _) (by omega)
  have h2 := h1.next (a := [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0])
    (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have ins := h1.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
  have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
    sx_nat (by have := pre.small; omega)
  have branch := counted_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
    (by simp only [ci]; exact run_brz_ne ins (by rw [hd]; exact read) (by decide))
  have world1 := hpw.wstab m m1 world (a1s.mono (Nat.zero_le _))
  obtain ⟨n, bound, m2, run2, agree, env, hw, keep⟩ := child.sound_normal (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp) lowerBody fitsBody inside
    abi low hprotected h2.left
    (Umf.agreeW inside surroundings (agreeW_of a1) (by simp [frei]; omega)) world1
  have h3 : PreS L m2 _ fp K (frei Γ reserved)
      ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)) ρ' reserved :=
    ⟨h2.ctx, h2.small, frameOK_agreeW h2.frame agree,
      codeAt_agreeWIn inside agree (codeAt_right h2.code)
        (codeFar_right (by simpa only [List.length_append] using h2.far)),
      codeFar_right (by simpa only [List.length_append] using h2.far),
      env, trivial, wstab_true _ _⟩
  have ji := h3.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ji
  have jump := run_step (t := ⟨_, fp⟩) ji (by decide) (run_jmp ji)
  have offset : sx (II.f 64) = (64 : W) := by decide
  rw [offset] at jump
  refine ⟨ni + 1 + n + 1, by omega, m2, ?_,
    (agreeW_of (a1.mono low)).trans agree, env, hw, ?_⟩
  · simpa [List.length_append, List.length_singleton, pc_add, addr_norm,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, normalize] using
      run1.trans (branch.trans (run2.trans (Counted.next jump (Counted.refl _ _))))
  · exact (keeps_of_agreeW inside (agreeW_of a1) hprotected
      (by have := inside.ks; omega)).trans keep


/-- A false source invariant reaches the actual failure block in the same joint
    state after the expression and one branch. The pending stop is separate. -/
theorem recursiveBlockCost.forever_false_invariant
    {P : Programm D} {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II}
    {dv : W} {Ks : Nat} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    {inv : Expr D Γ Λ .bool} {body : Block D V true Γ Λ Λ}
    {σ σ' : World D} {ρ ρ' : Env D Γ} {ni : Nat}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 0))
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {cc cb : List II} {m : Mem} {pc fp : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr (exPlus ex 4) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ) :
    CountedReach (ni + 1) L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * cc.length) + sx (II.f (16 * (cb.length + 2) : Int))) σ ρ reserved := by
  have hks := inside.ks
  have room := lowE_top _ _ _ _ lowerInv
  have hpw := PreS.welt pre.left inside.ks world inside.lay (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, w, read, value⟩ := invariant.sound lowerInv (by omega) hpw
  subst w
  have a1 := Agree.widen a1s inside.ks
  have h1 := pre.next a1 (Nat.le_refl _) (by omega)
  have ins := h1.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
  have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
    sx_nat (by have := pre.small; omega)
  have branch := run_step (t := ⟨_, fp⟩) ins (by decide)
    (run_brz_zero ins (by rw [hd]; exact read))
  refine ⟨m1, ?_, agreeW_of (a1.mono low), ?_, ?_, ?_⟩
  · simpa [pc_add, addr_norm, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      run1.trans (Counted.next branch (Counted.refl _ _))
  · exact envAt_agreeW pre.env (agreeW_of a1) inside.top
      pre.frame.room (Nat.le_refl _) (by omega)
  · exact hpw.wstab m m1 world (a1s.mono (Nat.zero_le _))
  · exact keeps_of_agreeW inside (agreeW_of a1) hprotected (by omega)

/-- A false invariant executes the emitted failure path: the expression,
    branch and two stop constants. The syscall stays pending. -/
theorem forever_false_stop_counted
    {P : Programm D} {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II}
    {dv : W} {Ks : Nat} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    {inv : Expr D Γ Λ .bool} {body : Block D V true Γ Λ Λ}
    {σ σ' : World D} {ρ ρ' : Env D Γ} {ni : Nat}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 0))
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {cc cb : List II} {m : Mem} {pc fp : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr (exPlus ex 4) body = some (cb, tb))
    (jumpFits : 16 * (cb.length + 2) < 2 ^ 31)
    (stopRoom : frei Γ reserved + 8 ≤ K)
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ) :
    CountedStops (ni + 3) ⟨pc, fp⟩ m 104 := by
  have hks := inside.ks
  have room := lowE_top _ _ _ _ lowerInv
  have hpw := PreS.welt pre.left inside.ks world inside.lay (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, w, read, value⟩ := invariant.sound lowerInv (by omega) hpw
  subst w
  have a1 := Agree.widen a1s inside.ks
  have h1 := pre.next a1 (Nat.le_refl _) (by omega)
  have ins := h1.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
  have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
    sx_nat (by have := pre.small; omega)
  have branch := run_step (t := ⟨_, fp⟩) ins (by decide)
    (run_brz_zero ins (by rw [hd]; exact read))
  have h1assoc : PreS L m1 (pc + BitVec.ofNat 64 (16 * cc.length)) fp K
      (frei Γ reserved) (([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ [ci 18 64 0 0])) ++ stopC 104 (frei Γ reserved)) ρ reserved := by
    simpa only [List.append_assoc] using h1
  have stopPre := h1assoc.next (a :=
      [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ [ci 18 64 0 0]))
    (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have jumpEq : sx (II.f (16 * (cb.length + 2) : Int)) =
      BitVec.ofNat 64 (16 * (cb.length + 2)) := sx_nat jumpFits
  have address : pc + BitVec.ofNat 64 (16 * cc.length) +
      sx (II.f (16 * (cb.length + 2) : Int)) =
      (pc + BitVec.ofNat 64 (16 * cc.length)) +
        BitVec.ofNat 64 (16 *
          ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
            (cb ++ [ci 18 64 0 0])).length) := by
    rw [jumpEq]
    simp [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have stopCode : CodeAt m1
      (pc + BitVec.ofNat 64 (16 * cc.length) +
        sx (II.f (16 * (cb.length + 2) : Int)))
      (stopC 104 (frei Γ reserved)) := by
    rw [address]
    exact stopPre.code
  have stopFar : CodeFar
      (pc + BitVec.ofNat 64 (16 * cc.length) +
        sx (II.f (16 * (cb.length + 2) : Int))) 3 fp K := by
    rw [address]
    exact stopPre.far
  obtain ⟨t, m2, q, runStop, stopped, nr, arg⟩ :=
    sys_counted stopCode stopFar stopPre.frame stopRoom pre.small (by decide) (by decide)
  refine ⟨t, m2, q, ?_, stopped, nr, arg⟩
  have firstRun : Counted (ni + 1) ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * cc.length) +
        sx (II.f (16 * (cb.length + 2) : Int)), fp⟩ m1 :=
    run1.trans (Counted.next branch (Counted.refl _ _))
  simpa [Nat.add_assoc] using firstRun.trans runStop

/-- Execute the actual invariant and positive dispatch before a body with any
    canonical outcome. In particular, returns keep their caller frame endpoint.
    Only the child body is a premise; the invariant/branch count is derived. -/
theorem forever_positive_counted
    {P : Programm D} {f : D.Fn} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {Γ : Ctx} {Λ : List (Res D)} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {rp cfp : W} {ni nb : Nat}
    {outcome : Ausgang (vertragVon D f) true Γ}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {cc cb : List II} {m : Mem} {pc fp e eL eN : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr
      (exPlus ex 4) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (inside : WIn L fp Ks K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (child : ∀ m1,
      PreS L m1 (pc + BitVec.ofNat 64 (16 * cc.length) + 16) fp K
        (frei Γ reserved) cb ρ reserved →
      Umf L A C dv m1 fp Ks K → WeltAt m1 L σ →
      CountedSim nb L P f σ0 ρ0 rp cfp fp lo K pr
        ⟨pc + BitVec.ofNat 64 (16 * cc.length) + 16, fp⟩ m1
        e eL eN outcome reserved) :
    CountedSim (ni + 1 + nb) L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m e eL eN outcome reserved := by
  have hks := inside.ks
  have room := lowE_top _ _ _ _ lowerInv
  have hpw := PreS.welt pre.left inside.ks world inside.lay
    (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, w, read, value⟩ := invariant.sound lowerInv (by omega) hpw
  subst w
  have a1 := Agree.widen a1s inside.ks
  have h1 := pre.next a1 (Nat.le_refl _) (by omega)
  have h2 := h1.next (a := [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0])
    (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have ins := h1.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
  have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
    sx_nat (by have := pre.small; omega)
  have branch := counted_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
    (by simp only [ci]; exact run_brz_ne ins (by rw [hd]; exact read) (by decide))
  have bodyPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cc.length) + 16)
      fp K (frei Γ reserved) cb ρ reserved := by simpa using h2.left
  have aw : AgreeW L fp lo K m m1 := agreeW_of (a1.mono low)
  exact CountedSim.prefix abi (by simpa using run1.trans branch) aw
    (keeps_of_agreeW inside (agreeW_of a1) hprotected (by omega))
    (child m1 bodyPre
      (Umf.agreeW inside surroundings (agreeW_of a1) (by simp [frei]; omega))
      (hpw.wstab m m1 world (a1s.mono (Nat.zero_le _))))


/-- Execute the invariant and recursive source body at their shared endpoint. -/
theorem recursiveBlockCost.positive_source_counted
    {P : Programm D} {f : D.Fn} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {Γ : Ctx} {Λ : List (Res D)} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {rp cfp : W} {ni nb : Nat}
    {outcome : Ausgang (vertragVon D f) true Γ}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {cc cb : List II} {m : Mem} {pc fp e eL eN : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr
      (exPlus ex 4) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (inside : WIn L fp Ks K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (child : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f) true
      body σ ρ outcome nb)
    (fitsBody : tb ≤ Ks)
    (endEq : e = pc + BitVec.ofNat 64 (16 * cc.length) + 16 +
      BitVec.ofNat 64 (16 * cb.length))
    (leaveEq : eL = e + BitVec.ofInt 64 (exPlus ex 4).1)
    (nextEq : eN = e + BitVec.ofInt 64 (exPlus ex 4).2) :
    ∃ n, n ≤ ni + 1 + nb ∧ CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m e eL eN outcome reserved := by
  have hks := inside.ks
  have room := lowE_top _ _ _ _ lowerInv
  have hpw := PreS.welt pre.left inside.ks world inside.lay
    (by have := inside.lo; omega)
  obtain ⟨m1, run1, a1s, w, read, value⟩ := invariant.sound lowerInv (by omega) hpw
  subst w
  have a1 := Agree.widen a1s inside.ks
  have h1 := pre.next a1 (Nat.le_refl _) (by omega)
  have h2 := h1.next (a := [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0])
    (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have ins := h1.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at ins
  have hd : sx (II.f (frei Γ reserved : Int)) = BitVec.ofNat 64 (frei Γ reserved) :=
    sx_nat (by have := pre.small; omega)
  have branch := counted_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
    (by simp only [ci]; exact run_brz_ne ins (by rw [hd]; exact read) (by decide))
  have bodyPre : PreS L m1 (pc + BitVec.ofNat 64 (16 * cc.length) + 16)
      fp K (frei Γ reserved) cb ρ reserved := by simpa using h2.left
  have aw : AgreeW L fp lo K m m1 := agreeW_of (a1.mono low)
  obtain ⟨n, bound, run⟩ := child.sound (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp)
    lowerBody fitsBody inside abi low hprotected bodyPre
    (Umf.agreeW inside surroundings (agreeW_of a1) (by simp [frei]; omega))
    (hpw.wstab m m1 world (a1s.mono (Nat.zero_le _)))
  rw [← endEq, ← leaveEq, ← nextEq] at run
  exact ⟨ni + 1 + n, by omega, CountedSim.prefix abi
    (by simpa using run1.trans branch) aw
    (keeps_of_agreeW inside (agreeW_of a1) hprotected (by omega)) run⟩


/-- The actual two-instruction positive header feeds a recursive source body. -/
theorem recursiveBlockCost.positive_header_source_counted
    {P : Programm D} {f : D.Fn} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {Γ : Ctx} {Λ : List (Res D)} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {rp cfp : W} {ni nb : Nat}
    {outcome : Ausgang (vertragVon D f) true Γ}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {counter one : Nat} {jump : Int} {fuel : W}
    {cc cb : List II} {m : Mem} {pc fp e eL eN : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr
      (exPlus ex 4) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (inside : WIn L fp Ks K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounter counter one jump ++ (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (counterLow : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (locals : frei Γ reserved ≤ K)
    (protectLow : lo ≤ counter) (protect : ∀ j ∈ pr, j < counter)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some fuel)
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (positive : fuel ≠ 0)
    (child : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f) true
      body σ ρ outcome nb)
    (fitsBody : tb ≤ Ks)
    (endEq : e = (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 +
      BitVec.ofNat 64 (16 * cb.length))
    (leaveEq : eL = e + BitVec.ofInt 64 (exPlus ex 4).1)
    (nextEq : eN = e + BitVec.ofInt 64 (exPlus ex 4).2) :
    ∃ n, n ≤ 2 + ni + 1 + nb ∧ CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m e eL eN outcome reserved := by
  obtain ⟨mh, header, ph, wh, ah, rh, oh⟩ :=
    counter_positive_source_counted inside pre world counterLow ordered allocated locals
      read readOne positive
  obtain ⟨n, bound, run⟩ := child.positive_source_counted invariant lowerInv lowerBody
    fitsInv inside abi low hprotected ph
    (Umf.agreeW inside surroundings (agreeW_of ah) (by omega)) wh
    fitsBody endEq leaveEq nextEq
  exact ⟨2 + n, by omega, CountedSim.prefix abi header
    (agreeW_of (ah.mono protectLow))
    (keeps_of_agreeW inside (agreeW_of ah) protect (by
      have := lowE_top _ _ _ _ lowerInv; unfold frei at *; omega)) run⟩


/-- Initialize both reserved words before the positive source pass. -/
theorem recursiveBlockCost.initialized_positive_source_counted
    {P : Programm D} {f : D.Fn} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {Γ : Ctx} {Λ : List (Res D)} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {σ σ0 : World D} {ρ : Env D Γ} {ρ0 : Env D (D.params f)}
    {rp cfp : W} {ni nb : Nat}
    {outcome : Ausgang (vertragVon D f) true Γ}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
    {lo K tc tb : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {counter one : Nat} {jump : Int} {value : Int}
    {cc cb : List II} {m : Mem} {pc fp e eL eN : W}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens pr
      (exPlus ex 4) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (inside : WIn L fp Ks K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved)
    (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved)
      ([ci 1 counter value 0] ++ [ci 1 one 1 0] ++ foreverCounter counter one jump ++ (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)))))) ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (counterLow : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (locals : frei Γ reserved ≤ K)
    (protectLow : lo ≤ counter) (protect : ∀ j ∈ pr, j < counter)
    (literal : lit32 value = true) (positive : (BitVec.ofInt 64 value : W) ≠ 0)
    (child : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f) true
      body σ ρ outcome nb)
    (fitsBody : tb ≤ Ks)
    (endEq : e = (pc + 16 + 16 + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 +
      BitVec.ofNat 64 (16 * cb.length))
    (leaveEq : eL = e + BitVec.ofInt 64 (exPlus ex 4).1)
    (nextEq : eN = e + BitVec.ofInt 64 (exPlus ex 4).2) :
    ∃ n, n ≤ 4 + ni + 1 + nb ∧ CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m e eL eN outcome reserved := by
  obtain ⟨m1, run1, pre1, world1, agree1, read1⟩ :=
    reserved_literal_source_entry inside pre world counterLow (by omega) locals literal
  obtain ⟨m2, run2, pre2, world2, agree2, read2⟩ :=
    reserved_literal_source_entry inside pre1 world1 (by omega) allocated locals (by decide)
  have counterRead : m2.rd64 (slot fp (BitVec.ofNat 64 counter)) =
      some (BitVec.ofInt 64 value) := by
    rw [agree_rd_low agree2 pre1.frame.room ordered (by unfold frei at locals; omega)]
    exact read1
  have agree := agree1.trans (agree2.mono (Nat.le_of_lt ordered))
  obtain ⟨n, bound, run⟩ := child.positive_header_source_counted invariant lowerInv lowerBody
    fitsInv inside abi low hprotected pre2
    (Umf.agreeW inside surroundings (agreeW_of agree) (by omega)) world2
    counterLow ordered allocated locals protectLow protect counterRead read2 positive
    fitsBody endEq leaveEq nextEq
  refine ⟨2 + n, by omega, ?_⟩
  exact CountedSim.prefix abi (run1.trans run2)
    (agreeW_of (agree.mono protectLow))
    (keeps_of_agreeW inside (agreeW_of agree) protect (by
      have := lowE_top _ _ _ _ lowerInv; unfold frei at *; omega)) run


namespace FullCallProbe
open FnptrProben
open FullFunProbe (fixtureDecl program layout world)
local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

def args : Args fixtureDecl [] [] (fixtureDecl.params 0) := .cons (.lit 37) .nil
def target (f : fixtureDecl.Fn) : List II := ((lowFun 2 program addresses layout f).getD ([], 0)).1
def caller : List II := callC (D := fixtureDecl) addresses (0 : fixtureDecl.Fn) 4 [ci 1 8 37 0]
def memory : Mem :=
  let segments := [(64, (target 0).flatMap encII), (576, (target 1).flatMap encII),
    (1088, (target 2).flatMap encII), (2048, caller.flatMap encII)]
  let base : Mem := {
    b := fun a => match segments.find? (fun s => s.1 ≤ a.toNat && a.toNat < s.1 + s.2.length) with
      | some s => (s.2[a.toNat - s.1]?).getD 0
      | none => 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write base 8192 8 64) 4112 8 2

theorem call_continuation_zeuge : ∃ n, n ≤ 17 ∧
    CountedReach n layout 4096 4 256 [] ⟨2048, 4096⟩ memory
      2128 world (Env.nil : Env fixtureDecl []) := by
  have targets : PCode memory addresses target 4096 256 := by
    have h : ∀ f : Fin 3, ∀ k : Fin (target f).length,
        InsAt memory (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
          (target f)[k.val].o (II.f (target f)[k.val].a)
          (II.f (target f)[k.val].b) (II.f (target f)[k.val].c) := by
      apply allFin
      decide +kernel
    intro f
    refine ⟨fun k hk => h f ⟨k, hk⟩, ?_⟩
    have far : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256 := by
      unfold CodeFar
      apply allFin
      decide +kernel
    exact far f
  have ccode : CodeAt memory 2048 caller := by
    have h : ∀ k : Fin caller.length,
        InsAt memory (2048 + BitVec.ofNat 64 (16 * k.val))
          caller[k.val].o (II.f caller[k.val].a) (II.f caller[k.val].b) (II.f caller[k.val].c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have frame : FrameOK memory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have pre : PreS layout memory 2048 4096 256 4 caller (Env.nil : Env fixtureDecl []) :=
    ⟨by decide, by decide, frame, ccode, by unfold CodeFar; decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have inside : WIn layout 4096 128 256 := by
    refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩,
      ?_, by decide, by decide, by decide⟩
    constructor
    · intro c c' hc hc' h
      cases c with
      | elem t => nomatch t
      | glob g =>
        cases c' with
        | elem t => nomatch t
        | glob g' => cases g; cases g'; rfl
    · intro c hc
      cases c with
      | elem t => nomatch t
      | glob _ => rfl
  have hw : WeltAt memory layout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  have sync : SyncOK memory layout 4096 128 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩
  have around : Umf layout addresses target 1 memory 4096 128 256 :=
    ⟨targets, by decide +kernel, by decide, sync, by decide⟩
  have cert : ArgsCost layout 0 4 args world world (Env.nil : Env fixtureDecl []) 1 :=
    .cons (ne := 1) (nr := 0) .nil .literal
  have recursive := recursiveBlockCost.call (L := layout) (reserved := 0) (Γ := []) (Λ := [])
    (f := (0 : fixtureDecl.Fn)) (P := program) (passes := 2) (args := args)
    (σ₀ := world) (σ := world) (ρ := Env.nil) (na := 1) (nq := 1) (nb := 6) (declared := 12)
    (A := addresses) (C := target)
    (Ks := 128) (top := 14) (dv := 1) (depth := 0)
    (returned := .zurueck world (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37))) (V := vertragVon fixtureDecl 0) (l := false)
    (rest := Block.nil) (nr := 0)
    (hp := {
      hw := fun t => nomatch t
      hg := fun _ h => h
      hk := ⟨[], List.Perm.nil, List.Sublist.refl []⟩
      hh := fun l => nomatch l })
    (hr := rfl) cert (by decide +kernel) (by decide)
    (by decide) (by rfl) (by decide) .truth
    (by
      intro ens hens snapshot
      have eq : ens = ([ci 1 6 1 0], 7) := Option.some.inj hens.symm
      subst ens
      let leaf : EndCost layout 3 (vertragVon fixtureDecl 0) false [.int 37 37]
          snapshot ([ci 1 6 1 0], 7) 5 (program.rumpf 0) world
          (evalArgs world args world Env.nil) 6 :=
        .normal (τ := .int 37 37) (v := (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)))
        (q := Expr.tru (Λ := [])) rfl List.Perm.nil .literal (.ordinary rfl .truth) rfl
      exact .source leaf)
    (by
      intro cs hcs
      have eq : cs = [] := Option.some.inj hcs.symm
      subst cs
      decide)
    (.source .nil)
  have joint := recursive.sound_normal (lo := 4) (ens := ([], 4)) (pr := []) (ex := (0, 0))
    (σ0 := FullFunProbe.world) (ρ0 := Env.cons (τ := .int 37 37) (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil)
    (rp := 0) (cfp := 0)
    (code := caller) (top := 10) rfl (by decide) inside (by decide) (by decide)
    (by intro j hj; cases hj) (by simpa [frei, FB] using pre) around hw
  simpa [caller, callC, callTail, callTailN, Env.tail] using joint
theorem fullCall_zeuge : ∃ n m', n ≤ 17 ∧
    Counted n ⟨2048, 4096⟩ memory ⟨2128, 4096⟩ m' := by
  obtain ⟨n, bound, m', run, _⟩ := call_continuation_zeuge
  exact ⟨n, m', bound, run⟩
end FullCallProbe


namespace BindCallProbe
open FnptrProben
open FullFunProbe (fixtureDecl program layout world)
local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

def args : Args fixtureDecl [] [] (fixtureDecl.params 0) := .cons (.lit 37) .nil
def target (f : fixtureDecl.Fn) : List II := ((lowFun 2 program addresses layout f).getD ([], 0)).1
def caller : List II := callC (D := fixtureDecl) addresses (0 : fixtureDecl.Fn) 4 [ci 1 8 37 0] ++ [ci 2 4 6 0]
def memory : Mem :=
  let segments := [(64, (target 0).flatMap encII), (576, (target 1).flatMap encII),
    (1088, (target 2).flatMap encII), (2048, caller.flatMap encII)]
  let base : Mem := {
    b := fun a => match segments.find? (fun s => s.1 ≤ a.toNat && a.toNat < s.1 + s.2.length) with
      | some s => (s.2[a.toNat - s.1]?).getD 0
      | none => 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write base 8192 8 64) 4112 8 2

theorem bind_continuation_zeuge : ∃ n, n ≤ 18 ∧
    CountedReach n layout 4096 4 256 [] ⟨2048, 4096⟩ memory
      2144 world (Env.nil : Env fixtureDecl []) := by
  have targets : PCode memory addresses target 4096 256 := by
    have h : ∀ f : Fin 3, ∀ k : Fin (target f).length,
        InsAt memory (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
          (target f)[k.val].o (II.f (target f)[k.val].a)
          (II.f (target f)[k.val].b) (II.f (target f)[k.val].c) := by
      apply allFin
      decide +kernel
    intro f
    refine ⟨fun k hk => h f ⟨k, hk⟩, ?_⟩
    have far : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256 := by
      unfold CodeFar
      apply allFin
      decide +kernel
    exact far f
  have ccode : CodeAt memory 2048 caller := by
    have h : ∀ k : Fin caller.length,
        InsAt memory (2048 + BitVec.ofNat 64 (16 * k.val))
          caller[k.val].o (II.f caller[k.val].a) (II.f caller[k.val].b) (II.f caller[k.val].c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have frame : FrameOK memory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have pre : PreS layout memory 2048 4096 256 4 caller (Env.nil : Env fixtureDecl []) :=
    ⟨by decide, by decide, frame, ccode, by unfold CodeFar; decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have inside : WIn layout 4096 128 256 := by
    refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩,
      ?_, by decide, by decide, by decide⟩
    constructor
    · intro c c' hc hc' h
      cases c with
      | elem t => nomatch t
      | glob g =>
        cases c' with
        | elem t => nomatch t
        | glob g' => cases g; cases g'; rfl
    · intro c hc
      cases c with
      | elem t => nomatch t
      | glob _ => rfl
  have hw : WeltAt memory layout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  have sync : SyncOK memory layout 4096 128 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩
  have around : Umf layout addresses target 1 memory 4096 128 256 :=
    ⟨targets, by decide +kernel, by decide, sync, by decide⟩
  have cert : ArgsCost layout 0 4 args world world (Env.nil : Env fixtureDecl []) 1 :=
    .cons (ne := 1) (nr := 0) .nil .literal
  have recursive := recursiveBlockCost.bindCall (τ := .int 37 37) (v := (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37))) (he := rfl) (L := layout) (reserved := 0) (Γ := []) (Λ := [])
    (f := (0 : fixtureDecl.Fn)) (P := program) (passes := 2) (args := args)
    (σ₀ := world) (σ := world) (ρ := Env.nil) (na := 1) (nq := 1) (nb := 6) (declared := 12)
    (A := addresses) (C := target)
    (Ks := 128) (top := 14) (dv := 1) (depth := 0)
    (returned := .zurueck world (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37))) (V := vertragVon fixtureDecl 0) (l := false)
    (rest := Block.nil) (nr := 0)
    (outcome := .ok world (Env.cons (τ := .int 37 37) (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil))
    (hp := {
      hw := fun t => nomatch t
      hg := fun _ h => h
      hk := ⟨[], List.Perm.nil, List.Sublist.refl []⟩
      hh := fun l => nomatch l })
    (hr := rfl) cert (by decide +kernel) (by decide)
    (by decide) (by rfl) (by decide) .truth
    (by
      intro ens hens snapshot
      have eq : ens = ([ci 1 6 1 0], 7) := Option.some.inj hens.symm
      subst ens
      let leaf : EndCost layout 3 (vertragVon fixtureDecl 0) false [.int 37 37]
          snapshot ([ci 1 6 1 0], 7) 5 (program.rumpf 0) world
          (evalArgs world args world Env.nil) 6 :=
        .normal (τ := .int 37 37) (v := (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)))
        (q := Expr.tru (Λ := [])) rfl List.Perm.nil .literal (.ordinary rfl .truth) rfl
      exact .source leaf)
    (by
      intro cs hcs
      have eq : cs = [] := Option.some.inj hcs.symm
      subst cs
      decide)
    rfl
    (.source .nil)
  have joint := recursive.sound_normal (lo := 4) (ens := ([], 4)) (pr := []) (ex := (0, 0))
    (σ0 := FullFunProbe.world) (ρ0 := Env.cons (τ := .int 37 37) (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil)
    (rp := 0) (cfp := 0)
    (code := caller) (top := 10) rfl (by decide) inside (by decide) (by decide)
    (by intro j hj; cases hj) (by simpa [frei, FB] using pre) around hw
  exact joint
end BindCallProbe


end Gabbro.Stage0.Senke

namespace Gabbro.Stage0.Senke.RecursiveTerminalProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem FnptrProben
open FullFunProbe (fixtureDecl program layout world)
variable [Kern]
def terminalCall : Endblock fixtureDecl (vertragVon fixtureDecl 0) false [] [] :=
  .cons (.call 0 FullCallProbe.args
    { hw := fun t => nomatch t
      hg := fun _ h => h
      hk := ⟨[], List.Perm.nil, List.Sublist.refl []⟩
      hh := fun l => nomatch l } rfl)
    (.ret (.val (.lit 37)) List.Perm.nil)
theorem recursiveEndCost_zeuge : Nonempty
    (RecursiveEndCost layout program 2 addresses FullCallProbe.target 2 128 0
      (vertragVon fixtureDecl 0) false [] 64 ([ci 1 5 1 0], 6) 4
      terminalCall world Env.nil (.zurueck world (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37))) 23) := by
  unfold terminalCall
  refine ⟨RecursiveEndCost.call
    (L := layout) (P := program) (passes := 2) (A := addresses) (C := FullCallProbe.target)
    (depth := 1) (Ks := 128) (reserved := 0) (top := 14) (nq := 1) (nb := 6) (declared := 12) (na := 1) (nr := 6) (σ₀ := world)
    (returned := .zurueck world (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37))) (f := 0)
    (Γ := []) (Λ := []) (.cons (ne := 1) (nr := 0) .nil .literal) (by decide +kernel) (by decide) (by decide) .truth ?_ ?_ ?_⟩
  · intro ens hens snapshot
    have eq : ens = ([ci 1 6 1 0], 7) := Option.some.inj hens.symm
    subst ens
    let cert : EndCost layout 3 (vertragVon fixtureDecl 0) false [.int 37 37]
        snapshot ([ci 1 6 1 0], 7) 5 (program.rumpf 0) world
        (evalArgs world FullCallProbe.args world Env.nil) 6 :=
      .normal (τ := .int 37 37)
        (v := (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)))
        (q := Expr.tru (Λ := [])) rfl List.Perm.nil .literal (.ordinary rfl .truth) rfl
    exact RecursiveEndCost.source cert
  · intro cs hcs
    have eq : cs = [] := Option.some.inj hcs.symm
    subst cs
    decide
  · let cert : EndCost layout 0 (vertragVon fixtureDecl 0) false []
        64 ([ci 1 5 1 0], 6) 4
        (.ret (.val (.lit 37)) List.Perm.nil) world Env.nil 6 :=
      .normal (τ := .int 37 37)
        (v := (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)))
        (q := Expr.tru (Λ := [])) rfl List.Perm.nil .literal (.ordinary rfl .truth) rfl
    exact RecursiveEndCost.source cert

end Gabbro.Stage0.Senke.RecursiveTerminalProbe

namespace Gabbro.Stage0.Senke.RecursiveTerminalProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem FnptrProben
open FullFunProbe (fixtureDecl program layout world)
variable [Kern]
local instance (m : Mem) (pc : W) (o : Nat) (a b c : BitVec 32) :
    Decidable (InsAt m pc o a b c) :=
  if h : m.rd8 pc = some (BitVec.ofNat 8 o) ∧ m.rd32 (pc + 4) = some a ∧
      m.rd32 (pc + 8) = some b ∧ m.rd32 (pc + 12) = some c then
    .isTrue ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  else .isFalse (fun h' => h ⟨h'.op, h'.f1, h'.f2, h'.f3⟩)

set_option maxHeartbeats 4000000
def target := FullCallProbe.target
def image : List II := ((lowEnd (D := fixtureDecl) 2 addresses FullFunProbe.layout 4 ([ci 1 5 1 0], 6) [] (0, 0) terminalCall).getD ([], 0)).1
def memory : Mem :=
  let segments := [(64, (target 0).flatMap encII), (576, (target 1).flatMap encII),
    (1088, (target 2).flatMap encII), (2048, image.flatMap encII)]
  let base : Mem := {
    b := fun a => match segments.find? (fun s => s.1 ≤ a.toNat && a.toNat < s.1 + s.2.length) with
      | some s => (s.2[a.toNat - s.1]?).getD 0
      | none => 0
    rd := fun _ => true
    wr := fun _ => true }
  write (write (write (write (write base 8192 8 64) 4112 8 3) 4096 8 3072) 4104 8 16384) 4120 8 64

theorem sound_zeuge : ∃ n m', n ≤ 23 ∧
    Counted n ⟨2048, 4096⟩ memory ⟨3072, 16384⟩ m' ∧
    AgreeW layout 4096 2 256 memory m' ∧ FrameOK m' 4096 256 ∧
    WeltAt m' layout world ∧
    m'.rd64 (slot 4096 5) = some 1 ∧
    ∃ w, m'.rd64 (slot 4096 2) = some w ∧ Enc layout (.int 37 37)
      (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) w := by
  have targets : PCode memory addresses target 4096 256 := by
    have h : ∀ f : Fin 3, ∀ k : Fin (target f).length,
        InsAt memory (BitVec.ofNat 64 (addresses f) + BitVec.ofNat 64 (16 * k.val))
          (target f)[k.val].o (II.f (target f)[k.val].a)
          (II.f (target f)[k.val].b) (II.f (target f)[k.val].c) := by
      apply allFin
      decide +kernel
    intro f
    refine ⟨fun k hk => h f ⟨k, hk⟩, ?_⟩
    have far : ∀ f : Fin 3, CodeFar (BitVec.ofNat 64 (addresses f)) (target f).length 4096 256 := by
      unfold CodeFar
      apply allFin
      decide +kernel
    exact far f
  have ccode : CodeAt memory 2048 image := by
    have h : ∀ k : Fin image.length,
        InsAt memory (2048 + BitVec.ofNat 64 (16 * k.val))
          image[k.val].o (II.f image[k.val].a) (II.f image[k.val].b) (II.f image[k.val].c) := by
      apply allFin
      decide +kernel
    exact fun k hk => h ⟨k, hk⟩
  have frame : FrameOK memory 4096 256 := ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩
  have pre : PreS layout memory 2048 4096 256 4 image (Env.nil : Env fixtureDecl []) :=
    ⟨by decide, by decide, frame, ccode, by unfold CodeFar; decide +kernel,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  have inside : WIn layout 4096 128 256 := by
    refine ⟨⟨(fun t => nomatch t), fun _ => ⟨by change 8192 ≤ 8192; decide, by change 8192 + 8 ≤ 8200; decide⟩, by decide⟩,
      ?_, by decide, by decide, by decide⟩
    constructor
    · intro c c' hc hc' h
      cases c with
      | elem t => nomatch t
      | glob g =>
        cases c' with
        | elem t => nomatch t
        | glob g' => cases g; cases g'; rfl
    · intro c hc
      cases c with
      | elem t => nomatch t
      | glob _ => rfl
  have hw : WeltAt memory layout world := by
    refine ⟨(fun t => nomatch t), (fun g => ⟨64, ?_, rfl⟩), (fun _ _ _ => rfl)⟩
    cases g
    decide +kernel
  have sync : SyncOK memory layout 4096 128 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      (fun l => nomatch l), by decide, (fun l => nomatch l), (fun l => nomatch l), (fun l => nomatch l)⟩
  have around : Umf layout addresses target 2 memory 4096 128 256 :=
    ⟨targets, by decide +kernel, by decide, sync, by decide⟩
  obtain ⟨cert⟩ := recursiveEndCost_zeuge
  obtain ⟨n, m', bound, run, agree, frame, hw, result, status⟩ :=
    cert.sound (K := 256) (top := 13) (pr := []) (ex := (0, 0))
      (code := image) (m := memory) (pc := 2048) (fp := 4096) (rp := 3072) (cfp := 16384)
      (by decide +kernel) (by decide) inside (by decide) (by decide) (by decide)
      (fun _ h => nomatch h) pre hw Env.nil (fun _ x => nomatch x) rfl
      (by decide +kernel) (by decide +kernel) (by decide +kernel) around (by decide)
  exact ⟨n, m', bound, run, agree, frame, hw, status.1, result _ _ rfl⟩

end Gabbro.Stage0.Senke.RecursiveTerminalProbe


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

/-- Observations of one actual counted endpoint. Return endpoints use the
    caller frame; pending requests retain their actual thread and memory.
    This predicate contains no execution or whole-source cost assumption. -/
def CountedSimOutcome (L : Lay D) (P : Programm D) (f : D.Fn)
    (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp fp : W)
    (lo K : Nat) (pr : List Nat) (m : Mem) (e eL eN : W)
    {l : Bool} {Γ : Ctx} (o : Ausgang (vertragVon D f) l Γ)
    (u : T) (a : Mem) (reserved : Nat := 0) : Prop :=
  let pending := fun c => ∃ q, StopAt u a q ∧ q.nr = 231 ∧ q.a1 = BitVec.ofNat 64 c
  let reach := fun endpoint σ ρ => u = ⟨endpoint, fp⟩ ∧ AgreeW L fp lo K m a ∧
    EnvAt L a fp ρ reserved ∧ WeltAt a L σ ∧ Keeps fp pr m a
  match o with
  | .ok σ ρ => reach e σ ρ
  | .leave _ σ ρ => reach eL σ ρ
  | .next _ σ ρ => reach eN σ ρ
  | .logik c => pending (logikCode c)
  | .hardware h => pending (hwCode h)
  | .why σ r => u = ⟨rp, cfp⟩ ∧ AgreeW L fp 2 K m a ∧
      a.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 r.val) ∧
      ReturnFlag a fp (D.params f).length false ∧ WeltAt a L σ
  | .zurueck σ v =>
      if wahr? (eval σ0 (P.ensures f) (σ.lese (vertragVon D f).ende (P.ensures f).orte)
          (ergEnv (D.erg f) v ρ0)) = false then pending 102
      else u = ⟨rp, cfp⟩ ∧ AgreeW L fp 2 K m a ∧
        (∃ w, a.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧
          EncErg L (D.erg f) v w ∧ ReturnFlag a fp (D.params f).length true) ∧ WeltAt a L σ

/-- All outcome kinds consume observations of the very same counted endpoint.
    In particular no callee-frame equality is imposed on a return. -/
theorem CountedSimOutcome.sound {L : Lay D} {P : Programm D} {f : D.Fn}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp : W}
    {lo K reserved n : Nat} {pr : List Nat} {m a : Mem} {t u : T} {e eL eN : W}
    {l : Bool} {Γ : Ctx} {o : Ausgang (vertragVon D f) l Γ}
    (run : Counted n t m u a)
    (post : CountedSimOutcome L P f σ0 ρ0 rp cfp fp lo K pr m e eL eN o u a reserved) :
    CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved := by
  cases o with
  | ok σ ρ | leave h σ ρ | next h σ ρ =>
    obtain ⟨rfl, rest⟩ := post
    exact ⟨a, run, rest⟩
  | logik c | hardware c =>
    obtain ⟨q, stop, nr, arg⟩ := post
    exact ⟨u, a, q, run, stop, nr, arg⟩
  | why σ r =>
    obtain ⟨rfl, rest⟩ := post
    exact ⟨a, run, rest⟩
  | zurueck σ v =>
    simp only [CountedSimOutcome] at post
    change CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ v
    unfold CountedRetZ
    split at post
    · rename_i bad
      rw [if_pos bad]
      obtain ⟨q, stop, nr, arg⟩ := post
      exact ⟨u, a, q, run, stop, nr, arg⟩
    · rename_i good
      rw [if_neg good]
      obtain ⟨rfl, rest⟩ := post
      exact ⟨a, run, rest⟩

/-- The real stop instructions produce the shared endpoint observations for
    either source stop kind, including progress hardware stops. -/
theorem stopC_counted_outcome {L : Lay D} {P : Programm D} {f : D.Fn}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp pc : W}
    {lo K reserved scratch c : Nat} {pr : List Nat} {m : Mem} {e eL eN : W}
    {l : Bool} {Γ : Ctx} {o : Ausgang (vertragVon D f) l Γ}
    (kind : (∃ reason, o = .logik reason ∧ c = logikCode reason) ∨
      (∃ reason, o = .hardware reason ∧ c = hwCode reason))
    (code : CodeAt m pc (stopC c scratch)) (far : CodeFar pc 3 fp K)
    (frame : FrameOK m fp K) (room : scratch + 8 ≤ K)
    (small : K < 2 ^ 31) (fits : c < 2 ^ 31) :
    ∃ u a, Counted 2 ⟨pc, fp⟩ m u a ∧
      CountedSimOutcome L P f σ0 ρ0 rp cfp fp lo K pr m e eL eN o u a reserved := by
  obtain ⟨u, a, q, run, stop, nr, arg, _⟩ :=
    sys_counted_frame code far frame room small fits (by decide)
  refine ⟨u, a, run, ?_⟩
  rcases kind with ⟨reason, rfl, rfl⟩ | ⟨reason, rfl, rfl⟩
  · exact ⟨q, stop, nr, arg⟩
  · exact ⟨q, stop, nr, arg⟩

end Gabbro.Stage0.Senke


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Actual budget exhaustion, with the source assumption named, is a hardware
    progress outcome at the same pending-request endpoint. -/
theorem counter_budget_stop_outcome
    {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp : W} {assumption : D.Annahme}
    {Γ : Ctx} {m : Mem} {pc fp : W} {K Ks lo scratch : Nat}
    {pr : List Nat} {σ : World D} {ρ : Env D Γ} {e eL eN : W}
    {d jump : BitVec 32}
    (test : InsAt m pc 19 d jump 0)
    (zero : m.rd64 (slot fp (sx d)) = some 0)
    (pre : PreS L m (pc + sx jump) fp K (frei Γ reserved)
      (stopC 111 scratch) ρ reserved)
    (inside : WIn L fp Ks K) (world : WeltAt m L σ)
    (low : lo ≤ scratch) (locals : frei Γ reserved ≤ scratch)
    (room : scratch + 8 ≤ K) (hprotected : ∀ j ∈ pr, j < scratch) :
    ∃ u a, Counted 3 ⟨pc, fp⟩ m u a ∧
      CountedSimOutcome L P f σ0 ρ0 rp cfp fp lo K pr m e eL eN
        (.hardware (.fortschritt assumption) : Ausgang (vertragVon D f) false Γ) u a reserved ∧
      AgreeW L fp lo K m a ∧ EnvAt L a fp ρ reserved ∧ WeltAt a L σ ∧ Keeps fp pr m a := by
  obtain ⟨u, a, q, run, stop, nr, arg, rest⟩ :=
    counter_budget_stop_counted test zero pre inside world low locals room hprotected
  exact ⟨u, a, run, ⟨q, stop, nr, arg⟩, rest⟩

namespace ActualStopProbe
open FullFunProbe
set_option maxRecDepth 10000

def image : List II := stopC 104 4
def memory : Mem := {
  b := fun a => ((image.flatMap encII)[a.toNat]?).getD 0
  rd := fun _ => true
  wr := fun _ => true }

/-- A genuine executed logic stop, with the pending request and canonical
    child simulation jointly witnessed, rather than assumed as a premise. -/
theorem stopC_counted_outcome_zeuge :
    ∃ u a, Counted 2 ⟨0, 4096⟩ memory u a ∧
      CountedSimOutcome layout program 0 world
        (Env.cons (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil)
        2048 16384 4096 4 32 [] memory 0 0 0
        (.logik .schleife : Ausgang (vertragVon fixtureDecl 0) false []) u a ∧
      CountedSim 2 layout program 0 world
        (Env.cons (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil)
        2048 16384 4096 4 32 [] ⟨0, 4096⟩ memory 0 0 0
        (.logik .schleife : Ausgang (vertragVon fixtureDecl 0) false []) := by
  have code : CodeAt memory 0 image := by
    have h : ∀ k : Fin image.length,
        memory.rd8 (BitVec.ofNat 64 (16 * k.val)) = some (BitVec.ofNat 8 image[k.val].o) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 4) = some (II.f image[k.val].a) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 8) = some (II.f image[k.val].b) ∧
        memory.rd32 (BitVec.ofNat 64 (16 * k.val) + 12) = some (II.f image[k.val].c) := by
      apply FnptrProben.allFin; decide +kernel
    intro k hk
    obtain ⟨o, a, b, c⟩ := h ⟨k, hk⟩
    exact ⟨by simpa using o, by simpa using a, by simpa using b, by simpa using c⟩
  obtain ⟨u, a, run, post⟩ := stopC_counted_outcome
    (L := layout) (P := program) (f := 0) (σ0 := world)
    (ρ0 := Env.cons (⟨37, by decide, by decide⟩ : Wert fixtureDecl (.int 37 37)) Env.nil)
    (rp := 2048) (cfp := 16384) (fp := 4096) (pc := 0) (scratch := 4)
    (lo := 4) (reserved := 0) (pr := [])
    (e := 0) (eL := 0) (eN := 0)
    (o := (.logik .schleife : Ausgang (vertragVon fixtureDecl 0) false []))
    (Or.inl ⟨.schleife, rfl, rfl⟩) code
    (K := 32) (by unfold CodeFar; decide +kernel)
    ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩ (by decide) (by decide) (by decide)
  exact ⟨u, a, run, post, CountedSimOutcome.sound run post⟩
end ActualStopProbe

end Gabbro.Stage0.Senke


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

/-- Recover a joint endpoint from any canonical child outcome. This direction
    makes the endpoint API reusable for existing recursively counted children. -/
theorem CountedSim.outcome {L : Lay D} {P : Programm D} {f : D.Fn}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp : W}
    {lo K reserved n : Nat} {pr : List Nat} {m : Mem} {t : T} {e eL eN : W}
    {l : Bool} {Γ : Ctx} {o : Ausgang (vertragVon D f) l Γ}
    (sim : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o reserved) :
    ∃ u a, Counted n t m u a ∧
      CountedSimOutcome L P f σ0 ρ0 rp cfp fp lo K pr m e eL eN o u a reserved := by
  cases o with
  | ok σ ρ | leave h σ ρ | next h σ ρ =>
    obtain ⟨a, run, rest⟩ := sim
    exact ⟨_, a, run, rfl, rest⟩
  | logik c | hardware c =>
    obtain ⟨u, a, q, run, stop, nr, arg⟩ := sim
    exact ⟨u, a, run, q, stop, nr, arg⟩
  | why σ r =>
    obtain ⟨a, run, rest⟩ := sim
    exact ⟨_, a, run, rfl, rest⟩
  | zurueck σ v =>
    change CountedRetZ n L P f σ0 ρ0 fp K rp cfp t m σ v at sim
    unfold CountedRetZ at sim
    simp only [CountedSimOutcome]
    split at sim
    · rename_i bad
      obtain ⟨u, a, q, run, stop, nr, arg⟩ := sim
      exact ⟨u, a, run, by rw [if_pos bad]; exact ⟨q, stop, nr, arg⟩⟩
    · rename_i good
      obtain ⟨a, run, rest⟩ := sim
      exact ⟨_, a, run, by rw [if_neg good]; exact ⟨rfl, rest⟩⟩

/-- Counted routing of the actual backedge. Both reserved words are protected
    by the body's own frame and protected-slot guarantee at the same endpoint. -/
theorem CountedSim.counter_dispatch
    {P : Programm D} {f : D.Fn} {Γ : Ctx}
    {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp header back exit : W} {lo K Ks n : Nat} {pr : List Nat}
    {t : T} {m : Mem} {o : Ausgang (vertragVon D f) true Γ}
    {jump b c : BitVec 32}
    (body : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m back exit header o reserved)
    (layout : WIn L fp Ks K) (bound : lo ≤ K)
    (edge : InsAt m back 18 jump b c) (far : CodeFar back 1 fp K)
    (target : back + sx jump = header) :
    match o with
    | .ok σ ρ | .next _ σ ρ =>
      ∃ k m', k ≤ n + 1 ∧ Counted k t m ⟨header, fp⟩ m' ∧
        AgreeW L fp lo K m m' ∧ EnvAt L m' fp ρ reserved ∧
        WeltAt m' L σ ∧ Keeps fp pr m m' ∧
        ∀ j, j < lo ∨ j ∈ pr →
          m'.rd64 (slot fp (BitVec.ofNat 64 j)) =
            m.rd64 (slot fp (BitVec.ofNat 64 j))
    | o => CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m header exit header o reserved := by
  cases o with
  | ok σ ρ =>
    obtain ⟨m', run, frame, env, world, kept⟩ := body
    have code : CodeAt m back [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
      intro k hk
      have : k = 0 := by simpa using hk
      subst k
      simpa [II.f] using edge
    have edge' := (codeAt_agreeWIn layout frame code far) 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at edge'
    have last := Counted.next (run_step (t := ⟨back, fp⟩) edge' (by decide)
      (run_jmp (t := ⟨back, fp⟩) edge')) (Counted.refl _ _)
    refine ⟨n + 1, m', by omega, ?_, frame, env, world, kept, ?_⟩
    · simpa [II.f, target] using run.trans last
    · intro j hj
      rcases hj with below | member
      · exact counter_preserved layout frame below bound
      · exact kept j member
  | next h σ ρ =>
    obtain ⟨m', run, frame, env, world, kept⟩ := body
    refine ⟨n, m', by omega, run, frame, env, world, kept, ?_⟩
    intro j hj
    rcases hj with below | member
    · exact counter_preserved layout frame below bound
    · exact kept j member
  | leave h σ ρ => exact body
  | zurueck | why | logik | hardware => exact body

/-- Rebuild the actual header interface after routing a body outcome.
    Its counter and unit reads follow from OWN protection, including the already
    decremented value supplied by the positive header. -/
theorem CountedSim.counter_reentry
    {P : Programm D} {f : D.Fn} {Γ : Ctx}
    {σ0 : World D} {ρ0 : Env D (D.params f)}
    {rp cfp fp header back exit : W} {lo K Ks n : Nat} {pr : List Nat}
    {t : T} {m : Mem} {o : Ausgang (vertragVon D f) true Γ}
    {jump b c : BitVec 32}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W}
    {code : List II} {ρ : Env D Γ}
    (pre : PreS L m header fp K (frei Γ reserved) code ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (body : CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m back exit header o reserved)
    (layout : WIn L fp Ks K) (bound : lo ≤ K) (abi : FB ≤ lo)
    (edge : InsAt m back 18 jump b c) (far : CodeFar back 1 fp K)
    (target : back + sx jump = header) :
    match o with
    | .ok σ ρ' | .next _ σ ρ' =>
      ∃ k m', k ≤ n + 1 ∧ Counted k t m ⟨header, fp⟩ m' ∧
        PreS L m' header fp K (frei Γ reserved) code ρ' reserved ∧
        Umf L A C dv m' fp Ks K ∧ WeltAt m' L σ ∧
        AgreeW L fp lo K m m' ∧ Keeps fp pr m m' ∧
        ∀ j, j < lo ∨ j ∈ pr →
          m'.rd64 (slot fp (BitVec.ofNat 64 j)) =
            m.rd64 (slot fp (BitVec.ofNat 64 j))
    | o => CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr t m header exit header o reserved := by
  have routed := body.counter_dispatch layout bound edge far target
  cases o with
  | ok σ ρ' =>
    obtain ⟨k, m', hk, run, frame, env, world, kept, words⟩ := routed
    exact ⟨k, m', hk, run,
      ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame frame,
        codeAt_agreeWIn layout frame pre.code pre.far, pre.far, env,
        trivial, wstab_true _ _⟩,
      surround.agreeW layout frame abi, world, frame, kept, words⟩
  | next h σ ρ' =>
    obtain ⟨k, m', hk, run, frame, env, world, kept, words⟩ := routed
    exact ⟨k, m', hk, run,
      ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame frame,
        codeAt_agreeWIn layout frame pre.code pre.far, pre.far, env,
        trivial, wstab_true _ _⟩,
      surround.agreeW layout frame abi, world, frame, kept, words⟩
  | leave h σ ρ' => exact routed
  | zurueck | why | logik | hardware => exact routed

/-- Recursive source certificates supply the counted body and its own reserved-slot
    protection before routing the actual emitted edge. No body run is assumed. -/
theorem recursiveBlockCost.counter_dispatch {P : Programm D} {passes : Nat}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {Ks : Nat}
    {f0 : D.Fn} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {b : Block D (vertragVon D f0) true Γ Λ Λ'} {σ σ0 : World D} {ρ : Env D Γ}
    {ρ0 : Env D (D.params f0)} {rp cfp : W} {outcome : Ausgang (vertragVon D f0) true Γ} {budget : Nat}
    (certificate : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f0) true b σ ρ outcome budget)
    {lo K top : Nat} {ens : List II × Nat} {pr : List Nat} {ex : Int × Int}
    {code : List II} {m : Mem} {pc fp : W}
    (lower : lowB (reserved := reserved) passes A L lo ens pr ex b = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K) (bound : lo ≤ K)
    (abi : FB ≤ lo) (low : lo ≤ frei Γ reserved) (hprotected : ∀ j ∈ pr, j < frei Γ reserved)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (surroundings : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    {jump a c : BitVec 32}
    (edge : InsAt m (pc + BitVec.ofNat 64 (16 * code.length)) 18 jump a c)
    (far : CodeFar (pc + BitVec.ofNat 64 (16 * code.length)) 1 fp K)
    (target : pc + BitVec.ofNat 64 (16 * code.length) + sx jump =
      pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2) :
    ∃ n, n ≤ budget ∧
    match outcome with
    | .ok σ ρ | .next _ σ ρ =>
      ∃ k m', k ≤ n + 1 ∧ Counted k ⟨pc, fp⟩ m ⟨(pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2), fp⟩ m' ∧
        AgreeW L fp lo K m m' ∧ EnvAt L m' fp ρ reserved ∧
        WeltAt m' L σ ∧ Keeps fp pr m m' ∧
        ∀ j, j < lo ∨ j ∈ pr →
          m'.rd64 (slot fp (BitVec.ofNat 64 j)) =
            m.rd64 (slot fp (BitVec.ofNat 64 j))
    | o => CountedSim n L P f0 σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2) (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2) o reserved := by
  obtain ⟨n, hn, run⟩ := certificate.sound (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp)
    lower fits inside abi low hprotected pre surroundings world
  have routed := run.counter_dispatch inside bound edge far target
  refine ⟨n, hn, ?_⟩
  cases outcome <;> exact routed


/-- A decreasing runtime-budget tree. `passes` remains the lowering parameter;
    it is deliberately independent of the remaining counter `fuel`. Children
    are recursive SOURCE certificates, including their recursive call children.
    Costs exclude the two initial literals, which are paid once at entry.
    The soundness theorem below executes the corresponding whole emitted suffix. -/
inductive NestedForever (L : Lay D) (reserved : Nat) (P : Programm D)
    (passes : Nat) (A : D.Fn → Nat) (C : D.Fn → List II) (dv : W) (Ks : Nat)
    (V : Vertrag D) {Γ : Ctx} {Λ : List (Res D)}
    (assumption : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) :
    Nat → World D → Env D Γ → Ausgang V true Γ → Nat → Type
  | zero {σ ρ} : NestedForever L reserved P passes A C dv Ks V assumption inv body
      0 σ ρ (.hardware (.fortschritt assumption)) 3
  | normal {fuel σ ρ σ' ρ' outcome ni nb nr}
      (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
      (child : recursiveBlockCost L reserved P passes A C dv Ks V true
        body σ ρ (.ok σ' ρ') nb)
      (tail : NestedForever L reserved P passes A C dv Ks V assumption inv body
        fuel σ' ρ' outcome nr) :
      NestedForever L reserved P passes A C dv Ks V assumption inv body
        (fuel + 1) σ ρ outcome (5 + ni + nb + nr)
  | next {fuel σ ρ σ' ρ' outcome ni nb nr}
      (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
      (child : recursiveBlockCost L reserved P passes A C dv Ks V true
        body σ ρ (.next rfl σ' ρ') nb)
      (tail : NestedForever L reserved P passes A C dv Ks V assumption inv body
        fuel σ' ρ' outcome nr) :
      NestedForever L reserved P passes A C dv Ks V assumption inv body
        (fuel + 1) σ ρ outcome (3 + ni + nb + nr)
  | leave {fuel σ ρ σ' ρ' ni nb}
      (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
      (child : recursiveBlockCost L reserved P passes A C dv Ks V true
        body σ ρ (.leave rfl σ' ρ') nb) :
      NestedForever L reserved P passes A C dv Ks V assumption inv body
        (fuel + 1) σ ρ (.ok σ' ρ') (3 + ni + nb)
  | early {fuel σ ρ outcome ni nb}
      (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
      (child : recursiveBlockCost L reserved P passes A C dv Ks V true body σ ρ outcome nb)
      (terminal : match outcome with
        | .ok .. | .next .. | .leave .. => False
        | _ => True) :
      NestedForever L reserved P passes A C dv Ks V assumption inv body
        (fuel + 1) σ ρ outcome (3 + ni + nb)
  | invariantStop {fuel σ ρ ni}
      (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 0)) :
      NestedForever L reserved P passes A C dv Ks V assumption inv body
        (fuel + 1) σ ρ (.logik .schleife) (5 + ni)

/-- Largest source-child charge in this particular tree, never a supplied
    whole-body execution bound. -/
def NestedForever.childCharge {P : Programm D} {passes A C dv Ks V Γ Λ}
    {assumption : D.Annahme} {inv : Expr D Γ Λ .bool} {body : Block D V true Γ Λ Λ}
    {fuel σ ρ outcome n}
    (tree : NestedForever L reserved P passes A C dv Ks V assumption inv body
      fuel σ ρ outcome n) : Nat :=
  match tree with
  | .zero => 0
  | .normal (ni := ni) (nb := nb) _ _ tail => max (ni + nb) tail.childCharge
  | .next (ni := ni) (nb := nb) _ _ tail => max (ni + nb) tail.childCharge
  | .leave (ni := ni) (nb := nb) _ _ => ni + nb
  | .early (ni := ni) (nb := nb) _ _ _ => ni + nb
  | .invariantStop (ni := ni) _ => ni

/-- Structural bound for the decreasing-budget source tree. The initialized
    soundness theorem below applies it to actual counted IR execution.
    No G-step or lowering-pass count is identified with an instruction count. -/
theorem NestedForever.structural_bound {P : Programm D} {passes A C dv Ks V Γ Λ}
    {assumption : D.Annahme} {inv : Expr D Γ Λ .bool} {body : Block D V true Γ Λ Λ}
    {fuel σ ρ outcome n}
    (tree : NestedForever L reserved P passes A C dv Ks V assumption inv body
      fuel σ ρ outcome n) :
    2 + n ≤ 5 + fuel * (5 + tree.childCharge) := by
  induction tree with
  | zero => simp [childCharge]
  | @normal fuel σ ρ σ' ρ' outcome ni nb nr invariant child tail ih
  | @next fuel σ ρ σ' ρ' outcome ni nb nr invariant child tail ih =>
    simp only [childCharge]
    have a := Nat.le_max_left (ni + nb) tail.childCharge
    have b := Nat.le_max_right (ni + nb) tail.childCharge
    have mul := Nat.mul_le_mul_left fuel (Nat.add_le_add_left b 5)
    rw [Nat.succ_mul]
    omega
  | leave invariant child | early invariant child terminal =>
    simp only [childCharge]
    rw [Nat.succ_mul]
    omega
  | invariantStop invariant =>
    simp only [childCharge]
    rw [Nat.succ_mul]
    omega

/-- The false invariant outcome executes the actual positive header and stops.
    The scratch slot is the one selected by expression lowering. -/
theorem forever_positive_invariant_stop_counted
    {P : Programm D} {passes A C dv Ks} {f : D.Fn} {Γ Λ}
    {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {fuel ni : Nat} {σ : World D} {ρ : Env D Γ}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 0))
    {fp pc : W}
    {lo K counter one tc tb : Nat} {ens : List II × Nat}
    {pr : List Nat} {cc cb : List II} {m : Mem}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens (counter :: one :: pr)
      (foreverTargets cc.length cb.length) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (abi : FB ≤ lo) (low : lo ≤ counter)
    (counterLow : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (locals : frei Γ reserved ≤ K)
    (hprotected : ∀ j ∈ pr, j < counter) (room : (frei Γ reserved) + 8 ≤ K)
    (jumpFits : 16 * (cc.length + cb.length + 8) < 2 ^ 31)
    (pre : PreS L m pc fp K (frei Γ reserved)
      ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved) ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 (frei Γ reserved)) ρ reserved)
    (around : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 (fuel + 1)))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (fuelFits : fuel + 1 < 2 ^ 64) :
    CountedStops (5 + ni) ⟨pc, fp⟩ m 104 := by
  have positive : (BitVec.ofNat 64 (fuel + 1) : W) ≠ 0 := by
    bv_omega
  obtain ⟨mh, headerRun, headerPre, headerWorld, frame, counterRead, unitRead⟩ :=
    counter_positive_source_counted inside pre world counterLow ordered allocated locals
      read readOne positive
  have slicePre : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
      (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
        (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved := by
    have grouped : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
        ((cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
          (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ++
          ([ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
            stopC 111 (frei Γ reserved))) ρ reserved := by
      simpa only [List.append_eq, List.nil_append, List.append_assoc] using headerPre
    exact grouped.left
  have stopped := forever_false_stop_counted (P := P) (σ' := σ) (ρ' := ρ) invariant lowerInv
    (ex := (64, -(16 * (cc.length + cb.length + 3 : Nat) : Int) - 64))
    (by simpa [exPlus, foreverTargets] using lowerBody) (by omega) room fitsInv fitsBody inside
    (by unfold frei; omega) (by intro j hj; simp only [List.mem_cons] at hj; rcases hj with rfl | rfl | hj <;> unfold frei; omega; omega; have := hprotected j hj; omega)
    slicePre (Umf.agreeW inside around (agreeW_of frame) (by omega)) headerWorld
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stopped.prefix headerRun


/-- The full positive suffix executes its actual source child with OWN protection.
    Canonical outcomes share the body endpoint; this is a prefix, not a loop bound. -/
theorem recursiveBlockCost.forever_full_positive_counted
    {P : Programm D} {passes A C dv Ks} {f : D.Fn} {Γ Λ}
    {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {fuel ni nb : Nat} {σ : World D} {ρ : Env D Γ}
    (invariant : ExprCost L reserved inv (frei Γ reserved) ni (· = 1))
    {outcome : Ausgang (vertragVon D f) true Γ}
    (child : recursiveBlockCost L reserved P passes A C dv Ks (vertragVon D f) true
      body σ ρ outcome nb)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp pc : W}
    {lo K counter one tc tb : Nat} {ens : List II × Nat}
    {pr : List Nat} {cc cb : List II} {m : Mem}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens (counter :: one :: pr)
      (foreverTargets cc.length cb.length) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (abi : FB ≤ lo) (low : lo ≤ counter)
    (counterLow : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (locals : frei Γ reserved ≤ K)
    (hprotected : ∀ j ∈ pr, j < counter) (room : (frei Γ reserved) + 8 ≤ K)
    (jumpFits : 16 * (cc.length + cb.length + 8) < 2 ^ 31)
    (pre : PreS L m pc fp K (frei Γ reserved)
      ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved) ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 (frei Γ reserved)) ρ reserved)
    (around : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 (fuel + 1)))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (fuelFits : fuel + 1 < 2 ^ 64) :
    ∃ n, n ≤ 3 + ni + nb ∧ CountedSim n L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m
      ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length))
      ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + 128)
      ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (foreverTargets cc.length cb.length).2) outcome reserved := by
    obtain ⟨mh, headerRun, headerPre, headerWorld, frame, counterRead, unitRead⟩ :=
      counter_positive_source_counted inside pre world counterLow ordered allocated locals
        read readOne (by bv_omega)
    have sourcePre : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
        (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
          (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved := by
      have grouped : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
          ((cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
            (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ++
            ([ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
              stopC 111 (frei Γ reserved))) ρ reserved := by
        simpa only [List.append_eq, List.nil_append, List.append_assoc] using headerPre
      exact grouped.left
    have lowF : lo ≤ frei Γ reserved := by unfold frei; omega
    have own : ∀ j ∈ counter :: one :: pr, j < frei Γ reserved := by
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj <;> unfold frei
      · omega
      · omega
      · have := hprotected j hj; omega
    obtain ⟨nb', bodyBound, bodyRun⟩ := child.positive_source_counted invariant lowerInv
      (ex := (64, -(16 * (cc.length + cb.length + 3 : Nat) : Int) - 64))
      (by simpa [exPlus, foreverTargets] using lowerBody)
      fitsInv inside abi lowF own sourcePre
      (Umf.agreeW inside around (agreeW_of frame) (by omega)) headerWorld fitsBody
      (e := (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length))
      (eL := (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + 128)
      (eN := ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (foreverTargets cc.length cb.length).2)) rfl (by simp [exPlus]) (by simp [exPlus, foreverTargets])
    have stripped : CountedSim nb' L P f σ0 ρ0 rp cfp fp lo K pr
        ⟨pc + 16 + 16, fp⟩ mh
        ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length))
        ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + 128)
        ((pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (foreverTargets cc.length cb.length).2) outcome reserved := by
      cases outcome with
      | ok σ ρ | leave h σ ρ | next h σ ρ =>
        obtain ⟨m', run, frame, env, world, kept⟩ := bodyRun
        exact ⟨m', run, frame, env, world, fun j hj => kept j (by simp [hj])⟩
      | zurueck | why | logik | hardware => exact bodyRun
    exact ⟨2 + nb', by omega, CountedSim.prefix abi headerRun
      (agreeW_of (frame.mono low))
      (keeps_of_agreeW inside (agreeW_of frame) hprotected
        (by have h := locals; unfold frei at h; omega)) stripped⟩

section NestedSound
set_option maxRecDepth 10000
/-- Execute the complete emitted suffix from source children and a decreasing
    runtime counter, including both jumps on every normal backedge. -/
theorem NestedForever.sound
    {P : Programm D} {passes A C dv Ks} {f : D.Fn} {Γ Λ}
    {assumption : D.Annahme} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {fuel σ ρ outcome n}
    (tree : NestedForever L reserved P passes A C dv Ks (vertragVon D f)
      assumption inv body fuel σ ρ outcome n)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp pc : W}
    {lo K counter one tc tb : Nat} {ens : List II × Nat}
    {pr : List Nat} {cc cb : List II} {m : Mem}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens (counter :: one :: pr)
      (foreverTargets cc.length cb.length) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (abi : FB ≤ lo) (low : lo ≤ counter)
    (counterLow : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (locals : frei Γ reserved ≤ K)
    (hprotected : ∀ j ∈ pr, j < counter) (room : (frei Γ reserved) + 8 ≤ K)
    (jumpFits : 16 * (cc.length + cb.length + 8) < 2 ^ 31)
    (pre : PreS L m pc fp K (frei Γ reserved)
      ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved) ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 (frei Γ reserved)) ρ reserved)
    (around : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 fuel))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (fuelFits : fuel < 2 ^ 64) :
    ∃ k, k ≤ n ∧ CountedSim k L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 11)))
      (pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 11))) pc outcome reserved := by
  induction tree generalizing m pc with
  | zero =>
    exact ⟨3, by omega, forever_zero_header_counted inside pre world locals room jumpFits
      (by simpa using read) (by unfold frei; omega)⟩
  | @normal fuel σ ρ σ' ρ' outcome ni nb nr invariant child tail ih =>
    obtain ⟨mh, headerRun, headerPre, headerWorld, frame, counterRead, unitRead⟩ :=
      counter_positive_source_counted inside pre world counterLow ordered allocated locals
        read readOne (by bv_omega)
    have sourcePre : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
        (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
          (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved := by
      have grouped : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
          ((cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
            (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ++
            ([ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
              stopC 111 (frei Γ reserved))) ρ reserved := by
        simpa only [List.append_eq, List.nil_append, List.append_assoc] using headerPre
      exact grouped.left
    have lowF : lo ≤ frei Γ reserved := by unfold frei; omega
    have own : ∀ j ∈ counter :: one :: pr, j < frei Γ reserved := by
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj <;> unfold frei
      · omega
      · omega
      · have := hprotected j hj; omega
    obtain ⟨nb', bodyBound, bodyRun⟩ := child.positive_source_counted (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp) invariant lowerInv
      (ex := (64, -(16 * (cc.length + cb.length + 3 : Nat) : Int) - 64))
      (by simpa [exPlus, foreverTargets] using lowerBody)
      fitsInv inside abi lowF own sourcePre
      (Umf.agreeW inside around (agreeW_of frame) (by omega)) headerWorld fitsBody
      (e := (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length))
      (eL := (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + 128)
      (eN := pc) rfl (by simp [exPlus]) (by
        simp only [exPlus, Prod.snd]
        have delta : -(16 * (cc.length + cb.length + 3 : Nat) : Int) - 64 + 16 * (4 : Nat) =
            -(16 * (cc.length + cb.length + 3 : Nat) : Int) := by omega
        rw [delta]
        have endEq : (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 +
            BitVec.ofNat 64 (16 * cb.length) =
            pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 3)) := by
          change pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1) +
            BitVec.ofNat 64 (16 * cc.length) + BitVec.ofNat 64 (16 * 1) +
            BitVec.ofNat 64 (16 * cb.length) = _
          simp only [pc_add]
          congr 2
          omega
        rw [endEq, BitVec.ofInt_neg, BitVec.ofInt_mul, BitVec.ofInt_natCast]
        change pc = pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 3)) +
          -(BitVec.ofNat 64 16 * BitVec.ofNat 64 (cc.length + cb.length + 3))
        rw [← BitVec.ofNat_mul, BitVec.add_neg_eq_sub, BitVec.add_sub_cancel])
    obtain ⟨m', bodyRun, bodyFrame, bodyEnv, bodyWorld, bodyKeep⟩ := bodyRun
    have code := codeAt_agreeWIn inside bodyFrame headerPre.code headerPre.far
    have suffix : CodeAt m' ((pc + 16 + 16) + BitVec.ofNat 64
        (16 * (cc.length + 1 + cb.length)))
        ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved) ++
          [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
          stopC 111 (frei Γ reserved)) := by
      have grouped : CodeAt m' (pc + 16 + 16)
          ((cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb) ++
          ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved) ++
          [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
          stopC 111 (frei Γ reserved))) := by
        simpa only [List.append_eq, List.nil_append, List.append_assoc] using code
      simpa only [List.length_append, List.length_singleton] using codeAt_right grouped
    have endEq : (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 +
        BitVec.ofNat 64 (16 * cb.length) =
        (pc + 16 + 16) + BitVec.ofNat 64 (16 * (cc.length + 1 + cb.length)) := by
      change _ + _ + BitVec.ofNat 64 (16 * 1) + _ = _
      simp only [pc_add]
    rw [endEq] at bodyRun
    have ji := suffix 0 (by simp)
    simp only [List.cons_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci] at ji
    have jump := run_step (t := ⟨_, fp⟩) ji (by decide) (run_jmp ji)
    rw [show sx (II.f 64) = (64 : W) by decide] at jump
    have backCode := codeAt_right (a := [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)) suffix
    have backPC : ((pc + 16 + 16) + BitVec.ofNat 64 (16 * (cc.length + 1 + cb.length))) +
        BitVec.ofNat 64 (16 * ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)).length) =
        pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 7)) := by
      change pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1) +
        BitVec.ofNat 64 (16 * (cc.length + 1 + cb.length)) + BitVec.ofNat 64 (16 * 4) = _
      simp only [pc_add]
      congr 2 <;> omega
    rw [backPC] at backCode
    have bj := backCode 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci] at bj
    have backRun := run_step (t := ⟨_, fp⟩) bj (by decide) (run_jmp bj)
    rw [sx_lit (by unfold lit32; simp; omega)] at backRun
    have backTarget : pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 7)) +
        BitVec.ofInt 64 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) = pc := by
      rw [BitVec.ofInt_neg, BitVec.ofInt_mul, BitVec.ofInt_natCast]
      change pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 7)) +
        -(BitVec.ofNat 64 16 * BitVec.ofNat 64 (cc.length + cb.length + 7)) = pc
      rw [← BitVec.ofNat_mul, BitVec.add_neg_eq_sub, BitVec.add_sub_cancel]
    rw [backTarget] at backRun
    have jumpTarget : (pc + 16 + 16) + BitVec.ofNat 64 (16 * (cc.length + 1 + cb.length)) + 64 =
        pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 7)) := by
      change pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1) + _ +
        BitVec.ofNat 64 (16 * 4) = _
      simp only [pc_add]
      congr 2 <;> omega
    rw [jumpTarget] at jump
    have jumps : Counted 2
        ⟨(pc + 16 + 16) + BitVec.ofNat 64 (16 * (cc.length + 1 + cb.length)), fp⟩ m'
        ⟨pc, fp⟩ m' := .next jump (.next backRun (.refl _ _))
    have routed : Counted (nb' + 2) ⟨pc + 16 + 16, fp⟩ mh ⟨pc, fp⟩ m' :=
      bodyRun.trans jumps
    have allFrame := (agreeW_of (frame.mono low)).trans bodyFrame
    have ownWords := bodyKeep counter (by simp)
    rw [counterRead] at ownWords
    have fuelRead : m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 fuel) := by
      have decEq : (BitVec.ofNat 64 (fuel + 1) : W) - 1 = BitVec.ofNat 64 fuel := by
        rw [BitVec.ofNat_add]
        exact BitVec.add_sub_cancel _ _
      exact ownWords.trans (congrArg some decEq)
    have oneRead := (bodyKeep one (by simp)).trans unitRead
    have ownOuter : Keeps fp pr mh m' := fun j hj => bodyKeep j (by simp [hj])
    have headerOuter := keeps_of_agreeW inside (agreeW_of frame) hprotected (by have h := locals; unfold frei at h; omega)
    have nextPre : PreS L m' pc fp K (frei Γ reserved) _ ρ' reserved :=
      ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame allFrame,
        codeAt_agreeWIn inside allFrame pre.code pre.far, pre.far, bodyEnv, trivial, wstab_true _ _⟩
    obtain ⟨nr', tailBound, tailRun⟩ := ih nextPre (Umf.agreeW inside around allFrame abi)
      bodyWorld fuelRead oneRead (by omega)
    exact ⟨2 + (nb' + 2) + nr', by omega,
      CountedSim.prefix abi (headerRun.trans routed) allFrame
        (headerOuter.trans ownOuter) tailRun⟩
  | @next fuel σ ρ σ' ρ' outcome ni nb nr invariant child tail ih =>
    obtain ⟨mh, headerRun, headerPre, headerWorld, frame, counterRead, unitRead⟩ :=
      counter_positive_source_counted inside pre world counterLow ordered allocated locals
        read readOne (by bv_omega)
    have sourcePre : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
        (cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
          (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ρ reserved := by
      have grouped : PreS L mh (pc + 16 + 16) fp K (frei Γ reserved)
          ((cc ++ ([ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++
            (cb ++ ([ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))))) ++
            ([ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
              stopC 111 (frei Γ reserved))) ρ reserved := by
        simpa only [List.append_eq, List.nil_append, List.append_assoc] using headerPre
      exact grouped.left
    have lowF : lo ≤ frei Γ reserved := by unfold frei; omega
    have own : ∀ j ∈ counter :: one :: pr, j < frei Γ reserved := by
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj <;> unfold frei
      · omega
      · omega
      · have := hprotected j hj; omega
    obtain ⟨nb', bodyBound, bodyRun⟩ := child.positive_source_counted (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp) invariant lowerInv
      (ex := (64, -(16 * (cc.length + cb.length + 3 : Nat) : Int) - 64))
      (by simpa [exPlus, foreverTargets] using lowerBody)
      fitsInv inside abi lowF own sourcePre
      (Umf.agreeW inside around (agreeW_of frame) (by omega)) headerWorld fitsBody
      (e := (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length))
      (eL := (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 + BitVec.ofNat 64 (16 * cb.length) + 128)
      (eN := pc) rfl (by simp [exPlus]) (by
        simp only [exPlus, Prod.snd]
        have delta : -(16 * (cc.length + cb.length + 3 : Nat) : Int) - 64 + 16 * (4 : Nat) =
            -(16 * (cc.length + cb.length + 3 : Nat) : Int) := by omega
        rw [delta]
        have endEq : (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 +
            BitVec.ofNat 64 (16 * cb.length) =
            pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 3)) := by
          change pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1) +
            BitVec.ofNat 64 (16 * cc.length) + BitVec.ofNat 64 (16 * 1) +
            BitVec.ofNat 64 (16 * cb.length) = _
          simp only [pc_add]
          congr 2
          omega
        rw [endEq, BitVec.ofInt_neg, BitVec.ofInt_mul, BitVec.ofInt_natCast]
        change pc = pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 3)) +
          -(BitVec.ofNat 64 16 * BitVec.ofNat 64 (cc.length + cb.length + 3))
        rw [← BitVec.ofNat_mul, BitVec.add_neg_eq_sub, BitVec.add_sub_cancel])
    obtain ⟨m', bodyRun, bodyFrame, bodyEnv, bodyWorld, bodyKeep⟩ := bodyRun
    have allFrame := (agreeW_of (frame.mono low)).trans bodyFrame
    have ownWords := bodyKeep counter (by simp)
    rw [counterRead] at ownWords
    have fuelRead : m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 fuel) := by
      have decEq : (BitVec.ofNat 64 (fuel + 1) : W) - 1 = BitVec.ofNat 64 fuel := by
        rw [BitVec.ofNat_add]
        exact BitVec.add_sub_cancel _ _
      exact ownWords.trans (congrArg some decEq)
    have oneRead := (bodyKeep one (by simp)).trans unitRead
    have ownOuter : Keeps fp pr mh m' := fun j hj => bodyKeep j (by simp [hj])
    have headerOuter := keeps_of_agreeW inside (agreeW_of frame) hprotected (by have h := locals; unfold frei at h; omega)
    have nextPre : PreS L m' pc fp K (frei Γ reserved) _ ρ' reserved :=
      ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame allFrame,
        codeAt_agreeWIn inside allFrame pre.code pre.far, pre.far, bodyEnv, trivial, wstab_true _ _⟩
    obtain ⟨nr', tailBound, tailRun⟩ := ih nextPre (Umf.agreeW inside around allFrame abi)
      bodyWorld fuelRead oneRead (by omega)
    exact ⟨2 + nb' + nr', by omega,
      CountedSim.prefix abi (headerRun.trans bodyRun) allFrame
        (headerOuter.trans ownOuter) tailRun⟩
  | leave invariant child =>
    obtain ⟨k, bound, run⟩ := recursiveBlockCost.forever_full_positive_counted
      (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp)
      invariant child lowerInv lowerBody fitsInv fitsBody inside abi low counterLow ordered
      allocated locals hprotected room jumpFits pre around world read readOne fuelFits
    refine ⟨k, bound, ?_⟩
    change CountedReach k L fp lo K pr ⟨pc, fp⟩ m _ _ _ reserved at run ⊢
    have endpoint : (pc + 16 + 16) + BitVec.ofNat 64 (16 * cc.length) + 16 +
        BitVec.ofNat 64 (16 * cb.length) + 128 =
        pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 11)) := by
      change pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1) +
        BitVec.ofNat 64 (16 * cc.length) + BitVec.ofNat 64 (16 * 1) +
        BitVec.ofNat 64 (16 * cb.length) + BitVec.ofNat 64 (16 * 8) = _
      simp only [pc_add]
      congr 2 <;> omega
    simpa only [endpoint] using run
  | @early fuel σ ρ outcome ni nb invariant child terminal =>
    obtain ⟨k, bound, run⟩ := recursiveBlockCost.forever_full_positive_counted
      (σ0 := σ0) (ρ0 := ρ0) (rp := rp) (cfp := cfp)
      invariant child lowerInv lowerBody fitsInv fitsBody inside abi low counterLow ordered
      allocated locals hprotected room jumpFits pre around world read readOne fuelFits
    refine ⟨k, bound, ?_⟩
    cases outcome <;> simp_all [CountedSim]
  | invariantStop invariant =>
    refine ⟨_, Nat.le_refl _, ?_⟩
    exact forever_positive_invariant_stop_counted (P := P) invariant lowerInv lowerBody fitsInv fitsBody
      inside abi low counterLow ordered allocated locals hprotected room jumpFits pre around
      world read readOne fuelFits
/-- Initialize both reserved words once and bound the complete emitted loop.
    The maximum child charge is computed from the source-certificate tree. -/
theorem NestedForever.initialized_sound
    {P : Programm D} {passes A C dv Ks} {f : D.Fn} {Γ Λ}
    {assumption : D.Annahme} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {fuel σ ρ outcome n}
    (tree : NestedForever L reserved P passes A C dv Ks (vertragVon D f)
      assumption inv body fuel σ ρ outcome n)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp pc : W}
    {lo K counter one tc tb : Nat} {ens : List II × Nat}
    {pr : List Nat} {cc cb : List II} {m : Mem}
    (lowerInv : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (lowerBody : lowB (reserved := reserved) passes A L lo ens (counter :: one :: pr)
      (foreverTargets cc.length cb.length) body = some (cb, tb))
    (fitsInv : tc ≤ Ks) (fitsBody : tb ≤ Ks)
    (inside : WIn L fp Ks K) (abi : FB ≤ lo) (low : lo ≤ counter)
    (counterLow : FB ≤ counter) (ordered : counter < one)
    (allocated : one < FB + reserved) (locals : frei Γ reserved ≤ K)
    (hprotected : ∀ j ∈ pr, j < counter) (room : (frei Γ reserved) + 8 ≤ K)
    (jumpFits : 16 * (cc.length + cb.length + 8) < 2 ^ 31)
    (literal : lit32 (fuel : Int) = true)
    (pre : PreS L m pc fp K (frei Γ reserved)
      ([ci 1 counter (fuel : Int) 0] ++ [ci 1 one 1 0] ++ ((foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
        cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved) ++
        [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0]) ++
        stopC 111 (frei Γ reserved))) ρ reserved)
    (around : Umf L A C dv m fp Ks K) (world : WeltAt m L σ)
    (fuelFits : fuel < 2 ^ 64) :
    ∃ k, k ≤ 5 + fuel * (5 + tree.childCharge) ∧ CountedSim k L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc, fp⟩ m (pc + 16 + 16 + BitVec.ofNat 64 (16 * (cc.length + cb.length + 11)))
      (pc + 16 + 16 + BitVec.ofNat 64 (16 * (cc.length + cb.length + 11))) (pc + 16 + 16) outcome reserved := by
  obtain ⟨m1, run1, pre1, world1, agree1, read1⟩ :=
    reserved_literal_source_entry inside pre world counterLow (by omega) locals literal
  obtain ⟨m2, run2, pre2, world2, agree2, read2⟩ :=
    reserved_literal_source_entry inside pre1 world1 (by omega) allocated locals (by decide)
  have counterRead : m2.rd64 (slot fp (BitVec.ofNat 64 counter)) =
      some (BitVec.ofNat 64 fuel) := by
    rw [agree_rd_low agree2 pre1.frame.room ordered (by unfold frei at locals; omega)]
    simpa only [BitVec.ofInt_natCast] using read1
  have agree := agree1.trans (agree2.mono (Nat.le_of_lt ordered))
  obtain ⟨k, bound, run⟩ := tree.sound lowerInv lowerBody fitsInv fitsBody
    inside abi low counterLow ordered allocated locals hprotected room jumpFits pre2
    (Umf.agreeW inside around (agreeW_of agree) (by omega)) world2 counterRead read2 fuelFits
  refine ⟨2 + k, Nat.le_trans (by omega) tree.structural_bound, ?_⟩
  exact CountedSim.prefix abi (run1.trans run2)
    (agreeW_of (agree.mono low))
    (keeps_of_agreeW inside (agreeW_of agree) hprotected (by
      have := locals; unfold frei at *; omega)) run


/-- Recover the invariant, body, reserved counter pair and actual relocation from
    accepted statement lowering before applying the whole-loop execution theorem.
    The source tree is still required; this bridge does not certify recursive
    source children containing positive loops. -/
theorem NestedForever.accepted_sound
    {P : Programm D} {passes A C dv Ks} {f : D.Fn} {Γ Λ}
    {assumption : D.Annahme} {inv : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ}
    {σ ρ outcome n}
    (tree : NestedForever L reserved P passes A C dv Ks (vertragVon D f)
      assumption inv body passes σ ρ outcome n)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp pc : W}
    {lo K top : Nat} {ens : List II × Nat} {pr : List Nat}
    {code : List II} {m : Mem} {ex : Int × Int}
    (lower : lowS (l := true) (reserved := reserved) passes A L lo ens pr ex
      (.forever assumption inv body) = some (code, top))
    (fits : top ≤ Ks) (inside : WIn L fp Ks K) (abi : FB ≤ lo)
    (hprotected : ∀ j ∈ pr, j < (counterPair reserved (counterDepthB body)).1)
    (jumpFits : 16 * code.length < 2 ^ 31)
    (pre : PreS L m pc fp K (frei Γ reserved) code ρ reserved)
    (around : Umf L A C dv m fp Ks K) (world : WeltAt m L σ) :
    ∃ k, k ≤ 5 + passes * (5 + tree.childCharge) ∧
      CountedSim k L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * code.length))
        (pc + BitVec.ofNat 64 (16 * code.length)) (pc + 16 + 16) outcome reserved := by
  dsimp only [lowS] at lower
  split at lower
  next allowed =>
    obtain ⟨⟨cc, tc⟩, lowerInv, emitted⟩ := Option.bind_eq_some_iff.mp lower
    have budget := foreverC_budget emitted
    obtain ⟨cb, tb, lowerBody, rfl, fitsInv, fitsBody, _, _, scratch⟩ :=
      foreverC_actual emitted
    have pairStep : (counterPair reserved (counterDepthB body)).2 =
        (counterPair reserved (counterDepthB body)).1 + 1 := rfl
    have result := tree.initialized_sound (σ0 := σ0) (ρ0 := ρ0)
      (rp := rp) (cfp := cfp) lowerInv lowerBody
      (by omega) (by omega) inside abi allowed.1 (by omega) (by omega)
      allowed.2.1 (by have := inside.ks; omega) hprotected
      (by have := inside.ks; omega)
      (by simp only [foreverCode_length] at jumpFits; omega)
      (lit32_nat budget.1)
      (by simpa only [foreverCode, foreverCounterInit, List.append_assoc] using pre)
      around world budget.2
    have endpoint : pc + 16 + 16 + BitVec.ofNat 64 (16 * (cc.length + cb.length + 11)) =
        pc + BitVec.ofNat 64 (16 * (cc.length + cb.length + 13)) := by
      change pc + BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * 1) + _ = _
      simp only [pc_add]
      congr 2 <;> omega
    simpa only [foreverCode_length, endpoint] using result
  next refused => simp at lower


end NestedSound
end Gabbro.Stage0.Senke
