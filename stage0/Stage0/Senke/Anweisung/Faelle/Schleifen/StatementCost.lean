/- Source-bound instruction costs for actual statement lowering. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted
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

end Gabbro.Stage0.Senke
