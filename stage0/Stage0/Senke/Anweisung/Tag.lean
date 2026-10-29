/-
  File:      stage0/Stage0/Senke/Anweisung/Tag.lean
  Subject:   Tagged dispatch, payload binding and the simulation of G's execArms.
-/
import Stage0.Senke.Anweisung.Verzweigung
import Stage0.Senke.Ausdruck.Tag
import Stage0.Senke.Anweisung

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration}

/-- The empty computation keeps the input word. -/
theorem input_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {w : Runner.W}
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some w) : Ok m pc fp K d [] (· = w) := by
  exact ⟨m, by simpa using (Star.refl (t := ⟨pc, fp⟩) (m := m)), Agree.refl _ _ _ _, w, hw, rfl⟩

theorem tagTest_ok {m : Runner.Mem} {pc fp : Runner.W} {K s k : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {w : Runner.W} {i : Nat} (hi : i < 256) (hk : k < 256)
    (htag : w &&& 255 = BitVec.ofNat 64 i)
    (hK : s + 3 ≤ K) (hp : PreS m pc fp K (s + 1) (tagTestC s k) ρ)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    Ok m pc fp K (s + 1) (tagTestC s k) (fun w => w = if i == k then 1 else 0) := by
  have hq : PreS m pc fp K (s + 1)
    (([ci 2 (s + 1) s 0] ++ [ci 1 (s + 2) 255 0] ++ [ci 8 (s + 1) (s + 1) (s + 2)]) ++
      [ci 1 (s + 2) k 0] ++ [ci 14 (s + 1) (s + 1) (s + 2)]) ρ := hp
  refine bin_ok2 (Pa := fun w => w = BitVec.ofNat 64 i)
    (bin_ok2 (mov_ok hq.left.left.left.left (by omega) (by omega) hw)
      (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun a b => some (a &&& b)) (fun a b ha hb => ⟨_, rfl, ?_⟩) rfl (by decide) (by omega) (by simpa only [Int.natCast_add, Int.ofNat_one, Int.add_assoc, show (1 : Int) + 1 = 2 from rfl] using hq.left.left))
    (fun m pc hp => const_ok hp (lit32_nat (by omega)) (by omega))
    (g := fun a b => some (Runner.IR.bool (a == b))) ?_ rfl (by decide) (by omega) (by simpa only [Int.natCast_add, Int.ofNat_one, Int.add_assoc, show (1 : Int) + 1 = 2 from rfl] using hq)
  · rw [ha, hb]; exact htag
  · intro a b ha hb
    refine ⟨_, rfl, ?_⟩
    rw [ha, hb, BitVec.ofInt_natCast, bool_word]
    have he : (BitVec.ofNat 64 i == BitVec.ofNat 64 k) = (i == k) := by
      by_cases he : i = k
      · simp [he]
      · have hn : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 k := by
          intro hh
          have ht := congrArg BitVec.toNat hh
          simp only [BitVec.toNat_ofNat] at ht
          omega
        rw [beq_eq_false_iff_ne.mpr hn, beq_eq_false_iff_ne.mpr he]
    rw [he]

theorem tagPayload_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {lo hi : Int} {v : Zahl lo hi} {w : Runner.W} (hl : lit32 lo = true) (hK : s + 2 ≤ K)
    (hp : Pre m pc fp K s
      [ci 1 (s + 1) 8 0, ci 12 s s (s + 1), ci 1 (s + 1) lo 0, ci 3 s s (s + 1)] ρ W)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w)
    (hoff : w >>> 8 = BitVec.ofNat 64 (sumOff (some (lo, hi)) v)) :
    Ok m pc fp K s
      [ci 1 (s + 1) 8 0, ci 12 s s (s + 1), ci 1 (s + 1) lo 0, ci 3 s s (s + 1)]
      (Enc (D := D) (.int lo hi) v) := by
  have hq : Pre m pc fp K s (([] ++ [ci 1 (s + 1) 8 0] ++ [ci 12 s s (s + 1)]) ++
      [ci 1 (s + 1) lo 0] ++ [ci 3 s s (s + 1)]) ρ W := hp
  refine bin_ok2 (Pa := fun x => x = w >>> 8)
    (bin_ok2 (input_ok hw) (fun m pc hp => const_ok hp (by decide) (by omega))
      (g := fun a b => some (a >>> (b.toNat % 64)))
      (fun a b ha hb => ⟨_, rfl, by rw [ha, hb]; rfl⟩) rfl (by decide) (by omega) (by simpa only [Int.natCast_add, Int.ofNat_one, Int.add_assoc, show (1 : Int) + 1 = 2 from rfl] using hq.left.left))
    (fun m pc hp => const_ok hp hl (by omega)) (g := fun a b => some (a + b))
    (fun a b ha hb => ⟨_, rfl, ?_⟩) rfl (by decide) (by omega) hq
  simp only [Enc]
  rw [ha, hb, hoff]
  simp only [sumOff]
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  have := v.lo_le
  omega

/-- Remove the payload binding after any outcome of an arm. -/
theorem Sim.schrumpfArm {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp : Runner.W} {lo K : Nat} {pr : List Nat}
    {l : Bool} {Γ : Ctx} {c : Option (Int × Int)} {o : Ausgang (vertragVon D f) l (ArmCtx Γ c)}
    {t : T} {m : Runner.Mem} {e eL eN : Runner.W}
    (h : Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => rcases p with ⟨a, b⟩; exact Sim.schrumpf h

/-- A predicate over every block of a tagged dispatch, respecting each payload context. -/
def ArmsAll {V : Vertrag D} (H : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → Prop) : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → Prop
  | _, _, _, _, _, .nil => True
  | _, _, _, _, _, .cons b rest => H b ∧ ArmsAll H rest

section
variable {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} {L : Lay D} {P : Programm D}
  {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp : Runner.W} {lo Ks K : Nat}
  {ens : List II × Nat} {pr : List Nat}

/-- The block simulation needed by dispatch, supplied by the mutual syntax induction. -/
def BlockRuns (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (L : Lay D) (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (cap : Nat)
    (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp fp : Runner.W)
    (lo Ks K : Nat) (ens : List II × Nat) (pr : List Nat)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D (vertragVon D f) l Γ Λ Λ') : Prop :=
  ∀ ex cb tb, lowB A L lo ens pr ex b = some (cb, tb) → tb + cap ≤ Ks → 16 * cb.length < 2 ^ 31 →
  ∀ m pc σ ρ, PreS m pc fp K (frei Γ) cb ρ → lo ≤ frei Γ →
    Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * cb.length))
      (pc + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R b σ ρ)

local notation "BR" => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K ens pr

theorem tagArm_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {c : Option (Int × Int)}
    {b : Block D (vertragVon D f) l (ArmCtx Γ c) Λ Λ'} {cp cb : List II} {tb : Nat} {ex : Int × Int}
    (hb : BR b) (hcb : lowB A L lo ens pr ex b = some (cb, tb)) (htb : tb + cap ≤ Ks)
    (hcp : tagPayloadC (frei Γ) c = some cp) (hs : 16 * (cp.length + cb.length) < 2 ^ 31)
    (hK : frei Γ + 3 ≤ Ks) (hW : WIn L fp Ks K) (hlo : FB ≤ lo)
    (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ} {w : Runner.W}
    (v : Nutzlast c) (hw : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w)
    (hoff : w >>> 8 = BitVec.ofNat 64 (sumOff c v))
    (hp : PreS m pc fp K (frei Γ) (cp ++ cb) ρ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (cp ++ cb).length))
      (pc + BitVec.ofNat 64 (16 * (cp ++ cb).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cp ++ cb).length) + BitVec.ofInt 64 ex.2)
      ((execBlock O passes R b σ (armEnv v ρ)).schrumpfArm c) := by
  cases c with
  | none =>
    simp only [tagPayloadC, Option.some.injEq] at hcp
    subst cp
    exact hb ex cb tb hcb htb (by simpa using hs) m pc σ ρ hp hlo2 hu hk hWa hpr
  | some p =>
    rcases p with ⟨a, z⟩
    simp only [tagPayloadC] at hcp
    split at hcp
    · next ha =>
      simp only [Option.some.injEq] at hcp
      subst cp
      have hks := hW.ks
      have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
      obtain ⟨m1, st, a1s, w1, r1, e1⟩ := tagPayload_ok ha (by omega) hpw hw hoff
      have a1 := Agree.widen a1s hks
      have hq := hp.next a1 (Nat.le_refl _) (by omega)
      have hfr : frei (ArmCtx Γ (some (a, z))) = frei Γ + 1 := by simp [frei, ArmCtx, Nat.add_assoc]
      have hp1 : PreS m1 _ fp K (frei (ArmCtx Γ (some (a, z)))) cb (armEnv v ρ) :=
        ⟨by simp [frei, ArmCtx], hq.small, hq.frame, hq.code, hq.far, envAt_cons hq.env r1 e1,
         trivial, wstab_true _ _⟩
      have ih := hb ex cb tb hcb htb (by omega) m1 _ σ _ hp1
        (by rw [hfr]; omega)
        (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
        (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega))
        (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _)))
        (fun j hj => by have := hpr j hj; rw [hfr]; omega)
      rw [pc_add1]
      exact Sim.prefix hlo st (agreeW_of (a1.mono hlo2))
        (keeps_of_agreeW hW a1 hpr (by omega)) (Sim.schrumpf ih)
    · cases hcp
theorem lowTags_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D f) l Γ Λ Λ' cs)
    (hblocks : ArmsAll (fun b => BR b) arms) {k : Nat} {cd : List II} {top : Nat}
    (hc : lowTags A L lo ens pr ex arms k = some (cd, top)) (ht : top + cap ≤ Ks)
    (hs : 16 * cd.length < 2 ^ 31) (hW : WIn L fp Ks K) (hlo : FB ≤ lo)
    (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ} {w : Runner.W}
    (v : Wert D (.sum cs)) (hi : k + v.1.val < 256)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w)
    (htag : w &&& 255 = BitVec.ofNat 64 (k + v.1.val))
    (hoff : w >>> 8 = BitVec.ofNat 64 (sumOff (cs.get v.1) v.2))
    (hp : PreS m pc fp K (frei Γ) cd ρ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * cd.length))
      (pc + BitVec.ofNat 64 (16 * cd.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * cd.length) + BitVec.ofInt 64 ex.2)
      (execArms O passes R arms v σ ρ) := by
  cases arms with
  | nil => exact Fin.elim0 v.1
  | cons b rest =>
    simp only [lowTags] at hc
    split at hc
    · next hki =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
      obtain ⟨⟨cr, tr⟩, hcr, cp, hcp, ⟨cb, tb⟩, hcb, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [List.length_append, tagTestC, List.length_cons, List.length_nil] at hs
      have hp' : PreS m pc fp K (frei Γ)
          (tagTestC (frei Γ) k ++ [ci 19 (frei Γ + 1) (16 * ((cp ++ cb).length + 2)) 0] ++
            (cp ++ cb) ++ [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr) ρ := by
        simpa only [List.length_append, List.append_assoc, Int.natCast_add] using hp
      have hh := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ + 1) (b := k + v.1.val == k)
        (ot := execArms O passes R (.cons b rest) v σ ρ)
        (oe := execArms O passes R (.cons b rest) v σ ρ)
        (by omega) (by have := hW.ks; omega) (by
          simp only [tagTestC, List.length_cons, List.length_nil, List.length_append]
          omega) hW hlo hlo0 hlo2 hpr
        (fun hpc => tagTest_ok hi hki htag (by have := hW.ks; omega)
          ⟨by have := hpc.ctx; omega, hpc.small, hpc.frame, hpc.code, hpc.far, hpc.env,
            trivial, wstab_true _ _⟩ hw)
        (fun hb m' pc' hp1 ha hu1 hk1 hw1 => ?_)
        (fun hb m' pc' hp1 ha hu1 hk1 hw1 => ?_) hp' hu hk hWa
      · simpa only [ite_self, List.length_append, List.length_singleton, Nat.add_assoc] using hh
      · have hz : v.1.val = 0 := by have := eq_of_beq hb; omega
        rcases v with ⟨⟨i, hiv⟩, nutz⟩
        change i = 0 at hz
        subst i
        simp only [execArms]
        have hr : m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w := by
          rw [agree_rd_low ha hp.frame.room (by omega) (by have := hW.ks; omega)]; exact hw
        exact tagArm_ok hblocks.1 hcb (by omega) hcp (by omega) (by omega) hW hlo hlo0 hlo2 hpr
          nutz hr hoff hp1 hu1 hk1 hw1
      · have hn : v.1.val ≠ 0 := by intro hz; simp only [hz, Nat.add_zero, beq_self_eq_true] at hb; cases hb
        rcases v with ⟨⟨i, hiv⟩, nutz⟩
        cases i with
        | zero => exact (hn rfl).elim
        | succ i =>
          simp only [execArms]
          have hr : m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w := by
            rw [agree_rd_low ha hp.frame.room (by omega) (by have := hW.ks; omega)]; exact hw
          exact lowTags_ok rest hblocks.2 hcr (by omega) (by omega) hW hlo hlo0 hlo2 hpr ⟨⟨i, Nat.lt_of_succ_lt_succ hiv⟩, nutz⟩
            (by simpa only [Fin.val_mk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi)
            hr (by simpa only [Fin.val_mk, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htag)
            hoff hp1 hu1 hk1 hw1
    · cases hc

termination_by cs.length

theorem onTag_ok {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    {v : Expr D Γ Λ (.sum cs)} {arms : Arms D (vertragVon D f) l Γ Λ Λ' cs}
    {cv ca : List II} {tv ta : Nat} {ex : Int × Int}
    (hblocks : ArmsAll (fun b => BR b) arms)
    (hcv : lowE L v (frei Γ) = some (cv, tv))
    (hca : lowTags A L lo ens pr ex arms 0 = some (ca, ta))
    (htv : tv ≤ Ks) (hta : ta + cap ≤ Ks) (hs : 16 * (cv.length + ca.length) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length)
    (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS m pc fp K (frei Γ) (cv ++ ca) ρ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length))
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cv ++ ca).length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (.onTag v arms) σ ρ) := by
  have htop := lowE_top v _ _ _ hcv
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, st, a1s, w, hw, hen⟩ := lowE_ok (σ.lese Λ v.orte) (σ.lese Λ v.orte)
    (fun _ h => h) v _ cv tv hcv htv m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
  have hfit : cs.length ≤ 256 := by
    have := hen.1
    simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have htag : w &&& 255 = BitVec.ofNat 64 (0 + (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ).1.val) := by
    rw [hen.2, sumWord_tag (D := D) hen.1, Nat.zero_add]
  have hoff : w >>> 8 = BitVec.ofNat 64 (sumOff _ (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ).2) := by
    rw [hen.2]; exact sumWord_off (D := D) hen.1 _
  have ih := lowTags_ok (σ := σ.lese Λ v.orte) arms hblocks hca hta (by omega) hW hlo hlo0 hlo2 hpr
    (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ)
    (by have := (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ).1.isLt; omega) hw htag hoff hp1
    (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
    (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega))
    (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _)))
  simp only [execStmt]
  rw [pc_add1]
  exact Sim.prefix hlo st (agreeW_of (a1.mono hlo2))
    (keeps_of_agreeW hW a1 hpr (by omega)) ih

/-- A dispatch with a bare arm and a payload arm is accepted, including a negative lower bound. -/
theorem onTag_ok_zeuge (A : D.Fn → Nat) (L : Lay D) (lo : Nat) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int) (f : D.Fn) :
    let cs := [none, some (-7, 13)]
    let arms : Arms D (vertragVon D f) false [.sum cs] [] [] cs := .cons .nil (.cons .nil .nil)
    ∃ code top, lowS A L lo ens pr ex (.onTag (.var .here) arms) = some (code, top) := by
  exact ⟨_, _, rfl⟩

end

end Gabbro.Stage0.Senke
