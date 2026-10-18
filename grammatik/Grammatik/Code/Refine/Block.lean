import Grammatik.Code.Lower.Stmt
import Grammatik.Code.Refine.Expr
import Grammatik.Code.Refine.Frame

/-
  File:      Grammatik/Code/Refine/Block.lean
  Subject:   TRACK L, PHASE L1 -- THE BUILDING BLOCKS OF THE STATEMENT REFINEMENT: running one
             lowered basic block, storing, and the trace that has no image.

    * `reach_block_jmp`, `reach_block_br`, `reach_block_ret` -- a block of the module whose body
      `seqI` runs is one `Reach`, ending in its terminator;
    * `store_of_load`, `stepI_store`, `storeTo_run` -- what the code of `storeTo` does;
    * `rep_merke`, `rep_lese` -- `Rep` does not see the trace, so the `lese`/`merke` of the
      semantics change nothing it speaks about.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res)

variable {D : Deklaration}

theorem rep_merke {lay : Layout D} {σ : World D} {m : Mem} (es : List (Gabbro.Grammatik.Ereignis D)) :
    Rep lay (σ.merke es) m ↔ Rep lay σ m := Iff.rfl

theorem rep_lese {lay : Layout D} {σ : World D} {m : Mem} (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) : Rep lay (σ.lese Λ os) m ↔ Rep lay σ m := Iff.rfl

/-! ## Running one block -/

theorem reach_block_jmp {M : Modl} {S : Sees} {fn : Nat} {lb k : Lbl} {b bk : Block}
    {m m' : Mem} {rs rs' : Regs} {ks : List Frame} {dst : Option Reg}
    (hb : M.blk fn lb = some b) (hbt : b.term = .jmp k) (hk : M.blk fn k = some bk)
    (hkp : bk.phis = []) (hs : seqI b.body m rs = some (m', rs')) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, k, 0, rs', dst⟩ ks) := by
  have h1 := reach_seq M S b.body m ⟨fn, lb, 0, rs, dst⟩ ks m' rs'
    ⟨b, hb, fun i h => by simp⟩ hs
  have h2 := reach_jmp (S := S) (m := m') (ks := ks)
    (f := ⟨fn, lb, 0 + b.body.length, rs', dst⟩) (l := k) (blk := b) (blk' := bk)
    ⟨hb, (show b.body.length ≤ 0 + b.body.length by omega), hbt⟩ hk hkp
  exact Reach.trans h1 h2

theorem reach_block_br {M : Modl} {S : Sees} {fn : Nat} {lb t e : Lbl} {b bk : Block}
    {m m' : Mem} {rs rs' : Regs} {ks : List Frame} {dst : Option Reg} {c : Opd} {x : BitVec 1}
    (hb : M.blk fn lb = some b) (hbt : b.term = .br c t e) (hs : seqI b.body m rs = some (m', rs'))
    (hc : c.ev rs' = some (.int 1 x)) (hk : M.blk fn (if x = 1 then t else e) = some bk)
    (hkp : bk.phis = []) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
      (.run m' ⟨fn, (if x = 1 then t else e), 0, rs', dst⟩ ks) := by
  have h1 := reach_seq M S b.body m ⟨fn, lb, 0, rs, dst⟩ ks m' rs'
    ⟨b, hb, fun i h => by simp⟩ hs
  have h2 := reach_br (S := S) (m := m') (ks := ks)
    (f := ⟨fn, lb, 0 + b.body.length, rs', dst⟩) (blk := b) (blk' := bk) (x := x)
    ⟨hb, (show b.body.length ≤ 0 + b.body.length by omega), hbt⟩ hc hk hkp
  exact Reach.trans h1 h2

/-- A block ending in `ret`: after its body the frame stands at the terminator. -/
theorem reach_block_end {M : Modl} {S : Sees} {fn : Nat} {lb : Lbl} {b : Block}
    {m m' : Mem} {rs rs' : Regs} {ks : List Frame} {dst : Option Reg}
    (hb : M.blk fn lb = some b) (hs : seqI b.body m rs = some (m', rs')) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m' ⟨fn, lb, b.body.length, rs', dst⟩ ks) := by
  have h1 := reach_seq M S b.body m ⟨fn, lb, 0, rs, dst⟩ ks m' rs'
    ⟨b, hb, fun i h => by simp⟩ hs
  simpa using h1

/-! ## Stores -/

theorem store_of_load {m : Mem} {b : Nat} {o : Int} {t : Ty} {v0 x : Val}
    (hl : m.load b o t = some v0) (hx : x.ty = t) : ∃ m', m.store b o t x = some m' := by
  unfold Mem.load at hl
  unfold Mem.store
  cases hb : m.blks b with
  | none => simp [hb] at hl
  | some blk =>
      simp only [hb] at hl ⊢
      by_cases hi : Mem.inside blk.size o t
      · simp [hi, hx]
      · simp [hi] at hl

theorem stepI_store {m m' : Mem} {rs : Regs} {t : Ty} {v p : Opd} {x : Val} {b : Nat} {o : Int}
    (hv : v.ev rs = some x) (hp : p.ev rs = some (.ptr b o)) (hs : m.store b o t x = some m') :
    stepI (.store t v p) m rs = some (m', rs) := by
  simp [stepI, hv, hp, hs]

theorem bool_zext : Val.ofInt 1 (0 : Int) = Val.ofInt 1 0 := rfl

/-- The register image of a value to its memory image. -/
theorem cvtM_frag (lay : Layout D) (τ : GTy) (v : Wert D τ) (hs : supp τ = true) (o : Opd) (r : Nat)
    (m : Mem) (rs : Regs) (hv : o.ev rs = some (encR lay τ v)) (hlt : OpdLt o r) (c : LR)
    (h : cvtM τ o r = some c) : Frag m rs r c (encM lay τ v) := by
  cases τ with
  | int lo hi =>
      simp only [cvtM] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hlt, hv⟩
      · simp at h
  | bool =>
      simp only [cvtM] at h
      obtain rfl := Option.some.inj h
      apply frag_one
      have e1 : encR lay .bool v = Val.ofInt 1 (if wbool v then 1 else 0) := by
        simp [encR, bool_ofInt]
        rfl
      rw [e1] at hv
      have e2 : encM lay .bool v = Val.ofInt 8 (if wbool v then 1 else 0) := rfl
      rw [e2]
      cases hb : wbool v <;>
        simp [stepI, hv, hb, Val.ty, Val.ofInt, Val.cast, Ar.zext_ofInt]
  | ptr n rw =>
      simp only [cvtM] at h
      obtain rfl := Option.some.inj h
      exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hlt, hv⟩
  | opt n =>
      simp only [cvtM] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hlt, hv⟩
      · simp at h
  | why n =>
      simp only [cvtM] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hlt, hv⟩
      · simp at h
  | sum cs =>
      simp only [cvtM] at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rs, rfl, Nat.le_refl _, fun _ _ => rfl, hlt, hv⟩
      · simp at h
  | _ => simp [supp] at hs

/-- **What the store code does**: the new memory is the old one with the value stored. -/
theorem storeTo_run (lay : Layout D) (τ : GTy) (v : Wert D τ) (hs : supp τ = true) (oe : Opd)
    (r1 : Nat) (p : Opd) (b : Nat) (o : Int) (m : Mem) (rs : Regs)
    (hv : oe.ev rs = some (encR lay τ v)) (hlt : OpdLt oe r1) (hp : p.ev rs = some (.ptr b o))
    (hlp : OpdLt p r1) (hl : ∃ x, m.load b o (memTy τ) = some x) (cs : List Instr) (r2 : Nat)
    (h : storeTo τ oe r1 p = some (cs, r2)) :
    ∃ m' rs', seqI cs m rs = some (m', rs') ∧ m.store b o (memTy τ) (encM lay τ v) = some m' ∧
      r1 ≤ r2 ∧ (∀ x, x < r1 → rs' x = rs x) := by
  unfold storeTo at h
  rcases hc : cvtM τ oe r1 with _ | ⟨cm, om, r3⟩
  · simp [hc] at h
  simp only [hc] at h
  obtain ⟨rfl, rfl⟩ : cs = cm ++ [storeI τ om p] ∧ r2 = r3 := by
    simpa [Prod.ext_iff] using (Option.some.inj h).symm
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := cvtM_frag lay τ v hs oe r1 m rs hv hlt (cm, om, r2) hc
  have hp1 : p.ev rs1 = some (.ptr b o) := by
    rw [ev_agree hag1 hlp]; exact hp
  obtain ⟨x, hx⟩ := hl
  obtain ⟨m', hm'⟩ := store_of_load hx (encM_ty lay v hs)
  refine ⟨m', rs1, ?_, hm', hr1, hag1⟩
  rw [seqI_append]
  simp only [hs1, Option.bind_some]
  simp only [seqI, storeI, stepI_store hev1 hp1 hm']

/-- **A new local**: the code `alloc`, `store` leaves a fresh block with the value in it. -/
theorem bind_run (lay : Layout D) {τ : GTy} (v : Wert D τ) (hs : supp τ = true) (om : Opd)
    (a : Reg) (m : Mem) (rs : Regs) (hom : om.ev rs = some (encM lay τ v)) (hlt : OpdLt om a) :
    ∃ m1 rs1, seqI [.alloc a (memTy τ), storeI τ om (.reg a)] m rs = some (m1, rs1) ∧
      m1.next = m.next + 1 ∧ (∀ x, x ≠ a → rs1 x = rs x) ∧ rs1 a = some (.ptr m.next 0) ∧
      m1.load m.next 0 (memTy τ) = some (encM lay τ v) ∧
      (m.Wf → m1.Wf) ∧
      (∀ σ : World D, WfL lay m → Rep lay σ m → Rep lay σ m1) ∧ (WfL lay m → WfL lay m1) ∧
      (∀ b, b < m.next → ∀ o t w, m.load b o t = some w → m1.load b o t = some w) := by
  have hsc := memTy_scalar hs
  have hty := encM_ty lay v hs
  obtain ⟨m1, hm1⟩ := alloc_store_ok m (memTy τ) (encM lay τ v) hsc hty
  have hom1 : om.ev (rs.set a (.ptr m.next 0)) = some (encM lay τ v) := by
    rw [ev_agree (r := a) (fun x hx => regs_set_ne rs a x _ (Nat.ne_of_lt hx)) hlt]; exact hom
  refine ⟨m1, (rs.set a (.ptr m.next 0)), ?_, ?_, ?_, regs_set_same _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · have hs1 : stepI (.alloc a (memTy τ)) m rs
        = some ((m.alloc (memTy τ).size false).1, rs.set a (.ptr m.next 0)) := rfl
    simp only [seqI, storeI]
    rw [hs1]
    simp only []
    rw [stepI_store hom1 (by simp [Opd.ev, regs_set_same]) hm1]
  · rw [store_next hm1]; simp [Mem.alloc]
  · intro x hx; exact regs_set_ne rs a x _ hx
  · exact load_store_of hm1 (dec_enc_encM lay v hs)
  · intro hw
    exact store_wf hm1 (alloc_wf hw _ _)
  · intro σ hW hR
    exact rep_store_other (rep_alloc hW.1 hR _ _) hm1
      ⟨fun t => Nat.ne_of_gt (hW.2.1 t), fun g => Nat.ne_of_gt (hW.2.2.1 g)⟩
  · intro hW
    exact wfL_store hm1 (wfL_alloc hW _ _)
  · intro b hb o t w hl
    rw [load_store_other hm1 (Or.inl (by omega)), alloc_load m _ _ b (by omega)]
    exact hl

/-- **A new local, as the lowering writes it** (`bindCode`): the value's register image is moved
    to its memory image, a fresh cell is allocated and stored into; afterwards the cell is the
    head of the environment. -/
theorem bindCode_run (lay : Layout D) {τ : GTy} {σ : World D} {Γ : Ctx} {cenv : List Reg}
    {ρ : Env D Γ} (v : Wert D τ) (oe : Opd) (r1 : Nat) (m : Mem) (rs : Regs)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m)
    (hev : oe.ev rs = some (encR lay τ v)) (hlt : OpdLt oe r1) (hc : ∀ x ∈ cenv, x < r1)
    {cb : List Instr} {a : Nat} {r2 : Nat} (h : bindCode τ oe r1 = some (cb, a, r2)) :
    ∃ m1 rs3, seqI cb m rs = some (m1, rs3) ∧ Rep lay σ m1 ∧
      EnvRep lay rs3 m1 (a :: cenv) (Env.cons v ρ) ∧ WfL lay m1 ∧ r1 ≤ a ∧ r2 = a + 1 ∧
      (∀ x, x < r1 → rs3 x = rs x) ∧ Fr lay cenv r1 m rs m1 rs3 ∧
      (∀ b, rs3 a = some (.ptr b 0) → m.next ≤ b) := by
  unfold bindCode at h
  rcases hcm : cvtM τ oe r1 with _ | ⟨cm, om, r3⟩
  · simp [hcm] at h
  simp only [hcm] at h
  have hs : supp τ = true := by
    cases hbb : supp τ
    · simp [hbb] at h
    · rfl
  simp only [hs, if_true] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hcb, hae, hr2⟩ := h'
  subst hcb
  subst hae
  subst hr2
  obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := cvtM_frag lay τ v hs oe r1 m rs hev hlt (cm, om, r3) hcm
  have hs2' : seqI cm m rs = some (m, rs2) := hs2
  obtain ⟨m1, rs3, hs3, hnext, hag3, hra, hld1, hwf1, hrep1, hwl1, hmem⟩ :=
    bind_run lay v hs om r3 m rs2 hev2 hlt2
  have hseq : seqI (cm ++ [.alloc r3 (memTy τ), storeI τ om (.reg r3)]) m rs = some (m1, rs3) := by
    rw [seqI_append, hs2', Option.bind_some]
    exact hs3
  have hr1' : r1 ≤ r3 := hr2
  have hag13 : ∀ r ∈ cenv, rs3 r = rs r := fun r hr' => by
    have l1 : r < r1 := hc r hr'
    have l3 : r < r3 := Nat.lt_of_lt_of_le l1 hr1'
    rw [hag3 r (Nat.ne_of_lt l3), hag2 r l1]
  have hE3 : EnvRep lay rs3 m cenv ρ := envRep_regs cenv ρ hag13 hE
  have hblt := envRep_blocks_lt hW.1 cenv ρ hE3
  have hE3' : EnvRep lay rs3 m1 cenv ρ :=
    envRep_load cenv ρ (fun r hr' b hb' hf o t w hl => hmem b (hblt r hr' b hb') o t w hl) hE3
  refine ⟨m1, rs3, hseq, hrep1 σ hW hR, ⟨⟨hs, m.next, hra,
    ⟨fun t => Nat.ne_of_gt (hW.2.1 t), fun g => Nat.ne_of_gt (hW.2.2.1 g), fun L => ⟨Nat.ne_of_gt (hW.2.2.2 L).1, Nat.ne_of_gt (hW.2.2.2 L).2⟩⟩,
    hld1,
    fun r' hr' b' hb' => Nat.ne_of_lt (hblt r' hr' b' hb')⟩, hE3'⟩, hwl1 hW, hr1', rfl, ?_, ?_, ?_⟩
  · intro x hx
    have l3 : x < r3 := Nat.lt_of_lt_of_le hx hr1'
    rw [hag3 x (Nat.ne_of_lt l3), hag2 x hx]
  · refine ⟨?_, by rw [hnext]; omega, ?_⟩
    · intro x hx
      have l3 : x < r3 := Nat.lt_of_lt_of_le hx hr1'
      rw [hag3 x (Nat.ne_of_lt l3), hag2 x hx]
    · intro b _ hb _ o t w hl
      exact hmem b hb o t w hl
  · intro b hb
    rw [hra] at hb
    have := Option.some.inj hb
    injection this with e1 e2
    exact Nat.le_of_eq e1

end Gabbro.Code.Lower
