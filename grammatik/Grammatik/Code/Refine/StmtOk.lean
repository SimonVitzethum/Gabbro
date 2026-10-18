import Grammatik.Code.Refine.Stmt

/-
  File:      Grammatik/Code/Refine/StmtOk.lean
  Subject:   TRACK L, PHASE L1 -- THE MUTUAL REFINEMENT THEOREM (see `Stmt.lean` for what it says).

  `lowerS_ok`, `lowerB_ok`, `lowerEnd_ok`: by recursion on the statement. The leaf forms (the four
  assignments, `return`, `leave`, `next`) are proved here; the compound forms are assembled from the
  outcomes of their parts with `outok_lift` (a run to the continuation), `outok_mono` (a larger
  counter) and `outok_schrumpf` (a local goes out of scope).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl)

variable {D : Deklaration} {V : Vertrag D}

mutual

theorem lowerS_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerS lay cenv lv s lb k st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st' m rs ks dst (execStmt O passes R s σ ρ)
  | _, _, _, _, .assignGlob (Λ := Λ) g e _ _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs,
      ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      have hs : supp (D.gtyp g) = true := by
        cases hbb : supp (D.gtyp g)
        · simp [hbb] at h
        · rfl
      simp only [hs, if_true] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hst : storeTo (D.gtyp g) oe r1 (.glob (lay.ggblk g)) with _ | ⟨cs, r2⟩
      · simp [hst] at h
      simp only [hst] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      simp only [execStmt, OutOk]
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
      have hs1' : seqI ce m rs = some (m, rs1) := hs1
      obtain ⟨m', rs2, hs2, hst2, hr2, hag2⟩ := storeTo_run lay (D.gtyp g) (eval σl e σl ρ) hs oe r1
        (.glob (lay.ggblk g)) (lay.ggblk g) 0 m rs1 hev1 hlt1 rfl (fun x hx => nomatch hx)
        ⟨_, hR.2 g hs⟩ cs r2 hst
      have hseq : seqI (ce ++ cs) m rs = some (m', rs2) := by
        rw [seqI_append, hs1']; exact hs2
      refine ⟨m', rs2, reach_block_jmp hb rfl hbk hkp hseq, ?_⟩
      have hRn : Rep lay (σl.schreibGlob g Λ (eval σl e σl ρ)) m' :=
        rep_store_glob hL hRl g _ hs hst2
      refine post_store hRn hE hW hst2 (not_fresh_glob g) (fun r hr => ?_) (fun x hx => ?_)
      · have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hr1
        rw [hag2 r l1, hag1 r (hc r hr)]
      · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hc x hx) hr1) hr2
  | _, _, _, _, .ret (Λ := Λ) e _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR,
      hE, hW, hc => by
      simp only [lowerS] at h
      simp only [execStmt, OutOk]
      obtain ⟨f', hr, hf1, hf2, hret⟩ := lowerErg_ok lay hL cenv e lb st st' blks h M S fn hM
        (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
      exact ⟨m, f', hr, hf1, hf2, hret, hR, hW⟩
  | _, _, _, _, .leave .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.1
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, hR, hE, hW, hc⟩
  | _, _, _, _, .next .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.2
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, hR, hE, hW, hc⟩
  | _, _, _, _, .assignSlot (Λ := Λ) t f i e _ _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs,
      ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      have hs : supp (D.typ t f) = true := by
        cases hbb : supp (D.typ t f)
        · simp [hbb] at h
        · rfl
      simp only [hs, if_true] at h
      rcases hi : lowerE lay cenv i st.r with _ | ⟨ci, oi, r1⟩
      · simp [hi] at h
      simp only [hi] at h
      rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
      · simp [he] at h
      simp only [he] at h
      rcases hsa : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r2 with
        _ | ⟨ca, oa, r3⟩
      · simp [hsa] at h
      simp only [hsa] at h
      rcases hst : storeTo (D.typ t f) oe r3 oa with _ | ⟨cs, r4⟩
      · simp [hst] at h
      simp only [hst] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      simp only [execStmt, OutOk]
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ (i.orte ++ e.orte) := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fi, _⟩ := lowerE_ok lay hL i cenv st.r (ci, oi, r1) hi σl σl ρ m rs hRl hE hc
      obtain ⟨rsA, hsA, hrA, hagA, hltA, hevA⟩ := Fi
      have hsA' : seqI ci m rs = some (m, rsA) := hsA
      have hEA := envRep_regs cenv ρ (fun x hx => hagA x (hc x hx)) hE
      have hcA : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hrA
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv r1 (ce, oe, r2) he σl σl ρ m rsA hRl hEA hcA
      obtain ⟨rsB, hsB, hrB, hagB, hltB, hevB⟩ := Fe
      have hsB' : seqI ce m rsA = some (m, rsB) := hsB
      let z : Zahl 0 (D.count t - 1) := eval σl i σl ρ
      have hk0 : 0 ≤ z.n := z.lo_le
      have hk1 : z.n < D.count t := by have := z.le_hi; omega
      have hoi : oi.ev rsB = some (Val.ofInt (Ar.wid 0 (D.count t - 1)) z.n) := by
        rw [ev_agree hagB hltA]; exact hevA
      have hltA2 : OpdLt oi r2 := fun x hx => Nat.lt_of_lt_of_le (hltA x hx) hrB
      have hld : ∃ v, m.load (lay.gblk t) (lay.off t z.n f) (memTy (D.typ t f)) = some v :=
        ⟨_, hR.1 t z.n f hs hk0 hk1⟩
      have FA := slotAddr_frag lay hL t f hs z.n hk0 hk1 (.glob (lay.gblk t)) oi r2 m rsB rfl
        (fun x hx => nomatch hx) hoi hltA2 hld (ca, oa, r3) hsa
      obtain ⟨rsC, hsC, hrC, hagC, hltC, hevC⟩ := FA
      have hsC' : seqI ca m rsB = some (m, rsC) := hsC
      have hoe : oe.ev rsC = some (encR lay (D.typ t f) (eval σl e σl ρ)) := by
        rw [ev_agree hagC hltB]; exact hevB
      have hltB2 : OpdLt oe r3 := fun x hx => Nat.lt_of_lt_of_le (hltB x hx) hrC
      obtain ⟨m', rsD, hsD, hstD, hrD, hagD⟩ := storeTo_run lay (D.typ t f) (eval σl e σl ρ) hs oe
        r3 oa (lay.gblk t) (lay.off t z.n f) m rsC hoe hltB2 hevC hltC hld cs r4 hst
      have hseq : seqI (ci ++ ce ++ ca ++ cs) m rs = some (m', rsD) := by
        rw [seqI_append, seqI_append, seqI_append, hsA', Option.bind_some, hsB', Option.bind_some,
          hsC', Option.bind_some]
        exact hsD
      refine ⟨m', rsD, reach_block_jmp hb rfl hbk hkp hseq, ?_⟩
      have hRn : Rep lay (σl.schreibSlot t Λ z.n f (eval σl e σl ρ)) m' :=
        rep_store_slot hL hRl t z.n f _ hs hk0 hk1 hstD
      refine post_store hRn hE hW hstD (not_fresh_tab t) (fun r hr => ?_) (fun x hx => ?_)
      · have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hrA
        have l2 : r < r2 := Nat.lt_of_lt_of_le l1 hrB
        have l3 : r < r3 := Nat.lt_of_lt_of_le l2 hrC
        rw [hagD r l3, hagC r l2, hagB r l1, hagA r (hc r hr)]
      · have l1 : x < r1 := Nat.lt_of_lt_of_le (hc x hx) hrA
        have l2 : x < r2 := Nat.lt_of_lt_of_le l1 hrB
        have l3 : x < r3 := Nat.lt_of_lt_of_le l2 hrC
        exact Nat.lt_of_lt_of_le l3 hrD
  | _, _, _, _, .assignThru (Λ := Λ) p t ht f i e _ _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m,
      rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      have hs : supp (D.typ t f) = true := by
        cases hbb : supp (D.typ t f)
        · simp [hbb] at h
        · rfl
      simp only [hs, if_true] at h
      rcases hp : lowerE lay cenv p st.r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      simp only [hp] at h
      rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
      · simp [hi] at h
      simp only [hi] at h
      rcases he : lowerE lay cenv e r2 with _ | ⟨ce, oe, r3⟩
      · simp [he] at h
      simp only [he] at h
      rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r3 with _ | ⟨ca, oa, r4⟩
      · simp [hsa] at h
      simp only [hsa] at h
      rcases hst : storeTo (D.typ t f) oe r4 oa with _ | ⟨cs, r5⟩
      · simp [hst] at h
      simp only [hst] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      simp only [execStmt, OutOk]
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ (p.orte ++ i.orte ++ e.orte) := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fp, _⟩ := lowerE_ok lay hL p cenv st.r (cp, op, r1) hp σl σl ρ m rs hRl hE hc
      obtain ⟨rsP, hsP, hrP, hagP, hltP, hevP⟩ := Fp
      have hsP' : seqI cp m rs = some (m, rsP) := hsP
      have hEP := envRep_regs cenv ρ (fun x hx => hagP x (hc x hx)) hE
      have hcP : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hrP
      obtain ⟨Fi, _⟩ := lowerE_ok lay hL i cenv r1 (ci, oi, r2) hi σl σl ρ m rsP hRl hEP hcP
      obtain ⟨rsA, hsA, hrA, hagA, hltA, hevA⟩ := Fi
      have hsA' : seqI ci m rsP = some (m, rsA) := hsA
      have hEA := envRep_regs (rs' := rsA) cenv ρ (fun x hx => by
        rw [hagA x (hcP x hx), hagP x (hc x hx)]) hE
      have hcA : ∀ x ∈ cenv, x < r2 := fun x hx => Nat.lt_of_lt_of_le (hcP x hx) hrA
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv r2 (ce, oe, r3) he σl σl ρ m rsA hRl hEA hcA
      obtain ⟨rsB, hsB, hrB, hagB, hltB, hevB⟩ := Fe
      have hsB' : seqI ce m rsA = some (m, rsB) := hsB
      let z : Zahl 0 (D.count t - 1) := eval σl i σl ρ
      have hk0 : 0 ≤ z.n := z.lo_le
      have hk1 : z.n < D.count t := by have := z.le_hi; omega
      have hoi : oi.ev rsB = some (Val.ofInt (Ar.wid 0 (D.count t - 1)) z.n) := by
        rw [ev_agree hagB hltA]; exact hevA
      have hopP : op.ev rsB = some (.ptr (lay.gblk t) 0) := by
        have h1 : op.ev rsA = op.ev rsP := ev_agree hagA hltP
        have h2 : op.ev rsB = op.ev rsA := ev_agree hagB (fun x hx => Nat.lt_of_lt_of_le (hltP x hx) hrA)
        rw [h2, h1, hevP]
        simp [encR, ht]
      have hltA2 : OpdLt oi r3 := fun x hx => Nat.lt_of_lt_of_le (hltA x hx) hrB
      have hltP2 : OpdLt op r3 := fun x hx =>
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hltP x hx) hrA) hrB
      have hld : ∃ v, m.load (lay.gblk t) (lay.off t z.n f) (memTy (D.typ t f)) = some v :=
        ⟨_, hR.1 t z.n f hs hk0 hk1⟩
      have FA := slotAddr_frag lay hL t f hs z.n hk0 hk1 op oi r3 m rsB hopP hltP2 hoi hltA2 hld
        (ca, oa, r4) hsa
      obtain ⟨rsC, hsC, hrC, hagC, hltC, hevC⟩ := FA
      have hsC' : seqI ca m rsB = some (m, rsC) := hsC
      have hoe : oe.ev rsC = some (encR lay (D.typ t f) (eval σl e σl ρ)) := by
        rw [ev_agree hagC hltB]; exact hevB
      have hltB2 : OpdLt oe r4 := fun x hx => Nat.lt_of_lt_of_le (hltB x hx) hrC
      obtain ⟨m', rsD, hsD, hstD, hrD, hagD⟩ := storeTo_run lay (D.typ t f) (eval σl e σl ρ) hs oe
        r4 oa (lay.gblk t) (lay.off t z.n f) m rsC hoe hltB2 hevC hltC hld cs r5 hst
      have hseq : seqI (cp ++ ci ++ ce ++ ca ++ cs) m rs = some (m', rsD) := by
        rw [seqI_append, seqI_append, seqI_append, seqI_append, hsP', Option.bind_some, hsA',
          Option.bind_some, hsB', Option.bind_some, hsC', Option.bind_some]
        exact hsD
      refine ⟨m', rsD, reach_block_jmp hb rfl hbk hkp hseq, ?_⟩
      have hRn : Rep lay (σl.schreibSlot t Λ z.n f (eval σl e σl ρ)) m' :=
        rep_store_slot hL hRl t z.n f _ hs hk0 hk1 hstD
      refine post_store hRn hE hW hstD (not_fresh_tab t) (fun r hr => ?_) (fun x hx => ?_)
      · have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hrP
        have l2 : r < r2 := Nat.lt_of_lt_of_le l1 hrA
        have l3 : r < r3 := Nat.lt_of_lt_of_le l2 hrB
        have l4 : r < r4 := Nat.lt_of_lt_of_le l3 hrC
        rw [hagD r l4, hagC r l3, hagB r l2, hagA r l1, hagP r (hc r hr)]
      · have l1 : x < r1 := Nat.lt_of_lt_of_le (hc x hx) hrP
        have l2 : x < r2 := Nat.lt_of_lt_of_le l1 hrA
        have l3 : x < r3 := Nat.lt_of_lt_of_le l2 hrB
        have l4 : x < r4 := Nat.lt_of_lt_of_le l3 hrC
        exact Nat.lt_of_lt_of_le l4 hrD
  | _, _, _, _, Gabbro.Grammatik.Stmt.assignVar (τ := τ) (Λ := Λ) x e, lb, k, st, st', blks, h, M, S, fn,
      hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      rcases hcx : cenv[varIdx x]? with _ | a
      · simp [hcx] at h
      simp only [hcx] at h
      have hs : supp τ = true := by
        cases hbb : supp τ
        · simp [hbb] at h
        · rfl
      simp only [hs, if_true] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hst : storeTo τ oe r1 (.reg a) with _ | ⟨cs, r2⟩
      · simp [hst] at h
      simp only [hst] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      simp only [execStmt, OutOk]
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
      have hs1' : seqI ce m rs = some (m, rs1) := hs1
      obtain ⟨a', b, ha', hsx, hrb, hfr, hlb⟩ := envRep_get x cenv ρ hE
      rw [hcx] at ha'
      have ha'' := Option.some.inj ha'
      subst ha''
      have hamem : a ∈ cenv := List.mem_of_getElem? hcx
      have hra : a < st.r := hc a hamem
      have hrs1 : rs1 a = rs a := hag1 a hra
      have hp1 : (Opd.reg a).ev rs1 = some (.ptr b 0) := by
        show rs1 a = _
        rw [hrs1]; exact hrb
      obtain ⟨m', rs2, hs2, hst2, hr2, hag2⟩ := storeTo_run lay τ (eval σl e σl ρ) hs oe r1 (.reg a)
        b 0 m rs1 hev1 hlt1 hp1 (opdlt_reg a r1 (Nat.lt_of_lt_of_le hra hr1)) ⟨_, hlb⟩ cs r2 hst
      have hseq : seqI (ce ++ cs) m rs = some (m', rs2) := by
        rw [seqI_append, hs1']; exact hs2
      refine ⟨m', rs2, reach_block_jmp hb rfl hbk hkp hseq, ?_⟩
      have hRn : Rep lay σl m' := rep_store_other hRl hst2 hfr
      have hag : ∀ r ∈ cenv, rs2 r = rs r := fun r hr => by
        have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hr1
        rw [hag2 r l1, hag1 r (hc r hr)]
      have hE2 := envRep_regs cenv ρ hag hE
      have hrb2 : rs2 a = some (.ptr b 0) := by rw [hag a hamem]; exact hrb
      refine ⟨hRn, envRep_set x cenv ρ (eval σl e σl ρ) a hE2 hcx hrb2 hst2, wfL_store hst2 hW, ?_⟩
      intro x hx
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hc x hx) hr1) hr2
  | _, _, _, _, .ite (Λ := Λ) c tb eb, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst,
      hR, hE, hW, hc => by
      simp only [lowerS] at h
      rcases hc1 : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
      · simp [hc1] at h
      simp only [hc1] at h
      rcases hb1 : lowerB lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ with _ | ⟨bt, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hb2 : lowerB lay cenv lv eb (st.l + 1) k s1 with _ | ⟨be, s2⟩
      · simp [hb2] at h
      simp only [hb2] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have S1 := lowerB_shape lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ s1 bt hb1
      have S2 := lowerB_shape lay cenv lv eb (st.l + 1) k s1 s2 be hb2
      have hb := hM _ (List.mem_cons_self ..)
      have hMt : InM M fn bt := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_append_left _ hb'))
      have hMe : InM M fn be := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_append_right _ hb'))
      have hKt := kok_of_shape S1 hMt
      have hKe := kok_of_shape S2 hMe
      have hm12 : s1.r ≤ s2.r := S2.2.2
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ c.orte := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fc, _⟩ := lowerE_ok lay hL c cenv st.r (cc, oc, r1) hc1 σl σl ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fc
      have hs1' : seqI cc m rs = some (m, rs1) := hs1
      have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
      have hc1' : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      have hbrT : (eval σl c σl ρ : Bool) = true →
          Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
        intro hv
        have hev : oc.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
          rw [hev1]
          show some (Val.bool (eval σl c σl ρ)) = _
          rw [hv]; rfl
        obtain ⟨bk, hbk, hkp⟩ := hKt
        have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hb rfl hs1' hev
          (by simpa using hbk) hkp
        simpa using this
      have hbrF : (eval σl c σl ρ : Bool) = false →
          Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
        intro hv
        have hev : oc.ev rs1 = some (.int 1 (0 : BitVec 1)) := by
          rw [hev1]
          show some (Val.bool (eval σl c σl ρ)) = _
          rw [hv]; rfl
        obtain ⟨bk, hbk, hkp⟩ := hKe
        have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
        have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (0 : BitVec 1)) hb rfl hs1' hev
          (by simpa [h01] using hbk) hkp
        simpa [h01] using this
      simp only [execStmt]
      try rw [← hσl]
      by_cases hv : (eval σl c σl ρ : Bool) = true
      · have hv' : Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true := hv
        rw [if_pos hv']
        exact outok_mono hm12 _ (outok_lift (hbrT hv) _ (lowerB_ok lay hL cenv lv O passes R tb st.l k
          ⟨r1, st.l + 2⟩ s1 bt hb1 M S fn hMt hk hlv σl ρ m rs1 ks dst hRl hE1 hW hc1'))
      · have hv0 : (eval σl c σl ρ : Bool) = false := Bool.eq_false_iff.mpr hv
        have hv' : ¬ (Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true) := hv
        rw [if_neg hv']
        exact outok_lift (hbrF hv0) _ (lowerB_ok lay hL cenv lv O passes R eb (st.l + 1) k s1 s2 be hb2
          M S fn hMe hk hlv σl ρ m rs1 ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1' x hx) S1.2.2))
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .onOption .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .onTag .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .onWhy .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .call .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .callInd .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .traverse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .retry .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .forever .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .axiomCall .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .regWrite .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .transition .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .publish .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .advances .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .retires .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .retWhy .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h

theorem lowerB_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerB lay cenv lv b lb k st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st' m rs ks dst (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerB, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execBlock, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, hR, hE, hW, hc⟩
  | _, _, _, _, .cons s rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE,
      hW, hc => by
      simp only [lowerB] at h
      rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
      · simp [hs] at h
      simp only [hs] at h
      rcases hr : lowerB lay cenv lv rest st.l k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have SS := lowerB_shape lay cenv lv rest st.l k s1 s2 b2 hr
      have hM1 : InM M fn b1 := fun b hb' => hM b (List.mem_append_left _ hb')
      have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_append_right _ hb')
      have hK2 := kok_of_shape SS hM2
      have IHs := lowerS_ok lay hL cenv lv O passes R s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs M S fn hM1 hK2
        hlv σ ρ m rs ks dst hR hE hW hc
      have hle : s1.r ≤ s2.r := SS.2.2
      simp only [execBlock]
      rcases hx : execStmt O passes R s σ ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1'⟩ | ⟨h1, σ1, ρ1⟩ |
        ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at IHs
        obtain ⟨m1, rs1, hr1, hP1⟩ := IHs
        obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
        simp only [hx]
        exact outok_lift hr1 _ (lowerB_ok lay hL cenv lv O passes R rest st.l k s1 s2 b2 hr M S fn
          hM2 hk hlv σ1 ρ1 m1 rs1 ks dst hRp hEp hWp hcp)
      · rw [hx] at IHs
        simp only [hx]
        exact IHs
      · simp only [hx, OutOk]
      · rw [hx] at IHs
        simp only [hx]
        exact outok_mono hle _ IHs
      · rw [hx] at IHs
        simp only [hx]
        exact outok_mono hle _ IHs
      · simp only [hx, OutOk]
      · simp only [hx, OutOk]
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) (Λ := Λ) e rest, lb, k, st, st', blks, h, M, S, fn,
      hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have SS := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr
      have hb0 := hM _ (List.mem_cons_self ..)
      have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_cons_of_mem _ hb')
      have hK2 := kok_of_shape SS hM2
      obtain ⟨bk2, hbk2, hkp2⟩ := hK2
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
      have hs1' : seqI ce m rs = some (m, rs1) := hs1
      have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      obtain ⟨m1, rs3, hs3, hRn, hEnew, hWn, hra, hr2e, hag3⟩ :=
        bindCode_run lay (eval σl e σl ρ) oe r1 m rs1 hRl hE1 hW hev1 hlt1 hc1 hb
      subst hr2e
      have hseq : seqI (ce ++ cb) m rs = some (m1, rs3) := by
        rw [seqI_append, hs1', Option.bind_some]; exact hs3
      have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hb0 rfl hbk2 hkp2 hseq
      have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') hra)
      have IHr := lowerB_ok lay hL (a :: cenv) lv O passes R rest st.l k ⟨a + 1, st.l + 1⟩ s2 b2 hr M S fn
        hM2 hk hlv σl (Env.cons (eval σl e σl ρ) ρ) m1 rs3 ks dst hRn hEnew hWn hbound
      simp only [execBlock]
      try rw [← hσl]
      exact outok_schrumpf _ (outok_lift hreach _ IHr)
  | _, _, _, _, .check (Λ := Λ) c sonst rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs,
      ks, dst, hR, hE, hW, hc => by
      simp only [lowerB] at h
      rcases hc1 : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
      · simp [hc1] at h
      simp only [hc1] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ with _ | ⟨be, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hb2 : lowerB lay cenv lv rest (st.l + 1) k s1 with _ | ⟨br, s2⟩
      · simp [hb2] at h
      simp only [hb2] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ s1 be hb1
      have S2 := lowerB_shape lay cenv lv rest (st.l + 1) k s1 s2 br hb2
      have hb := hM _ (List.mem_cons_self ..)
      have hMe : InM M fn be := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_append_left _ hb'))
      have hMr : InM M fn br := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_append_right _ hb'))
      have hKe := kok_of_shape S1 hMe
      have hKr := kok_of_shape S2 hMr
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ c.orte := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fc, _⟩ := lowerE_ok lay hL c cenv st.r (cc, oc, r1) hc1 σl σl ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fc
      have hs1' : seqI cc m rs = some (m, rs1) := hs1
      have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
      have hc1' : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      have hbrT : (eval σl c σl ρ : Bool) = true →
          Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
        intro hv
        have hev : oc.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
          rw [hev1]
          show some (Val.bool (eval σl c σl ρ)) = _
          rw [hv]; rfl
        obtain ⟨bk, hbk, hkp⟩ := hKr
        have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hb rfl hs1' hev
          (by simpa using hbk) hkp
        simpa using this
      have hbrF : (eval σl c σl ρ : Bool) = false →
          Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
        intro hv
        have hev : oc.ev rs1 = some (.int 1 (0 : BitVec 1)) := by
          rw [hev1]
          show some (Val.bool (eval σl c σl ρ)) = _
          rw [hv]; rfl
        obtain ⟨bk, hbk, hkp⟩ := hKe
        have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
        have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (0 : BitVec 1)) hb rfl hs1' hev
          (by simpa [h01] using hbk) hkp
        simpa [h01] using this
      simp only [execBlock]
      try rw [← hσl]
      by_cases hv : (eval σl c σl ρ : Bool) = true
      · have hv' : Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true := hv
        rw [if_pos hv']
        exact outok_lift (hbrT hv) _ (lowerB_ok lay hL cenv lv O passes R rest (st.l + 1) k s1 s2 br hb2
          M S fn hMr hk hlv σl ρ m rs1 ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1' x hx) S1.2.2))
      · have hv0 : (eval σl c σl ρ : Bool) = false := Bool.eq_false_iff.mpr hv
        have hv' : ¬ (Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true) := hv
        rw [if_neg hv']
        exact outok_mono S2.2.2 _ (outok_lift (hbrF hv0) _ (outok_of_endok _
          (lowerEnd_ok lay hL cenv lv O passes R sonst st.l ⟨r1, st.l + 2⟩ s1 be hb1 M S fn hMe hlv σl ρ m rs1
            ks dst hRl hE1 hW hc1')))
  | _, _, _, _, .bindCall .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindCallInd .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindCallElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiom .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiomElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .regRead .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .regReadElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .awaits .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .exchange .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .narrow .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .float .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .floatLit .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .floatOf .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .floatNarrow .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h

theorem lowerEnd_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Gabbro.Grammatik.Endblock D V l Γ Λ)
      (lb : Lbl) (st st' : St) (blks : List Block),
      lowerEnd lay cenv lv e lb st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → LvOk M fn lv →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        EndOk lay cenv lv M S fn lb st' m rs ks dst (execEnd O passes R e σ ρ)
  | _, _, _, .ret (Λ := Λ) e _, lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerEnd] at h
      simp only [execEnd, EndOk]
      obtain ⟨f', hr, hf1, hf2, hret⟩ := lowerErg_ok lay hL cenv e lb st st' blks h M S fn hM
        (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
      exact ⟨m, f', hr, hf1, hf2, hret, hR, hW⟩
  | _, _, _, .leave .., lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execEnd, EndOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.1
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, hR, hE, hW, hc⟩
  | _, _, _, .next .., lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execEnd, EndOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.2
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, hR, hE, hW, hc⟩
  | _, _, _, .cons s rest, lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerEnd] at h
      rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
      · simp [hs] at h
      simp only [hs] at h
      rcases hr : lowerEnd lay cenv lv rest st.l s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have SS := lowerEnd_shape lay cenv lv rest st.l s1 s2 b2 hr
      have hM1 : InM M fn b1 := fun b hb' => hM b (List.mem_append_left _ hb')
      have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_append_right _ hb')
      have hK2 := kok_of_shape SS hM2
      have IHs := lowerS_ok lay hL cenv lv O passes R s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs M S fn hM1 hK2
        hlv σ ρ m rs ks dst hR hE hW hc
      have hle : s1.r ≤ s2.r := SS.2.2
      simp only [execEnd]
      rcases hx : execStmt O passes R s σ ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1'⟩ | ⟨h1, σ1, ρ1⟩ |
        ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at IHs
        obtain ⟨m1, rs1, hr1, hP1⟩ := IHs
        obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
        simp only [hx]
        exact endok_lift hr1 _ (lowerEnd_ok lay hL cenv lv O passes R rest st.l s1 s2 b2 hr M S fn hM2 hlv
          σ1 ρ1 m1 rs1 ks dst hRp hEp hWp hcp)
      · rw [hx] at IHs
        simp only [hx]
        exact IHs
      · simp only [hx, EndOk]
      · rw [hx] at IHs
        simp only [hx]
        exact runOk_mono hle IHs
      · rw [hx] at IHs
        simp only [hx]
        exact runOk_mono hle IHs
      · simp only [hx, EndOk]
      · simp only [hx, EndOk]
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) (Λ := Λ) e rest, lb, st, st', blks, h, M, S, fn, hM, hlv,
      σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr : lowerEnd lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      simp only [hr] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have SS := lowerEnd_shape lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ s2 b2 hr
      have hb0 := hM _ (List.mem_cons_self ..)
      have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_cons_of_mem _ hb')
      have hK2 := kok_of_shape SS hM2
      obtain ⟨bk2, hbk2, hkp2⟩ := hK2
      obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
      try rw [← hσl]
      have hRl : Rep lay σl m := by rw [hσl]; exact hR
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
      have hs1' : seqI ce m rs = some (m, rs1) := hs1
      have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      obtain ⟨m1, rs3, hs3, hRn, hEnew, hWn, hra, hr2e, hag3⟩ :=
        bindCode_run lay (eval σl e σl ρ) oe r1 m rs1 hRl hE1 hW hev1 hlt1 hc1 hb
      subst hr2e
      have hseq : seqI (ce ++ cb) m rs = some (m1, rs3) := by
        rw [seqI_append, hs1', Option.bind_some]; exact hs3
      have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hb0 rfl hbk2 hkp2 hseq
      have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') hra)
      have IHr := lowerEnd_ok lay hL (a :: cenv) lv O passes R rest st.l ⟨a + 1, st.l + 1⟩ s2 b2 hr M S fn
        hM2 hlv σl (Env.cons (eval σl e σl ρ) ρ) m1 rs3 ks dst hRn hEnew hWn hbound
      simp only [execEnd]
      try rw [← hσl]
      exact endok_schrumpf _ (endok_lift hreach _ IHr)
  | _, _, _, .retWhy .., lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerEnd] at h
  | _, _, _, .bindAxiom .., lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerEnd] at h
  | _, _, _, .bindAxiomElse .., lb, st, st', blks, h, M, S, fn, hM, hlv, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerEnd] at h

end

end Gabbro.Code.Lower
