import Grammatik.Code.Refine.Stmt
import Grammatik.Code.Refine.Loop
import Grammatik.Code.Refine.Traverse
import Grammatik.Code.Refine.Retry
import Grammatik.Code.Refine.CallRun
import Grammatik.Code.Refine.Match.OnOption
import Grammatik.Code.Refine.Match.Why
import Grammatik.Code.Refine.Match.Tag

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
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)

variable {D : Deklaration} {V : Vertrag D}

mutual

theorem lowerS_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerS lay cenv lv s lb k st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R s σ ρ)
  | _, _, _, _, .assignGlob (Λ := Λ) g e _ _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs,
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
      have hFr : Fr lay cenv st.r m rs m' rs2 := fr_store hst2 (Or.inl (not_fresh_glob g)) (fun x hx => by
        rw [hag2 x (Nat.lt_of_lt_of_le hx hr1), hag1 x hx])
      refine ⟨m', rs2, reach_block_jmp hb rfl hbk hkp hseq, ?_, hFr⟩
      have hRn : Rep lay (σl.schreibGlob g Λ (eval σl e σl ρ)) m' :=
        rep_store_glob hL hRl g _ hs hst2
      refine post_store hRn hE hW hst2 (not_fresh_glob g) (fun r hr => ?_) (fun x hx => ?_)
      · have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hr1
        rw [hag2 r l1, hag1 r (hc r hr)]
      · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hc x hx) hr1) hr2
  | _, _, _, _, .ret (Λ := Λ) e _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR,
      hE, hW, hc => by
      simp only [lowerS] at h
      simp only [execStmt, OutOk]
      obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerRet_ok lay hL cenv V.gruende e lb st st' blks h M S fn hM
        (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
      exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩
  | _, _, _, _, .leave .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.1
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, _, .next .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.2
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, _, .assignSlot (Λ := Λ) t f i e _ _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs,
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
      have hFr : Fr lay cenv st.r m rs m' rsD := fr_store hstD (Or.inl (not_fresh_tab t)) (fun x hx => by
        have l1 : x < r1 := Nat.lt_of_lt_of_le hx hrA
        have l2 : x < r2 := Nat.lt_of_lt_of_le l1 hrB
        have l3 : x < r3 := Nat.lt_of_lt_of_le l2 hrC
        rw [hagD x l3, hagC x l2, hagB x l1, hagA x hx])
      refine ⟨m', rsD, reach_block_jmp hb rfl hbk hkp hseq, ?_, hFr⟩
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
  | _, _, _, _, .assignThru (Λ := Λ) p t ht f i e _ _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m,
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
      have hFr : Fr lay cenv st.r m rs m' rsD := fr_store hstD (Or.inl (not_fresh_tab t)) (fun x hx => by
        have l1 : x < r1 := Nat.lt_of_lt_of_le hx hrP
        have l2 : x < r2 := Nat.lt_of_lt_of_le l1 hrA
        have l3 : x < r3 := Nat.lt_of_lt_of_le l2 hrB
        have l4 : x < r4 := Nat.lt_of_lt_of_le l3 hrC
        rw [hagD x l4, hagC x l3, hagB x l2, hagA x l1, hagP x hx])
      refine ⟨m', rsD, reach_block_jmp hb rfl hbk hkp hseq, ?_, hFr⟩
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
      hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
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
      have hFr : Fr lay cenv st.r m rs m' rs2 := fr_store hst2 (Or.inr ⟨a, hamem, hrb⟩) (fun x hx => by
        rw [hag2 x (Nat.lt_of_lt_of_le hx hr1), hag1 x hx])
      refine ⟨m', rs2, reach_block_jmp hb rfl hbk hkp hseq, ?_, hFr⟩
      have hRn : Rep lay σl m' := rep_store_other hRl hst2 hfr
      have hag : ∀ r ∈ cenv, rs2 r = rs r := fun r hr => by
        have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hr1
        rw [hag2 r l1, hag1 r (hc r hr)]
      have hE2 := envRep_regs cenv ρ hag hE
      have hrb2 : rs2 a = some (.ptr b 0) := by rw [hag a hamem]; exact hrb
      refine ⟨hRn, envRep_set x cenv ρ (eval σl e σl ρ) a hE2 hcx hrb2 hst2, wfL_store hst2 hW, ?_⟩
      intro x hx
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hc x hx) hr1) hr2
  | _, _, _, _, .ite (Λ := Λ) c tb eb, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst,
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
        exact outok_mono hm12 _ (outok_lift (hbrT hv) (fr_regs hag1) hr1 hc _ (lowerB_ok lay hL cenv lv O passes R tb st.l k
          ⟨r1, st.l + 2⟩ s1 bt hb1 M S fn hMt hk hlv hFn hCall σl ρ m rs1 ks dst hRl hE1 hW hc1'))
      · have hv0 : (eval σl c σl ρ : Bool) = false := Bool.eq_false_iff.mpr hv
        have hv' : ¬ (Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true) := hv
        rw [if_neg hv']
        exact outok_lift (hbrF hv0) (fr_regs hag1) (Nat.le_trans hr1 S1.2.2) hc _
          (lowerB_ok lay hL cenv lv O passes R eb (st.l + 1) k s1 s2 be hb2
          M S fn hMe hk hlv hFn hCall σl ρ m rs1 ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1' x hx) S1.2.2))
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .onOption o p a, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      onOption_ok lay hL cenv lv O passes R o p a
        (fun c lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn' hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc' =>
          lowerB_ok lay hL (c :: cenv) lv O passes R p lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn'
            hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc')
        (fun lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn' hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc' =>
          lowerB_ok lay hL cenv lv O passes R a lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn'
            hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc')
        lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  | _, _, _, _, .onTag v arms, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      onTag_ok lay hL cenv lv O passes R v arms (lowerAr_ok lay hL cenv lv O passes R arms) lb k st st' blks h M S fn
        hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  | _, _, _, _, .onWhy r arms, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      onWhy_ok lay hL cenv lv O passes R r arms (lowerGA_ok lay hL cenv lv O passes R arms) lb k st st' blks h M S fn
        hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  | _, _, _, _, .call (Λ := Λ) f args _ hr, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs,
      ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp [hla] at h
      simp only [hla, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      have hRl : Rep lay (σ.lese Λ args.orte) m := hR
      obtain ⟨rs1, hs1, hr1, hag1, hmap⟩ := lowerArgs_ok lay hL cenv args st.r (ca, ops, r1) hla
        (σ.lese Λ args.orte) (σ.lese Λ args.orte) ρ m rs hRl hE hc
      have hs1' : seqI ca m rs = some (m, rs1) := hs1
      simp only [execStmt]
      rcases hRf : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        ⟨σ', v⟩ | ⟨σ', r⟩ | e | e
      · simp only [OutOk]
        obtain ⟨m', hreach, hRn, hWn, hK⟩ := call_run_none hFn hCall hRf hb (pre := ca) (post := []) (ks := ks) (dst := dst) rfl hs1'
          hmap hRl hW
        have hjmp := reach_jmp (S := S) (m := m') (ks := ks)
          (f := ⟨fn, lb, ca.length + 1, rs1, dst⟩) (l := k) (blk := ⟨lb, [], ca ++ [.call none (lay.fno f) ops], .jmp k⟩)
          ⟨hb, by simp, rfl⟩ hbk hkp
        have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
        have hEm : EnvRep lay rs1 m' cenv ρ := envRep_load cenv ρ
          (fun r hr' b hb' hf o t w hl => hK.2 b hf (envRep_blocks_lt hW.1 cenv ρ hE1 r hr' b hb') o t w hl) hE1
        exact ⟨m', rs1, Reach.trans hreach hjmp, ⟨hRn, hEm, hWn, fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1⟩,
          fun x hx => hag1 x hx, hK.1, fun b hf hb' _ o t w hl => hK.2 b hf hb' o t w hl⟩
      · exact (Fin.cast hr r).elim0
      · simp only [OutOk]
      · simp only [OutOk]
  | _, _, _, _, .callInd .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .traverse (Λ := Λ) t inv body, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks,
      dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      by_cases hcn : 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128
      · simp only [hcn, and_self, if_true] at h
        rcases hv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg st.r) (st.r + 1) with
          _ | ⟨cv, ov, r1⟩
        · simp [hv] at h
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (D.count t - 1)) ov r1 with _ | ⟨cb, a, r2⟩
        · simp [hb] at h
        simp only [hb] at h
        rcases hb2 : lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ with
          _ | ⟨bb, s1⟩
        · simp [hb2] at h
        simp only [hb2] at h
        have h' := Option.some.inj h
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        have S2 := lowerB_shape lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb hb2
        have hM0 : M.blk fn lb = some ⟨lb, [], [.bin st.r .add (Ar.wid 0 (D.count t))
            (.int (Ar.wid 0 (D.count t)) 0) (.int (Ar.wid 0 (D.count t)) 0)], .jmp st.l⟩ :=
          hM _ (List.mem_cons_self ..)
        have hMH : M.blk fn st.l = some ⟨st.l, [], [], .brc .ult (Ar.wid 0 (D.count t)) (.reg st.r)
            (.int (Ar.wid 0 (D.count t)) (D.count t)) (st.l + 1) k⟩ :=
          hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hMB : M.blk fn (st.l + 1) = some ⟨st.l + 1, [], cv ++ cb, .jmp (st.l + 3)⟩ :=
          hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        have hMI : M.blk fn (st.l + 2) = some ⟨st.l + 2, [], [.bin st.r .add (Ar.wid 0 (D.count t))
            (.reg st.r) (.int (Ar.wid 0 (D.count t)) 1)], .jmp st.l⟩ :=
          hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        have hMbb : InM M fn bb := fun b hb' =>
          hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hb'))))
        have hKbd := kok_of_shape S2 hMbb
        have hKI : KOk M fn (st.l + 2) := ⟨_, hMI, rfl⟩
        have hKH : KOk M fn st.l := ⟨_, hMH, rfl⟩
        simp only [execStmt]
        -- the counter starts at zero
        have hinit : seqI [Instr.bin st.r .add (Ar.wid 0 (D.count t)) (.int (Ar.wid 0 (D.count t)) 0)
            (.int (Ar.wid 0 (D.count t)) 0)] m rs
            = some (m, rs.set st.r (Val.ofInt (Ar.wid 0 (D.count t)) ((0 : Nat) : Int))) := by
          simp [seqI, stepI, Opd.ev, val_bin_add]
        obtain ⟨bkh, hbkh, hkph⟩ := hKH
        have hI0 := reach_block_jmp (S := S) (ks := ks) (dst := dst) hM0 rfl hbkh hkph hinit
        have hmap : (alleIndizes (D.count t)).map (·.n) =
            (List.range' 0 ((D.count t).toNat - 0)).map (fun k : Nat => (k : Int)) := by
          rw [alleIndizes_map, Nat.sub_zero, ← List.range_eq_range']
        have hE0 := envRep_regs (rs' := rs.set st.r (Val.ofInt (Ar.wid 0 (D.count t)) ((0 : Nat) : Int))) cenv ρ
          (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt (hc x hx))) hE
        exact outok_lift hI0 (fr_regs (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt hx))) (Nat.le_refl _) hc _
          (traverse_loop (lay := lay) (lv := lv) (O := O) (passes := passes) (R := R) t inv body
            (c := st.r) (H := st.l) (Bl := st.l + 1) (I := st.l + 2) (Bd := st.l + 3) (cv := cv) (cb := cb)
            (ov := ov) (a := a) (r1 := r1) (r2 := r2) (r' := s1.r) hcn.1 hcn.2 hv hb S2.2.2 hMH hMB hMI hk hKbd
            (fun σ ρ' m rs hR hE hW hc => lowerB_ok lay hL (a :: cenv) (k, st.l + 2) O passes R body (st.l + 3)
              (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb hb2 M S fn hMbb hKI ⟨hk, hKI⟩ hFn hCall σ ρ' m rs ks dst hR hE hW hc)
            (alleIndizes (D.count t)) 0 hmap (Nat.zero_le _) σ ρ m
            (rs.set st.r (Val.ofInt (Ar.wid 0 (D.count t)) ((0 : Nat) : Int))) hR hE0 hW hc (regs_set_same _ _ _))
      · simp [hcn] at h
  | _, _, _, _, .retry (Λ := Λ) n bis body ueb, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m,
      rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      by_cases hcn : retryOk n = true
      · simp only [hcn, if_true] at h
        rcases hcb : lowerE lay cenv bis (st.r + 1) with _ | ⟨cb, ob, r1⟩
        · simp [hcb] at h
        simp only [hcb] at h
        rcases hb1 : lowerB lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ with _ | ⟨bb, s1⟩
        · simp [hb1] at h
        simp only [hb1] at h
        rcases hb2 : lowerB lay cenv lv ueb (st.l + 2) k s1 with _ | ⟨bo, s2⟩
        · simp [hb2] at h
        simp only [hb2] at h
        have h' := Option.some.inj h
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        have S1 := lowerB_shape lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb hb1
        have S2 := lowerB_shape lay cenv lv ueb (st.l + 2) k s1 s2 bo hb2
        have hM0 : M.blk fn lb = some ⟨lb, [], [.bin st.r .add (Ar.wid 0 (n : Int))
            (.int (Ar.wid 0 (n : Int)) 0) (.int (Ar.wid 0 (n : Int)) 0)], .jmp st.l⟩ :=
          hM _ (List.mem_cons_self ..)
        have hMH : M.blk fn st.l = some ⟨st.l, [], cb, .br ob k (st.l + 1)⟩ :=
          hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hMT : M.blk fn (st.l + 1) = some ⟨st.l + 1, [], [], .brc .ult (Ar.wid 0 (n : Int)) (.reg st.r)
            (.int (Ar.wid 0 (n : Int)) (n : Int)) (st.l + 4) (st.l + 2)⟩ :=
          hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        have hMI : M.blk fn (st.l + 3) = some ⟨st.l + 3, [], [.bin st.r .add (Ar.wid 0 (n : Int))
            (.reg st.r) (.int (Ar.wid 0 (n : Int)) 1)], .jmp st.l⟩ :=
          hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
        have hMbb : InM M fn bb := fun b hb' => hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb')))))
        have hMbo : InM M fn bo := fun b hb' => hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb')))))
        have hKbd := kok_of_shape S1 hMbb
        have hKov := kok_of_shape S2 hMbo
        have hKI : KOk M fn (st.l + 3) := ⟨_, hMI, rfl⟩
        have hKH : KOk M fn st.l := ⟨_, hMH, rfl⟩
        simp only [execStmt]
        have hinit : seqI [Instr.bin st.r .add (Ar.wid 0 (n : Int)) (.int (Ar.wid 0 (n : Int)) 0)
            (.int (Ar.wid 0 (n : Int)) 0)] m rs
            = some (m, rs.set st.r (Val.ofInt (Ar.wid 0 (n : Int)) ((0 : Nat) : Int))) := by
          simp [seqI, stepI, Opd.ev, val_bin_add]
        obtain ⟨bkh, hbkh, hkph⟩ := hKH
        have hI0 := reach_block_jmp (S := S) (ks := ks) (dst := dst) hM0 rfl hbkh hkph hinit
        have hE0 := envRep_regs (rs' := rs.set st.r (Val.ofInt (Ar.wid 0 (n : Int)) ((0 : Nat) : Int))) cenv ρ
          (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt (hc x hx))) hE
        exact outok_lift hI0 (fr_regs (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt hx))) (Nat.le_refl _) hc _
          (retry_loop (lay := lay) hL (lv := lv) (O := O) (passes := passes) (R := R) (cenv := cenv) n bis body ueb
            (c := st.r) (H := st.l) (T := st.l + 1) (OV := st.l + 2) (I := st.l + 3) (BD := st.l + 4)
            (cb := cb) (ob := ob) (r1 := r1) (rb := s1.r) (ro := s2.r) (retryOk_fits hcn) hcb S1.2.2 S2.2.2
            hMH hMT hMI hk hKbd hKov
            (fun σ ρ m rs hR hE hW hc => lowerB_ok lay hL cenv (k, st.l + 3) O passes R body (st.l + 4)
              (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb hb1 M S fn hMbb hKI ⟨hk, hKI⟩ hFn hCall σ ρ m rs ks dst hR hE hW hc)
            (fun σ ρ m rs hR hE hW hc => lowerB_ok lay hL cenv lv O passes R ueb (st.l + 2) k s1 s2 bo hb2
              M S fn hMbo hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc)
            n 0 (by omega) σ ρ m (rs.set st.r (Val.ofInt (Ar.wid 0 (n : Int)) ((0 : Nat) : Int))) hR hE0 hW hc
            (regs_set_same _ _ _))
      · simp [hcn] at h
  | _, _, _, _, .forever (Λ := Λ) a inv body, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks,
      dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      have hKl := kok_of_shape (lowerB_shape lay cenv (k, lb) body lb lb st st' blks h) hM
      simp only [execStmt]
      exact forever_ok a inv body (fun σ ρ m rs hR hE hW hc => lowerB_ok lay hL cenv (k, lb) O passes R body lb lb
        st st' blks h M S fn hM hKl ⟨hk, hKl⟩ hFn hCall σ ρ m rs ks dst hR hE hW hc) passes σ ρ m rs hR hE hW hc
  | _, _, _, _, .axiomCall .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .regWrite .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .transition .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .publish .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .advances .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .retires .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerS] at h
  | _, _, _, _, .retWhy r _, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS] at h
      simp only [execStmt, OutOk]
      obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerWhy_ok lay cenv V.gruende V.erg r.val lb st st' blks h M S fn hM
        m rs ks dst
      exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩

theorem lowerB_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerB lay cenv lv b lb k st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerB, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execBlock, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hk
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, _, .cons s rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE,
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
        hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
      have hle : s1.r ≤ s2.r := SS.2.2
      have S0 := lowerS_shape lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
      simp only [execBlock]
      rcases hx : execStmt O passes R s σ ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1'⟩ | ⟨h1, σ1, ρ1⟩ |
        ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at IHs
        obtain ⟨m1, rs1, hr1, hP1, hF1⟩ := IHs
        obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
        simp only [hx]
        exact outok_lift hr1 hF1 S0.2.2 hc _ (lowerB_ok lay hL cenv lv O passes R rest st.l k s1 s2 b2 hr M S fn
          hM2 hk hlv hFn hCall σ1 ρ1 m1 rs1 ks dst hRp hEp hWp hcp)
      · rw [hx] at IHs
        simp only [hx]
        exact IHs
      · rw [hx] at IHs
        simp only [hx]
        exact IHs
      · rw [hx] at IHs
        simp only [hx]
        exact outok_mono hle _ IHs
      · rw [hx] at IHs
        simp only [hx]
        exact outok_mono hle _ IHs
      · simp only [hx, OutOk]
      · simp only [hx, OutOk]
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) (Λ := Λ) e rest, lb, k, st, st', blks, h, M, S, fn,
      hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
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
      obtain ⟨m1, rs3, hs3, hRn, hEnew, hWn, hra, hr2e, hag3, hFb, hcell⟩ :=
        bindCode_run lay (eval σl e σl ρ) oe r1 m rs1 hRl hE1 hW hev1 hlt1 hc1 hb
      subst hr2e
      have hFbind : Fr lay cenv st.r m rs m1 rs3 := fr_trans (fr_regs hag1) hFb hr1 hc
      have hseq : seqI (ce ++ cb) m rs = some (m1, rs3) := by
        rw [seqI_append, hs1', Option.bind_some]; exact hs3
      have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hb0 rfl hbk2 hkp2 hseq
      have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') hra)
      have IHr := lowerB_ok lay hL (a :: cenv) lv O passes R rest st.l k ⟨a + 1, st.l + 1⟩ s2 b2 hr M S fn
        hM2 hk hlv hFn hCall σl (Env.cons (eval σl e σl ρ) ρ) m1 rs3 ks dst hRn hEnew hWn hbound
      simp only [execBlock]
      try rw [← hσl]
      exact outok_bind hreach hFbind hcell hc (Nat.le_succ_of_le (Nat.le_trans hr1 hra)) _ IHr
  | _, _, _, _, .check (Λ := Λ) c sonst rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs,
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
        exact outok_lift (hbrT hv) (fr_regs hag1) (Nat.le_trans hr1 S1.2.2) hc _
          (lowerB_ok lay hL cenv lv O passes R rest (st.l + 1) k s1 s2 br hb2
          M S fn hMr hk hlv hFn hCall σl ρ m rs1 ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1' x hx) S1.2.2))
      · have hv0 : (eval σl c σl ρ : Bool) = false := Bool.eq_false_iff.mpr hv
        have hv' : ¬ (Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true) := hv
        rw [if_neg hv']
        exact outok_mono S2.2.2 _ (outok_lift (hbrF hv0) (fr_regs hag1) hr1 hc _ (outok_of_endok _
          (lowerEnd_ok lay hL cenv lv O passes R sonst st.l ⟨r1, st.l + 2⟩ s1 be hb1 M S fn hMe hlv hFn hCall σl ρ m rs1
            ks dst hRl hE1 hW hc1')))
  | _, _, _, _, Gabbro.Grammatik.Block.bindCall (τ := τ) (Λ := Λ) f args he _ hr rest, lb, k, st, st', blks, h, M, S,
      fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp [hla] at h
      simp only [hla] at h
      rcases hb : bindCode τ (.reg r1) (r1 + 1) with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hr' : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr'] at h
      simp only [hr'] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hm1 := lowerArgs_mono lay cenv args st.r _ hla
      have SS := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr'
      have hb0 := hM _ (List.mem_cons_self ..)
      have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_cons_of_mem _ hb')
      obtain ⟨bk2, hbk2, hkp2⟩ := kok_of_shape SS hM2
      have hRl : Rep lay (σ.lese Λ args.orte) m := hR
      obtain ⟨rs1, hs1, hr1, hag1, hmap⟩ := lowerArgs_ok lay hL cenv args st.r (ca, ops, r1) hla
        (σ.lese Λ args.orte) (σ.lese Λ args.orte) ρ m rs hRl hE hc
      have hs1' : seqI ca m rs = some (m, rs1) := hs1
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      simp only [execBlock]
      rcases hRf : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        ⟨σ', v⟩ | ⟨σ', r⟩ | e | e
      · simp only [hRf]
        have hw : retImg lay (D.gruende f) (D.erg f) v = some (encR lay τ (ergWert he v)) := by
          unfold retImg
          rw [if_pos hr]
          exact ergImg_ergWert lay he v
        obtain ⟨m', hreach, hRn, hWn, hK⟩ := call_run_some hFn hCall hRf hb0 (pre := ca) (post := cb) (r := r1) (ks := ks) (dst := dst)
          (by simp) hw hs1' hmap hRl hW
        -- the cells of the locals survive the call
        have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
        have hEm : EnvRep lay rs1 m' cenv ρ := envRep_load cenv ρ
          (fun r hr' b hb' hf o t w hl => hK.2 b hf (envRep_blocks_lt hW.1 cenv ρ hE1 r hr' b hb') o t w hl) hE1
        have hag2 : ∀ x ∈ cenv, (rs1.set r1 (encR lay τ (ergWert he v))) x = rs1 x := fun x hx =>
          regs_set_ne rs1 r1 x _ (Nat.ne_of_lt (hc1 x hx))
        have hEs := envRep_regs (rs' := rs1.set r1 (encR lay τ (ergWert he v))) cenv ρ hag2 hEm
        obtain ⟨m1, rs4, hs4, hRn', hEnew, hWn', hra, hr2e, hag4, hFb, hcell⟩ :=
          bindCode_run lay (ergWert he v) (.reg r1) (r1 + 1) m' (rs1.set r1 (encR lay τ (ergWert he v))) hRn hEs hWn
            (by simp [Opd.ev, regs_set_same]) (opdlt_reg r1 (r1 + 1) (Nat.lt_succ_self _))
            (fun x hx => Nat.lt_succ_of_lt (hc1 x hx)) hb
        subst hr2e
        -- the rest of the block: `cb`, then the jump
        have hstr : Stretch M fn lb (ca.length + 1) cb := ⟨_, hb0, fun i hi => by
          show (ca ++ [Instr.call (some r1) (lay.fno f) ops] ++ cb)[ca.length + 1 + i]? = some cb[i]
          rw [List.append_assoc, List.getElem?_append_right (by omega)]
          simp [show ca.length + 1 + i - ca.length = i + 1 by omega, List.getElem?_eq_getElem hi]⟩
        have hseqb := reach_seq M S cb m'
          ⟨fn, lb, ca.length + 1, rs1.set r1 (encR lay τ (ergWert he v)), dst⟩ ks m1 rs4 hstr hs4
        have hjmp := reach_jmp (S := S) (m := m1) (ks := ks)
          (f := ⟨fn, lb, ca.length + 1 + cb.length, rs4, dst⟩) (l := st.l)
          (blk := ⟨lb, [], ca ++ [.call (some r1) (lay.fno f) ops] ++ cb, .jmp st.l⟩)
          ⟨hb0, by simp; omega, rfl⟩ hbk2 hkp2
        have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') (Nat.le_trans (Nat.le_succ _) hra))
        have IHr := lowerB_ok lay hL (a :: cenv) lv O passes R rest st.l k ⟨a + 1, st.l + 1⟩ s2 b2 hr' M S fn
          hM2 hk hlv hFn hCall σ'
          (Env.cons (ergWert he v) ρ) m1 rs4 ks dst hRn' hEnew hWn' hbound
        have hFa : Fr lay cenv st.r m rs m' rs1 := ⟨fun x hx => hag1 x hx, hK.1,
          fun b hf hb' _ o t w hl => hK.2 b hf hb' o t w hl⟩
        have hFs : Fr lay cenv st.r m' rs1 m' (rs1.set r1 (encR lay τ (ergWert he v))) :=
          fr_regs (fun x hx => regs_set_ne rs1 r1 x _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx hr1)))
        have hFtot : Fr lay cenv st.r m rs m1 rs4 :=
          fr_trans hFa (fr_trans hFs (hFb) (Nat.le_succ_of_le hr1) hc) (Nat.le_refl _) hc
        have hcell' : ∀ b, rs4 a = some (.ptr b 0) → m.next ≤ b := fun b hb' => Nat.le_trans hK.1 (hcell b hb')
        have hreach2 : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, st.l, 0, rs4, dst⟩ ks) := by
          have := Reach.trans hreach (Reach.trans hseqb hjmp)
          simpa using this
        exact outok_bind hreach2 hFtot hcell' hc (Nat.le_succ_of_le (Nat.le_trans hr1 (Nat.le_trans (Nat.le_succ _) hra)))
          _ IHr
      · exact (Fin.cast hr r).elim0
      · simp only [OutOk]
      · simp only [OutOk]
  | _, _, _, _, .bindCallInd .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindCallElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiom .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiomElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .regRead .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .regReadElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .awaits .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .exchange .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' sonst rest, lb, k, st,
      st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB] at h
      rcases hcd : lowerE lay cenv (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
          (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi')))
          st.r with _ | ⟨cc, oc, r1⟩
      · simp [hcd] at h
      simp only [hcd] at h
      rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
      · simp [he] at h
      simp only [he] at h
      rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
      · simp [hv] at h
      simp only [hv] at h
      rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
      · simp [hb] at h
      simp only [hb] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ with _ | ⟨be, s1⟩
      · simp [hb1] at h
      simp only [hb1] at h
      rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k s1 with _ | ⟨br, s2⟩
      · simp [hb2] at h
      simp only [hb2] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have m1 := lowerE_mono lay cenv _ st.r _ hcd
      have m2 := lowerE_mono lay cenv e r1 _ he
      have m3 := cvtG_mono hv
      have m4 := bindCode_mono hb
      have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ s1 be hb1
      have S2 := lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k s1 s2 br hb2
      have hb0 := hM _ (List.mem_cons_self ..)
      have hbb := hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hMe : InM M fn be := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb')))
      have hMr : InM M fn br := fun b hb' =>
        hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb')))
      have hKe := kok_of_shape S1 hMe
      have hKr := kok_of_shape S2 hMr
      have hle14 : r1 ≤ r4 := by
        have a2 := m2
        have a3 := m3
        have a4 := m4
        simp only at a2 a3 a4
        omega
      have hRl : Rep lay (σ.lese Λ e.orte) m := hR
      simp only [execBlock]
      -- the test
      obtain ⟨Fc, _⟩ := lowerE_ok lay hL _ cenv st.r (cc, oc, r1) hcd (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs hRl hE hc
      obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fc
      have hs1' : seqI cc m rs = some (m, rs1) := hs1
      have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      have hcond : (eval (σ.lese Λ e.orte) (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
          (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi'))) (σ.lese Λ e.orte) ρ : Bool)
          = (decide (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) && decide ((eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) := by
        first | rfl | simp [eval, Gabbro.Grammatik.wahr?]
      by_cases hn : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
      · rw [dif_pos hn]
        -- the test succeeds: run the bind block
        have hT : (eval (σ.lese Λ e.orte) (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
            (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi'))) (σ.lese Λ e.orte) ρ : Bool)
            = true := by
          rw [hcond, decide_eq_true hn.1, decide_eq_true hn.2]; rfl
        have hev : oc.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
          rw [hT] at hev1; exact hev1
        obtain ⟨bkb, hbkb, hkpb⟩ : ∃ bk, M.blk fn (st.l + 1) = some bk ∧ bk.phis = [] := ⟨_, hbb, rfl⟩
        have hbr0 := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hb0 rfl hs1' hev
          (by simpa using hbkb) hkpb
        have hbr : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
          simpa using hbr0
        -- the value, moved to the new type
        obtain ⟨Fe, hfe⟩ := lowerE_ok lay hL e cenv r1 (ce, oe, r2) he (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs1 hRl hE1 hc1
        obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := Fe
        have hs2' : seqI ce m rs1 = some (m, rs2) := hs2
        have hE2 := envRep_regs cenv ρ (fun x hx => hag2 x (hc1 x hx)) hE1
        have hc2 : ∀ x ∈ cenv, x < r2 := fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hr2
        obtain ⟨cV, hcV, FV⟩ := cvtG_frag (lb := lo') (hb := hi') (m := m) (rs := rs2) (z := (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n)
          (hfe lo hi rfl) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).lo_le (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).le_hi hev2 hlt2
        rw [hv] at hcV
        have hcV' := Option.some.inj hcV
        subst hcV'
        obtain ⟨rs3, hs3, hr3, hag3, hlt3, hev3⟩ := FV
        have hs3' : seqI cv m rs2 = some (m, rs3) := hs3
        have hE3 := envRep_regs cenv ρ (fun x hx => hag3 x (hc2 x hx)) hE2
        have hc3 : ∀ x ∈ cenv, x < r3 := fun x hx => Nat.lt_of_lt_of_le (hc2 x hx) hr3
        obtain ⟨m1, rs4, hs4, hRn, hEnew, hWn, hra, hr4e, hag4, hFb, hcell⟩ :=
          bindCode_run lay (τ := .int lo' hi') (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hn.1, hn.2⟩ : Zahl lo' hi') ov r3 m rs3 hRl hE3 hW
            hev3 hlt3 hc3 hb
        subst hr4e
        have hseq1 : seqI (ce ++ cv) m rs1 = some (m, rs3) := by
          rw [seqI_append, hs2', Option.bind_some]; exact hs3'
        have hseq : seqI (ce ++ cv ++ cb) m rs1 = some (m1, rs4) := by
          rw [seqI_append, hseq1, Option.bind_some]; exact hs4
        obtain ⟨bkr, hbkr, hkpr⟩ := hKr
        have hreach2 := reach_block_jmp (S := S) (ks := ks) (dst := dst) hbb rfl hbkr hkpr hseq
        have hS1r : a + 1 ≤ s1.r := S1.2.2
        have hbound : ∀ x ∈ a :: cenv, x < s1.r := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hS1r
          · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc3 x hx') hra)) hS1r
        have IHr := lowerB_ok lay hL (a :: cenv) lv O passes R rest (st.l + 2) k s1 s2 br hb2
          M S fn hMr hk hlv hFn hCall (σ.lese Λ e.orte) (Env.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hn.1, hn.2⟩ ρ) m1 rs4 ks dst hRn hEnew hWn hbound
        have hF123 : Fr lay cenv st.r m rs m1 rs4 :=
          fr_trans (fr_regs hag1) (fr_trans (fr_regs hag2) (fr_trans (fr_regs hag3) hFb hr3 hc2) hr2 hc1) hr1 hc
        exact outok_bind (Reach.trans hbr hreach2) hF123 hcell hc
          (Nat.le_trans (Nat.le_trans hr1 (Nat.le_trans hr2 (Nat.le_trans hr3 hra)))
            (Nat.le_trans (Nat.le_succ a) hS1r)) _ IHr
      · rw [dif_neg hn]
        have hF : (eval (σ.lese Λ e.orte) (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
            (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi'))) (σ.lese Λ e.orte) ρ : Bool)
            = false := by
          rw [hcond]
          by_cases h1 : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n
          · have h2 : ¬ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := fun h2 => hn ⟨h1, h2⟩
            rw [decide_eq_false h2]; exact Bool.and_false _
          · rw [decide_eq_false h1]; rfl
        have hev : oc.ev rs1 = some (.int 1 (0 : BitVec 1)) := by
          rw [hF] at hev1; exact hev1
        obtain ⟨bke, hbke, hkpe⟩ := hKe
        have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
        have hbr0 := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (0 : BitVec 1)) hb0 rfl hs1' hev
          (by simpa [h01] using hbke) hkpe
        have hbr : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
          simpa [h01] using hbr0
        exact outok_mono S2.2.2 _ (outok_lift hbr (fr_regs hag1) (Nat.le_trans hr1 hle14) hc _ (outok_of_endok _
          (lowerEnd_ok lay hL cenv lv O passes R sonst st.l ⟨r4, st.l + 3⟩ s1 be hb1 M S fn hMe hlv hFn hCall (σ.lese Λ e.orte) ρ m rs1
            ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hle14))))
  | _, _, _, _, .float .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .floatLit .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .floatOf .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h
  | _, _, _, _, .floatNarrow .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerB] at h

theorem lowerEnd_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Gabbro.Grammatik.Endblock D V l Γ Λ)
      (lb : Lbl) (st st' : St) (blks : List Block),
      lowerEnd lay cenv lv e lb st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R e σ ρ)
  | _, _, _, .ret (Λ := Λ) e _, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerEnd] at h
      simp only [execEnd, EndOk]
      obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerRet_ok lay hL cenv V.gruende e lb st st' blks h M S fn hM
        (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
      exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩
  | _, _, _, .leave .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execEnd, EndOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.1
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, .next .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execEnd, EndOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.2
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, .cons s rest, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
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
        hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
      have hle : s1.r ≤ s2.r := SS.2.2
      have S0 := lowerS_shape lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
      simp only [execEnd]
      rcases hx : execStmt O passes R s σ ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1'⟩ | ⟨h1, σ1, ρ1⟩ |
        ⟨h1, σ1, ρ1⟩ | e1 | e1
      · rw [hx] at IHs
        obtain ⟨m1, rs1, hr1, hP1, hF1⟩ := IHs
        obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
        simp only [hx]
        exact endok_lift hr1 hF1 S0.2.2 hc _ (lowerEnd_ok lay hL cenv lv O passes R rest st.l s1 s2 b2 hr M S fn hM2 hlv hFn hCall
          σ1 ρ1 m1 rs1 ks dst hRp hEp hWp hcp)
      · rw [hx] at IHs
        simp only [hx]
        exact IHs
      · rw [hx] at IHs
        simp only [hx]
        exact IHs
      · rw [hx] at IHs
        simp only [hx]
        exact runOk_mono hle IHs
      · rw [hx] at IHs
        simp only [hx]
        exact runOk_mono hle IHs
      · simp only [hx, EndOk]
      · simp only [hx, EndOk]
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) (Λ := Λ) e rest, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall,
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
      obtain ⟨m1, rs3, hs3, hRn, hEnew, hWn, hra, hr2e, hag3, hFb, hcell⟩ :=
        bindCode_run lay (eval σl e σl ρ) oe r1 m rs1 hRl hE1 hW hev1 hlt1 hc1 hb
      subst hr2e
      have hFbind : Fr lay cenv st.r m rs m1 rs3 := fr_trans (fr_regs hag1) hFb hr1 hc
      have hseq : seqI (ce ++ cb) m rs = some (m1, rs3) := by
        rw [seqI_append, hs1', Option.bind_some]; exact hs3
      have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hb0 rfl hbk2 hkp2 hseq
      have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') hra)
      have IHr := lowerEnd_ok lay hL (a :: cenv) lv O passes R rest st.l ⟨a + 1, st.l + 1⟩ s2 b2 hr M S fn
        hM2 hlv hFn hCall σl (Env.cons (eval σl e σl ρ) ρ) m1 rs3 ks dst hRn hEnew hWn hbound
      simp only [execEnd]
      try rw [← hσl]
      exact endok_bind hreach hFbind hcell hc (Nat.le_succ_of_le (Nat.le_trans hr1 hra)) _ IHr
  | _, _, _, .retWhy r _, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd] at h
      simp only [execEnd, EndOk]
      obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerWhy_ok lay cenv V.gruende V.erg r.val lb st st' blks h M S fn hM
        m rs ks dst
      exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩
  | _, _, _, .bindAxiom .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerEnd] at h
  | _, _, _, .bindAxiomElse .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp [lowerEnd] at h

/-- Every arm body of a `match` on a tagged value refines (the structural companion of `lowerB_ok`). -/
theorem lowerAr_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (i : Fin cs.length),
      ArmBOk lay cenv lv O passes R (cs.get i) (garmT arms i)
  | _, _, _, _, _, .cons (c := none) b _, ⟨0, _⟩ =>
      fun lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc =>
        lowerB_ok lay hL cenv lv O passes R b lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst
          hR hE hW hc
  | _, _, _, _, _, .cons (c := some (lo, hi)) b _, ⟨0, _⟩ =>
      fun a lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc =>
        lowerB_ok lay hL (a :: cenv) lv O passes R b lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs
          ks dst hR hE hW hc
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, hi⟩ =>
      lowerAr_ok lay hL cenv lv O passes R rest ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Every arm of a `match` on a reason refines (the arms are subterms, so this is the structural
    companion of `lowerB_ok`). -/
theorem lowerGA_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (i : Fin n),
      BOk lay cenv lv O passes R (garm arms i)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩ =>
      fun lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc =>
        lowerB_ok lay hL cenv lv O passes R b lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst
          hR hE hW hc
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, hi⟩ =>
      lowerGA_ok lay hL cenv lv O passes R rest ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end

end Gabbro.Code.Lower
