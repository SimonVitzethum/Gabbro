module
public import Grammatik.Code.Refine.Stmt
public import Grammatik.Code.Refine.Loops.Loop
public import Grammatik.Code.Refine.Loops.Traverse
public import Grammatik.Code.Refine.Loops.Retry
public import Grammatik.Code.Refine.Calls.CallRun
public import Grammatik.Code.Refine.Match.OnOption
public import Grammatik.Code.Refine.Match.Why
public import Grammatik.Code.Refine.Match.Tag
public import Grammatik.Code.Refine.Match.Else
@[expose] public section


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

set_option linter.unusedSectionVars false in
theorem lowerS_ok_assignGlob (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (g)
    (e)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignGlob (Λ := Λ) g e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hk : KOk M fn k)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.assignGlob (Λ := Λ) g e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  have hs : supp (D.gtyp g) = true := by
    cases hbb : supp (D.gtyp g)
    · simp only [hbb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · rfl
  simp only [hs, if_true] at h
  rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hst : storeTo (D.gtyp g) oe r1 (.glob (lay.ggblk g)) with _ | ⟨cs, r2⟩
  · simp only [hst, reduceCtorEq] at h
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
    (hR.2 g hs).1 cs r2 hst
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

set_option linter.unusedSectionVars false in
theorem lowerS_ok_ret (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (e)
    (zz1)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.ret (Λ := Λ) e zz1 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hk : KOk M fn k)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.ret (Λ := Λ) e zz1 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  simp only [execStmt, OutOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerRet_ok lay hL cenv V.gruende e lb st st' blks h M S fn hM
    (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
  exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerS_ok_assignSlot (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (t)
    (f)
    (i)
    (e)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignSlot (Λ := Λ) t f i e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hk : KOk M fn k)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.assignSlot (Λ := Λ) t f i e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  have hs : supp (D.typ t f) = true := by
    cases hbb : supp (D.typ t f)
    · simp only [hbb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · rfl
  simp only [hs, if_true] at h
  rcases hi : lowerE lay cenv i st.r with _ | ⟨ci, oi, r1⟩
  · simp only [hi, reduceCtorEq] at h
  simp only [hi] at h
  rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hsa : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r2 with
    _ | ⟨ca, oa, r3⟩
  · simp only [hsa, reduceCtorEq] at h
  simp only [hsa] at h
  rcases hst : storeTo (D.typ t f) oe r3 oa with _ | ⟨cs, r4⟩
  · simp only [hst, reduceCtorEq] at h
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

set_option linter.unusedSectionVars false in
theorem lowerS_ok_assignThru (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (Λ)
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) (Λ := Λ) p t ht f i e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hk : KOk M fn k)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) (Λ := Λ) p t ht f i e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  have hs : supp (D.typ t f) = true := by
    cases hbb : supp (D.typ t f)
    · simp only [hbb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · rfl
  simp only [hs, if_true] at h
  rcases hp : lowerE lay cenv p st.r with _ | ⟨cp, op, r1⟩
  · simp only [hp, reduceCtorEq] at h
  simp only [hp] at h
  rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
  · simp only [hi, reduceCtorEq] at h
  simp only [hi] at h
  rcases he : lowerE lay cenv e r2 with _ | ⟨ce, oe, r3⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r3 with _ | ⟨ca, oa, r4⟩
  · simp only [hsa, reduceCtorEq] at h
  simp only [hsa] at h
  rcases hst : storeTo (D.typ t f) oe r4 oa with _ | ⟨cs, r5⟩
  · simp only [hst, reduceCtorEq] at h
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
    simp only [encR, (Deklaration.capTab_sound ht).1]
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

set_option linter.unusedSectionVars false in
theorem lowerS_ok_assignThruOwn (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (Λ)
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (mo)
    (s)
    (ho)
    (he)
    (hg)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) (Λ := Λ) p t ht f i e mo s ho he hg zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hk : KOk M fn k)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) (Λ := Λ) p t ht f i e mo s ho he hg zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  have hs : supp (D.typ t f) = true := by
    cases hbb : supp (D.typ t f)
    · simp only [hbb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · rfl
  simp only [hs, if_true] at h
  rcases hp : lowerE lay cenv p st.r with _ | ⟨cp, op, r1⟩
  · simp only [hp, reduceCtorEq] at h
  simp only [hp] at h
  rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
  · simp only [hi, reduceCtorEq] at h
  simp only [hi] at h
  rcases he : lowerE lay cenv e r2 with _ | ⟨ce, oe, r3⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r3 with _ | ⟨ca, oa, r4⟩
  · simp only [hsa, reduceCtorEq] at h
  simp only [hsa] at h
  rcases hst : storeTo (D.typ t f) oe r4 oa with _ | ⟨cs, r5⟩
  · simp only [hst, reduceCtorEq] at h
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
    simp only [encR, (Deklaration.capTab_sound ht).1]
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

end Gabbro.Code.Lower
