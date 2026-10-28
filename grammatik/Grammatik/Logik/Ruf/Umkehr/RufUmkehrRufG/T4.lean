/- Part 4 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

set_option linter.unusedSimpArgs false in
/-- **Each step keeps the frame semantics, with calls.** The top frame of a
    covered residue either stays (same frame result), pops (logged value =
    frame result), or pushes an admitted callee above the frame it leaves
    waiting (`ErhaltK`). `hRSG`: the handler does not see the trace on the
    admitted callees (the trace may differ; the bare lock steps that
    changed only the trace were removed from G on 2026-09-13). -/
theorem schrittErhaltK {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {A : D.Lock → Prop}
    {C : D.Fn → Prop} (hRSG : RufSG R C)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestK A C r) :
    ErhaltK P O passes R A C M M' f z ρ r := by
  subst hz
  unfold ErhaltK
  cases hs with
  | blatt l2 Γ2 Λ2 Λ2' s rest ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨_, hr, _⟩ := he.cons_inv
    simp only [Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende rest hr ho.2, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_blatt O passes R s rest _ _ _ ρ' (by rw [istBlatt_R O passes R hleaf]; exact hstep))
  | ruf l2 Γ2 Λ2 g args hp hr rest ρ2 hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs0 hrho
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨hst, hr', _⟩ := he.cons_inv
    have hC := hst.call_inv
    simp only [Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inr (Or.inr ⟨g, _, _, _, hC, rufUpdateG_self _ _ _, rfl,
      Or.inl ⟨_, _, _, _, .ende rest, rfl, rfl, RestK.ende rest hr' ho.2, ?_⟩⟩)
    intro σ1 v1 hR1
    exact semK_ruf O passes R g args hp hr rest _ _ σ1 v1 hR1
  | rueck caller rst hpop Γ2 Λ2 e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr (Or.inl ⟨_, _, caller, caller, rst, hpop, Wiederauf.wie hnw, ?_, rfl,
      REnde.gleich_of_eq (semK_rueck O passes R e hperm _ _)⟩)
    rw [faeden_upd, hrho]
    rfl
  | endeEntf l2 Γ2 Λ2 Λ2' s rest ρ2 hent hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨hs, hr, _⟩ := he.cons_inv
    simp only [Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann (.cons s .nil) (.ende rest), _, rufUpdateG_self _ _ _, RestK.dann _ _ (BlockR.cons s .nil hs BlockR.nil) (by simp only [Block.kOk, ho.1, Bool.and_self]) (RestK.ende rest hr ho.2), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeEntf O passes R s rest _ _)
  | endeForm l2 Γ2 Λ2 e ρ2 hl hent hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    cases he <;> simp only [EndEntfaltbar, Bool.false_eq_true] at hent
  | dannBlatt l2 Γ2 Λ2 Λ2' Λ2'' s rest k ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_dannBlatt O passes R s rest k _ _ _ ρ' (by rw [istBlatt_R O passes R hleaf]; exact hstep))
  | dannLeer l2 Γ2 Λ2 k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | dannIteWahr l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann t (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ ht ho.1.1 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_iteWahr O passes R c t e rest k _ _ hw)
  | dannIteFalsch l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann e (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ he ho.1.2 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_iteFalsch O passes R c t e rest k _ _ hw)
  | dannOnOptionSome l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann p (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestK.dann _ _ hp ho.1.1 (RestK.schrumpf _ (RestK.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_optSome O passes R o p a rest k _ _ v hv)
  | dannOnOptionNone l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann a (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ ha ho.1.2 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_optNone O passes R o p a rest k _ _ hv)
  | dannOnTagSome l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ lo hi b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    have hbb := armWahlG_R' arms _ hw ha
    have hbo := armWahlG_kOk' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbb hbo (RestK.schrumpf _ (RestK.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_tagSome O passes R v arms rest k _ _ lo hi b nutz hw)
  | dannOnTagNone l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    have hbb := armWahlG_R' arms _ hw ha
    have hbo := armWahlG_kOk' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbb hbo (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_tagNone O passes R v arms rest k _ _ b nutz hw)
  | dannOnGrund l2 Γ2 Λ2 Λ2' Λ2'' n rg arms rest k ρ2 hhead σ₁ hs₁ b hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁ hw
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onGrund_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, _, _, rufUpdateG_self _ _ _, RestK.dann _ _ (grundWahlG_R arms _ ha) (grundWahlG_kOk arms _ ho.1) (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_grund O passes R rg arms rest k _ _)
  | endeBind l2 Γ2 Λ2 τ e rest ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨he, ho⟩ := hcov.ende_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende rest he.bind_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeBind O passes R e rest (M.weltVon f) ρ)
  | dannBind l2 Γ2 Λ2 Λ2' Λ2'' τ e rest k ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.bind_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_dannBind O passes R e rest k (M.weltVon f) ρ)
  | dannNarrowOk l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_narrowOk O passes R e lo' hi' sonst rest k _ _ h)
  | dannNarrowElse l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann sonst.alsBlock.2 (.abbruch k), _, rufUpdateG_self _ _ _,
      RestK.dann _ _ (EndR.alsBlock hs) (by rw [Endblock.kOk_alsBlock]; exact ho.1)
        (RestK.abbruch _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_narrowElse O passes R e lo' hi' sonst rest k _ _ h)
  | dannPruefWahr l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_pruefWahr O passes R c sonst rest k _ _ hw)
  | dannPruefFalsch l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann sonst.alsBlock.2 (.abbruch k), _, rufUpdateG_self _ _ _,
      RestK.dann _ _ (EndR.alsBlock hs) (by rw [Endblock.kOk_alsBlock]; exact ho.1)
        (RestK.abbruch _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_pruefFalsch O passes R c sonst rest k _ _ hw)
  | dannBreaking l2 Γ2 Λ2 Λ2' Λ2'' i body rest k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have hbd := hst.breaking_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.dann rest k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbd ho.1 (RestK.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_breaking O passes R i body rest k _ _)
  | dannLocks l2 Γ2 Λ2 Λ2'' L hrg body rest k ρ2 hhead hself hrang hfrei =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨_, hbd, _⟩ := hst.locks_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.frei L (.dann rest k)), _, rufUpdateG_self _ _ _, RestK.dann _ _ hbd ho.1 (RestK.frei _ _ (RestK.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact semK_locks O passes R L hrg body rest k (M.weltVon f) ρ
  | freiGib l2 Γ2 Λ2 L k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hcov.frei_inv, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | schrumpfVergiss l2 Γ2 Λ2 τ k v ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    refine Or.inl ⟨_, _, _, _, k, _, rufUpdateG_self _ _ _, hcov.schrumpf_inv, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq rfl
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | travNext _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | travDone _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederUeber _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeBindAxiom _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rufDann l2 Γ2 Λ2 Λ2' Λ2'' g args hp hr rest k ρ2 hhead hΛ s0 hs0 rho hrho neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs0 hrho
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr'⟩ := hb.cons_inv
    have hC := hst.call_inv
    simp only [Block.kOk, Bool.and_eq_true] at ho
    refine Or.inr (Or.inr ⟨g, _, _, _, hC, rufUpdateG_self _ _ _, rfl,
      Or.inl ⟨_, _, _, _, .dann rest k, rfl, rfl, RestK.dann rest k hr' ho.2 hk, ?_⟩⟩)
    intro σ1 v1 hR1
    exact semK_rufDann O passes R g args hp hr rest k _ _ σ1 v1 hR1
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannBindCall l2 Γ2 Λ2 Λ2' Λ2'' τ g args he hp hr rest k ρ2 hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs0 hrho
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hC, hrest⟩ := hb.bindCall_inv
    simp only [Block.kOk] at ho
    refine Or.inr (Or.inr ⟨g, _, _, _, hC, rufUpdateG_self _ _ _, rfl,
      Or.inr ⟨_, _, _, _, _, _, rest, k, he, rfl,
        RestK.dann rest (.schrumpf k) hrest ho (RestK.schrumpf k hk), ?_⟩⟩)
    intro σ1 v1 hR1
    exact semK_bindCall O passes R g args he hp hr rest k _ _ σ1 v1 hR1
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rueckBind caller rst hpop l2 Γ2 Λ2 Λ2' τ restb k ρc hcaller Γc Λc e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    rcases hcaller with hc | ⟨n, err, hc⟩
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop, Wiederauf.bind restb k ρc hc he, ?_, rfl,
        REnde.gleich_of_eq (semK_rueck O passes R e hperm _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop,
        Wiederauf.bindSonst n err restb k ρc hc he, ?_, rfl, REnde.gleich_of_eq (semK_rueck O passes R e hperm _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelDannNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelAbbruchLeave _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | peelAbbruchNext _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRet l2 Γ2 Λ2 Λ2'' e hperm rest k ρ2 hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu
      hnw =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr (Or.inl ⟨_, _, caller, caller, rst, hpop, Wiederauf.wie hnw, ?_, rfl,
      REnde.gleich_of_eq (semK_dannRet O passes R e hperm rest k _ _)⟩)
    rw [faeden_upd, hrho]
    rfl
  | rueckCons caller rst hpop Γ2 Λ2 e hperm rest ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr (Or.inl ⟨_, _, caller, caller, rst, hpop, Wiederauf.wie hnw, ?_, rfl,
      REnde.gleich_of_eq (semK_rueckCons O passes R e hperm rest _ _)⟩)
    rw [faeden_upd, hrho]
    rfl
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    rcases hcaller with hc | ⟨n, err, hc⟩
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop, Wiederauf.bind restb k ρc hc he, ?_, rfl,
        REnde.gleich_of_eq (semK_dannRet O passes R e hperm restk kk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop,
        Wiederauf.bindSonst n err restb k ρc hc he, ?_, rfl, REnde.gleich_of_eq (semK_dannRet O passes R e hperm restk kk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
  | rueckConsBind lk Γk Λk e hperm restk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    rcases hcaller with hc | ⟨n, err, hc⟩
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop, Wiederauf.bind restb k ρc hc he, ?_, rfl,
        REnde.gleich_of_eq (semK_rueckCons O passes R e hperm restk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
    · refine Or.inr (Or.inl ⟨_, _, caller, _, rst, hpop,
        Wiederauf.bindSonst n err restb k ρc hc he, ?_, rfl, REnde.gleich_of_eq (semK_rueckCons O passes R e hperm restk _ _)⟩)
      rw [faeden_upd, hrho]
      rfl
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannExchange l2 Γ2 Λ2 Λ2' g neuE hw hL rest k ρ2 hhead σ₁ hs₁ σ₂ hs₂ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    subst hs₂
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.exchange_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_exchange O passes R g neuE hw hL rest k (M.weltVon f) ρ)
  | dannGleit l2 Γ2 Λ2 Λ2' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.gleit_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleit O passes R op a b lo hi rest k _ _ v hv)
  | dannGleitLit l2 Γ2 Λ2 Λ2' q lo hi rest k ρ2 hhead v hv =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.gleitLit_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitLit O passes R q lo hi rest k _ _ v hv)
  | dannGleitVon l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hb.gleitVon_inv ho (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitVon O passes R e lo hi rest k _ _ v hv)
  | dannGleitNarrowOk l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestK.dann _ _ hr ho.2 (RestK.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitNarrowOk O passes R e lo hi sonst rest k _ _ v hv)
  | dannGleitNarrowElse l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ hn neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.kOk, Stmt.kOk, Endblock.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann sonst.alsBlock.2 (.abbruch k), _, rufUpdateG_self _ _ _,
      RestK.dann _ _ (EndR.alsBlock hs) (by rw [Endblock.kOk_alsBlock]; exact ho.1)
        (RestK.abbruch _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_gleitNarrowElse O passes R e lo hi sonst rest k _ _ hn)
  | dannBindAxiom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | dannBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | rueckGrund _ _ _ hhead => widerlegeK hhead
  | rueckConsGrund _ _ _ _ hhead => widerlegeK hhead
  | dannRetGrund _ _ _ _ _ hhead => widerlegeK hhead


/-! ## 5. The pending call chain

    While the frame of `fn` is on the stack, the frames above it are its
    callees, their callees, and so on; each waits in the frame below it.
    The frame at position `i` above the frame of `fn` runs at depth `n - i`
    (its calls go through `rufRumpf (n - i)`). A returning frame's result is
    DEMANDED by the chain below it (`Anspruch`): a normal answer must make
    the frame below -- resumed as the machine resumes it -- end with the
    demand of ITS chain, down to the frame of `fn`, whose result must agree
    with `S` (the sequential result). A frame that does not answer normally
    (`sonst`) is never popped (`schrittErhaltK`), so it is demanded nothing. -/


end Gabbro.Grammatik
