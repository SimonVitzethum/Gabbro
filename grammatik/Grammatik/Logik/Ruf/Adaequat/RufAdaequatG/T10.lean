/- Part 10 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T9

namespace Gabbro.Grammatik

variable {D : Deklaration}

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem schrittErhalt {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestG A r) :
    ErhaltG O passes A M M' f z ρ r := by
  subst hz
  unfold ErhaltG
  cases hs with
  | blatt l2 Γ2 Λ2 Λ2' s rest ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨_, hr, _⟩ := he.cons_inv
    simp only [Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende rest hr ho.2, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_blatt O passes s rest _ _ _ ρ' hstep)
  | ruf _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rueck caller rst hpop Γ2 Λ2 e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueck O passes e hperm _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | endeEntf l2 Γ2 Λ2 Λ2' s rest ρ2 hent hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    obtain ⟨hs, hr, _⟩ := he.cons_inv
    simp only [Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann (.cons s .nil) (.ende rest), _, rufUpdateG_self _ _ _, RestG.dann _ _ (BlockG.cons s .nil hs BlockG.nil) (by simp [Block.ohneOrakel, ho.1]) (RestG.ende rest hr ho.2), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeEntf O passes s rest _ _)
  | endeForm l2 Γ2 Λ2 e ρ2 hl hent hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨he, ho⟩ := hcov.ende_inv
    cases he <;> simp [EndEntfaltbar] at hent
  | dannBlatt l2 Γ2 Λ2 Λ2' Λ2'' s rest k ρ2 hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_dannBlatt O passes s rest k _ _ _ ρ' hstep)
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
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann t (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ ht ho.1.1 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_iteWahr O passes c t e rest k _ _ hw)
  | dannIteFalsch l2 Γ2 Λ2 Λ2' Λ2'' c t e rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨ht, he⟩ := hst.ite_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann e (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ he ho.1.2 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_iteFalsch O passes c t e rest k _ _ hw)
  | dannOnOptionSome l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann p (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestG.dann _ _ hp ho.1.1 (RestG.schrumpf _ (RestG.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_optSome O passes o p a rest k _ _ v hv)
  | dannOnOptionNone l2 Γ2 Λ2 Λ2' Λ2'' n o p a rest k ρ2 hhead σ₁ hs₁ hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨hp, ha⟩ := hst.onOption_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann a (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ ha ho.1.2 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_optNone O passes o p a rest k _ _ hv)
  | dannOnTagSome l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ lo hi b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    have hbb := armWahlG_G' arms _ hw ha
    have hbo := armWahlG_ohne' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.schrumpf (.dann rest k)), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbb hbo (RestG.schrumpf _ (RestG.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_tagSome O passes v arms rest k _ _ lo hi b nutz hw)
  | dannOnTagNone l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ b nutz hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onTag_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    have hbb := armWahlG_G' arms _ hw ha
    have hbo := armWahlG_ohne' arms _ hw ho.1
    refine Or.inl ⟨_, _, _, _, .dann b (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbb hbo (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_tagNone O passes v arms rest k _ _ b nutz hw)
  | dannOnGrund l2 Γ2 Λ2 Λ2' Λ2'' n rg arms rest k ρ2 hhead σ₁ hs₁ b hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁ hw
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have ha := hst.onGrund_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, _, _, rufUpdateG_self _ _ _, RestG.dann _ _ (grundWahlG_G arms _ ha) (grundWahlG_ohneOrakel arms _ ho.1) (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_grund O passes rg arms rest k _ _)
  | endeBind l2 Γ2 Λ2 τ e rest ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨he, ho⟩ := hcov.ende_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende rest he.bind_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeBind O passes e rest (M.weltVon f) ρ)
  | dannBind l2 Γ2 Λ2 Λ2' Λ2'' τ e rest k ρ2 hhead σ₁ hs₁ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.bind_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_dannBind O passes e rest k (M.weltVon f) ρ)
  | dannNarrowOk l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_narrowOk O passes e lo' hi' sonst rest k _ _ h)
  | dannNarrowElse l2 Γ2 Λ2 Λ2' Λ2'' lo hi lo' hi' e sonst rest k ρ2 hhead σ₁ hs₁ h neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.narrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann sonst.alsBlock.2 (.abbruch k), _, rufUpdateG_self _ _ _,
      RestG.dann _ _ (EndG.alsBlock hs) (by rw [Endblock.ohneOrakel_alsBlock]; exact ho.1)
        (RestG.abbruch _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_narrowElse O passes e lo' hi' sonst rest k _ _ h)
  | dannPruefWahr l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest k, _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 hk, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_pruefWahr O passes c sonst rest k _ _ hw)
  | dannPruefFalsch l2 Γ2 Λ2 Λ2' Λ2'' c sonst rest k ρ2 hhead σ₁ hs₁ hw neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.pruefung_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann sonst.alsBlock.2 (.abbruch k), _, rufUpdateG_self _ _ _,
      RestG.dann _ _ (EndG.alsBlock hs) (by rw [Endblock.ohneOrakel_alsBlock]; exact ho.1)
        (RestG.abbruch _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_pruefFalsch O passes c sonst rest k _ _ hw)
  | dannBreaking l2 Γ2 Λ2 Λ2' Λ2'' i body rest k ρ2 hhead =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    have hbd := hst.breaking_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.dann rest k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbd ho.1 (RestG.dann _ _ hr ho.2 hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_breaking O passes i body rest k _ _)
  | dannLocks l2 Γ2 Λ2 Λ2'' L hrg body rest k ρ2 hhead hself hrang hfrei =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨hst, hr⟩ := hb.cons_inv
    obtain ⟨_, hbd⟩ := hst.locks_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann body (.frei L (.dann rest k)), _, rufUpdateG_self _ _ _, RestG.dann _ _ hbd ho.1 (RestG.frei _ _ (RestG.dann _ _ hr ho.2 hk)), ?_⟩
    rw [weltVon_upd]
    exact sem_locks O passes L hrg body rest k (M.weltVon f) ρ
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
  | dannTrav _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | travNext _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | travFort _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | travDone _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRetry _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederUeber _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederWeiter _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederSchritt _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | wiederFort _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannForever _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | ewigWeiter _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | ewigFort _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rufDann _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rufCallInd _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindCallInd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindCallElse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rueckBind caller rst hpop l2 Γ2 Λ2 Λ2' τ restb k ρc hcaller Γc Λc e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueck O passes e hperm _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | dannLeaveTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannNextTrav _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannLeaveWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannNextWieder _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannLeaveEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannNextEwig _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelDannLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelDannNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelSchrumpfLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelSchrumpfNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelFreiLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelFreiNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelAbbruchLeave _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | peelAbbruchNext _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRet l2 Γ2 Λ2 Λ2'' e hperm rest k ρ2 hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_dannRet O passes e hperm rest k _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | rueckCons caller rst hpop Γ2 Λ2 e hperm rest ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueckCons O passes e hperm rest _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_dannRet O passes e hperm restk kk _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | rueckConsBind lk Γk Λk e hperm restk ρ2 hhead caller rst hpop l2 Γ2 Λ2 Λ2' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hfg hs0 hs1 hv
    refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueckCons O passes e hperm restk _ _)⟩
    rw [faeden_upd, hrho]
    rfl
  | dannRegLies _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRegLiesElseWahr _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannRegLiesElseFalsch _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannAwaits _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannExchange l2 Γ2 Λ2 Λ2' g neuE hw hL rest k ρ2 hhead σ₁ hs₁ σ₂ hs₂ neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    subst hs₂
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.exchange_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_exchange O passes g neuE hw hL rest k (M.weltVon f) ρ)
  | dannGleit l2 Γ2 Λ2 Λ2' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleit_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleit O passes op a b lo hi rest k _ _ v hv)
  | dannGleitLit l2 Γ2 Λ2 Λ2' q lo hi rest k ρ2 hhead v hv =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleitLit_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitLit O passes q lo hi rest k _ _ v hv)
  | dannGleitVon l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleitVon_inv ho (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitVon O passes e lo hi rest k _ _ v hv)
  | dannGleitNarrowOk l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ v hv neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 (RestG.schrumpf _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitNarrowOk O passes e lo hi sonst rest k _ _ v hv)
  | dannGleitNarrowElse l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi sonst rest k ρ2 hhead σ₁ hs₁ hn neu hneu =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
    obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
    simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .dann sonst.alsBlock.2 (.abbruch k), _, rufUpdateG_self _ _ _,
      RestG.dann _ _ (EndG.alsBlock hs) (by rw [Endblock.ohneOrakel_alsBlock]; exact ho.1)
        (RestG.abbruch _ hk), ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_gleitNarrowElse O passes e lo hi sonst rest k _ _ hn)
  | dannBindAxiom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | dannBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | endeBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | endeBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | endeBindAxiom _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlege hhead
  | rueckGrund _ _ _ hhead => widerlege hhead
  | rueckConsGrund _ _ _ _ hhead => widerlege hhead
  | dannRetGrund _ _ _ _ _ hhead => widerlege hhead

/-- A step of thread `f` keeps its log or prepends one event. -/
theorem rufSchrittG_log {P : Programm D} {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O passes M f M') :
    (M'.faeden f).log = (M.faeden f).log ∨ ∃ e, (M'.faeden f).log = e :: (M.faeden f).log := by
  cases hs <;> rw [faeden_upd] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, rfl⟩

/-! ## 17. TARGET B: the converse for the value -/

/-- The run invariant of the converse: either the frame of `fn` is still on
    top with a covered residue whose frame result agrees (up to the trace)
    with the fixed result `S`, or it has popped, and the log, below any later
    events, holds a `rueck` whose world and value agree with `S`. -/
def InvB (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (f : Faden) (fn : D.Fn)
    (rho : Env D (D.params fn)) (s0 : World D) (stapel : List (RufRahmenG D))
    (log : List (RufEreignisF D)) (S : REnde (vertragVon D fn)) (M : RufMaschineG D) : Prop :=
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D fn) l Γ Λ) (sp : List (Ereignis D)),
      M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨l, Γ, Λ, ρ, r⟩⟩, sp, log⟩ ∧
      RestG A r ∧ (semR O passes r (M.weltVon f) ρ).gleich S) ∨
  (∃ (v : ErgVal D (D.erg fn)) (s1 : World D) (ext : List (RufEreignisF D)),
      (M.faeden f).log = ext ++ RufEreignisF.rueck fn rho v s0 s1 :: log ∧
      (REnde.zurueck (V := vertragVon D fn) s1 v).gleich S)

theorem invB_schritt {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {f : Faden} {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {stapel : List (RufRahmenG D)} {log : List (RufEreignisF D)} {S : REnde (vertragVon D fn)}
    {M M' : RufMaschineG D} (hs : RufSchrittG P O passes M f M')
    (h : InvB O passes A f fn rho s0 stapel log S M) :
    InvB O passes A f fn rho s0 stapel log S M' := by
  rcases h with ⟨l, Γ, Λ, ρ, r, sp, hM, hc, hg⟩ | ⟨v, s1, ext, hlog, hg⟩
  · rcases schrittErhalt (A := A) hs _ hM ρ r rfl hc with
      ⟨l', Γ', Λ', ρ', r', sp', hM', hc', hg'⟩ | ⟨v, s1, hlog, hg'⟩
    · exact Or.inl ⟨l', Γ', Λ', ρ', r', sp', hM', hc', REnde.gleich_trans hg' hg⟩
    · refine Or.inr ⟨v, s1, [], ?_, REnde.gleich_trans (REnde.gleich_symm hg') hg⟩
      rw [List.nil_append]
      exact hlog
  · rcases rufSchrittG_log hs with he | ⟨e, he⟩
    · exact Or.inr ⟨v, s1, ext, by rw [he]; exact hlog, hg⟩
    · exact Or.inr ⟨v, s1, e :: ext, by rw [he, hlog]; rfl, hg⟩

theorem invB_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {f : Faden} {fn : D.Fn} {rho : Env D (D.params fn)} {s0 : World D}
    {stapel : List (RufRahmenG D)} {log : List (RufEreignisF D)} {S : REnde (vertragVon D fn)}
    {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M')
    (h : InvB O passes A f fn rho s0 stapel log S M) :
    InvB O passes A f fn rho s0 stapel log S M' := by
  induction hl with
  | refl => exact h
  | schritt hs _ ih => exact ih (invB_schritt hs h)

/-- **TARGET B -- the converse for the value.** Thread `f` of `M` runs a
    frame of `fn` with residue `.ende b` for a covered, oracle-free end
    block `b`. If ANY run of thread `f` alone reaches a machine whose log is
    the old log with exactly one new event `rueck fn rho' v' s0' s1'` (the
    pop of this frame -- a further call or return would add events), then
    the sequential semantics, started at the thread's world `M.weltVon f`,
    ends normally, returning THE SAME value `v'`, in a world with the same
    shared memory as the logged `s1'`; the logged parameters and entry
    world are the frame's.

    The statement was written for runs that interleave bare
    `nimmt`/`gibt` steps (removed from G on 2026-09-13; it holds a
    fortiori): the logged `s1'` agrees with `execEnd`'s world in memory,
    not necessarily in trace. No lock-freedom
    or holdings premise is needed: the statement is about runs that exist.
    `b.ohneOrakel` excludes `regLies`/`regLiesElse`/`awaits`, whose oracle
    sees the whole world, trace included (see the CUTS block). -/
theorem rufG_adaequat_umkehr (P : Programm D) (O : Orakel D) (passes : Nat)
    (M : RufMaschineG D) (f : Faden) (fn : D.Fn) (rho : Env D (D.params fn))
    (s0 : World D) (stapel : List (RufRahmenG D)) (spur : List (Ereignis D))
    (log : List (RufEreignisF D)) {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (b : Endblock D (vertragVon D fn) false Γ Λ) (A : D.Lock → Prop) (hb : EndG A b)
    (ho : b.ohneOrakel = true)
    (hM : M.faeden f = ⟨stapel, ⟨fn, rho, s0, ⟨false, Γ, Λ, ρ, .ende b⟩⟩, spur, log⟩)
    (M'' : RufMaschineG D) (hl : RufLaufG P O passes f M M'')
    (rho' : Env D (D.params fn)) (v' : ErgVal D (D.erg fn)) (s0' s1' : World D)
    (hlog : (M''.faeden f).log = RufEreignisF.rueck fn rho' v' s0' s1' :: log) :
    ∃ σ', execEnd O passes keinRuf b (M.weltVon f) ρ = .zurueck σ' v' ∧
      σ'.speicher = s1'.speicher ∧ rho' = rho ∧ s0' = s0 := by
  have h0 : InvB O passes A f fn rho s0 stapel log
      (endErg (execEnd O passes keinRuf b (M.weltVon f) ρ)) M :=
    Or.inl ⟨false, Γ, Λ, ρ, .ende b, spur, hM, RestG.ende b hb ho, REnde.gleich_refl _⟩
  rcases invB_lauf hl h0 with ⟨l, Γ', Λ', ρ', r, sp, hM'', _, _⟩ | ⟨v, s1, ext, hlog', hg⟩
  · rw [hM''] at hlog
    have hlen := congrArg List.length hlog
    simp at hlen
  · rw [hlog'] at hlog
    have hext : ext = [] := by
      have hlen := congrArg List.length hlog
      simp at hlen
      exact hlen
    subst hext
    simp only [List.nil_append, List.cons.injEq, RufEreignisF.rueck.injEq] at hlog
    obtain ⟨⟨_, hrho, hv, hs0, hs1⟩, _⟩ := hlog
    have hv' : v = v' := eq_of_heq hv
    have hrho' : rho = rho' := eq_of_heq hrho
    subst hv' hrho' hs0 hs1
    revert hg
    cases hex : execEnd O passes keinRuf b (M.weltVon f) ρ with
    | zurueck σ' w =>
      intro hg
      obtain ⟨hsg, hvw⟩ := hg
      subst hvw
      exact ⟨σ', rfl, hsg.speicher.symm, rfl, rfl⟩
    | _ => intro hg; exact absurd hg id

/-- The witness body never consults the oracle. -/
theorem adRumpf_ohneOrakel : adRumpf.ohneOrakel = true := rfl


end Gabbro.Grammatik
