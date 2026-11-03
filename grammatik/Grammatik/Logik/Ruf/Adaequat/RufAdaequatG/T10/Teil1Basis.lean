/- Part 10 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9
@[expose] public section


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
  | g1 hs =>
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
    | ruf =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
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
      refine Or.inl ⟨_, _, _, _, .dann (.cons s .nil) (.ende rest), _, rufUpdateG_self _ _ _, RestG.dann _ _ (BlockG.cons s .nil hs BlockG.nil) (by simp only [Block.ohneOrakel, ho.1, Bool.and_self]) (RestG.ende rest hr ho.2), ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq (sem_endeEntf O passes s rest _ _)
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
    | dannOnTagSome l2 Γ2 Λ2 Λ2' Λ2'' cs v arms rest k ρ2 hhead σ₁ hs₁ τ b nutz hw neu hneu =>
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
      exact REnde.gleich_of_eq (sem_tagSome O passes v arms rest k _ _ τ b nutz hw)
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
    | endeBindAxiom =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | endeBindAxiomOpt =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | g2 hs =>
    cases hs with
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
    | dannTrav =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | travNext =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | travFort =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | travDone =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannRetry =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | wiederUeber =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | wiederWeiter =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | wiederSchritt =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | wiederFort =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannForever =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | ewigWeiter =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | ewigFort =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | rufDann =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | g3 hs =>
    cases hs with
    | dannAxiomCallElseOk =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannAxiomCallElseGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannCallInd =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | rufCallInd =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindCall =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindCallInd =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindCallElse =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindCallIndElse =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannCallIndElse =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | rueckBind caller rst hpop l2 Γ2 Λ2 Λ2' τ restb k ρc hcaller Γc Λc e hperm ρ2 hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      rw [hR] at hhead
      cases hhead
      subst hfg hs0 hs1 hv
      refine Or.inr ⟨_, _, ?_, REnde.gleich_of_eq (sem_rueck O passes e hperm _ _)⟩
      rw [faeden_upd, hrho]
      rfl
    | dannLeaveTrav =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannNextTrav =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannLeaveWieder =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannNextWieder =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannLeaveEwig =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | g4 hs =>
    cases hs with
    | dannNextEwig =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelDannLeave =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelDannNext =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelSchrumpfLeave =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelSchrumpfNext =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelFreiLeave =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelFreiNext =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelAbbruchLeave =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | peelAbbruchNext =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
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
    | rueckGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | g5 hs =>
    cases hs with
    | dannRegLies =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannRegLiesElseWahr =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannRegLiesElseFalsch =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannAwaits =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannExchange =>
      rename_i l2 Γ2 Λ2 Λ2' g neuE hL ρ2 σ₁ σ₂ hs₂ neu hw rest k hhead hs₁ hneu hΛ
      rw [hR] at hhead
      cases hhead
      subst hs₁
      subst hs₂
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
      simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
      refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.exchange_inv ho (RestG.schrumpf _ hk), ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq (sem_exchange O passes g neuE hw hL rest k (M.weltVon f) ρ)
    | dannGleit =>
      rename_i l2 Γ2 Λ2 Λ2' l₁ h₁ l₂ h₂ op a b lo hi ρ2 σ₁ v hv neu rest k hhead hs₁ hneu hΛ
      rw [hR] at hhead
      cases hhead
      subst hs₁
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
      simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
      refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleit_inv ho (RestG.schrumpf _ hk), ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq (sem_gleit O passes op a b lo hi rest k _ _ v hv)
    | dannGleitLit =>
      rename_i l2 Γ2 Λ2 Λ2' q lo hi ρ2 v hv rest k hhead
      rw [hR] at hhead
      cases hhead
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
      simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
      refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleitLit_inv ho (RestG.schrumpf _ hk), ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq (sem_gleitLit O passes q lo hi rest k _ _ v hv)
    | dannGleitVon =>
      rename_i l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi ρ2 σ₁ v hv neu rest k hhead hs₁ hneu hΛ
      rw [hR] at hhead
      cases hhead
      subst hs₁
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
      simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
      refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hb.gleitVon_inv ho (RestG.schrumpf _ hk), ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq (sem_gleitVon O passes e lo hi rest k _ _ v hv)
    | dannGleitNarrowOk =>
      rename_i l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi ρ2 σ₁ v hv neu sonst rest k hhead hs₁ hneu hΛ
      rw [hR] at hhead
      cases hhead
      subst hs₁
      obtain ⟨⟨_, hb⟩, ho, hk⟩ := hcov.dann_inv
      obtain ⟨_, hr, hs, _⟩ := hb.gleitNarrow_inv
      simp only [Block.ohneOrakel, Stmt.ohneOrakel, Endblock.ohneOrakel, Bool.and_eq_true] at ho
      refine Or.inl ⟨_, _, _, _, .dann rest (.schrumpf k), _, rufUpdateG_self _ _ _, RestG.dann _ _ hr ho.2 (RestG.schrumpf _ hk), ?_⟩
      rw [weltVon_upd]
      exact REnde.gleich_of_eq (sem_gleitNarrowOk O passes e lo hi sonst rest k _ _ v hv)
    | dannGleitNarrowElse =>
      rename_i l2 Γ2 Λ2 Λ2' l₁ h₁ e lo hi ρ2 σ₁ hn neu sonst rest k hhead hs₁ hneu hΛ
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
    | dannBindAxiom =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindAxiomElseOk =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindAxiomElseGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindAxiomOpt =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindAxiomOptElseOk =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannBindAxiomOptElseGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | rueckConsGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannRetGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | endeBindAxiomElseGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | endeBindAxiomOptElseOk =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | endeBindAxiomOptElseGrund =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | g7 hs =>
    cases hs with
    | dannVerbrauch =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | verbrauchWeiter =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | verbrauchLeer =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | verbrauchFort =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannLeaveVerbrauch =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
    | dannNextVerbrauch =>
      have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead


end Gabbro.Grammatik
