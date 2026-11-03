/-
  File:      Grammatik/Nichtinterferenz/SchrittTreu.lean
  Subject:   EVERY RULE OF MACHINE G COMPUTES `kSchrittK` (`schrittK_von`).

  One case per rule: the head residue named by the rule's `hhead` is
  put into the ghost-free state (`kSchrittK_kern`), the side conditions are
  dropped, the value premises (`hw`, `hv`, `hstep`, …) decide the branch of
  the function, and both sides are the same term.
-/
module
public import Grammatik.Nichtinterferenz.Schritt
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- `kSchrittK` of a thread state whose head residue is known. -/
theorem kSchrittK_kern (P : Programm D) (O : Orakel D) (passes : Nat) (z : RufFadenG D)
    (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (h : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    kSchrittK P O passes z.kern sp =
      kr P O passes (z.stapel.map RufRahmenG.kern) z.kopf.f z.kopf.rho z.spur sp ρ r.kern := by
  unfold kSchrittK RufFadenG.kern RufRahmenG.kern
  dsimp only
  rw [h]

theorem GEntfaltbar_blatt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : s.istBlatt = true) : GEntfaltbar s = false := by
  cases s <;> simp_all [Stmt.istBlatt, GEntfaltbar]

/-- A frame whose residue waits is seen waiting through `kern`. -/
theorem kern_wartend {caller : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D caller.f) l Γ Λ}
    (hc : caller.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    (RufRahmenG.kern caller).rest.2.2.2.2.wartend = r.wartend := by
  unfold RufRahmenG.kern
  dsimp only
  rw [hc]
  cases r <;> rfl

set_option hygiene false in
/-- The common start of every case of `schrittK_von`. -/
macro "kstart" : tactic => `(tactic| (
  rw [kSchrittK_kern _ _ _ _ _ ‹(M.faeden f).kopf.rest = _›]
  dsimp only
  simp only [GRest.kern]
  rw [rufUpdateG_self]))

set_option maxHeartbeats 4000000 in
/-- **Every rule of machine G computes `kSchrittK`**: the ghost-free state
    of the acting thread after the step, and the memory after the step, are
    what `kSchrittK` returns from the ghost-free state and memory before. -/
theorem schrittK_von_g1 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG1 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hk =>
      kstart
      simp only [kr, kEnde, kEndeCons, GEntfaltbar_blatt s hleaf, hleaf]
      simp only [RufMaschineG.weltVon] at hstep
      simp only [hstep, kAusEnde, kLokal, RufFadenG.kern, RufRahmenG.kern, GRest.kern]
      rfl
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      kstart
      subst hs0 hrho
      rfl
  | rueck caller rest hpop Γ Λ e hperm ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kEnde, kPop, List.map_cons]
      rw [if_neg (by
        rw [kern_wartend (caller := caller) (r := caller.rest.2.2.2.2) rfl]
        change ¬caller.wartend = true
        rw [hnw]
        exact Bool.false_ne_true)]
      rfl
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      kstart
      simp only [kr, kEnde, kEndeCons, hent, if_true]
      rfl
  | endeForm l Γ Λ e ρ hl hent hhead =>
      kstart
      cases e <;> try (simp only [EndEntfaltbar, Bool.false_eq_true] at hent; done)
      all_goals (simp only [kr, kEnde, hl, if_true]; rfl)
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hk =>
      kstart
      simp only [kr, kDann, kDannCons, GEntfaltbar_blatt s hleaf, hleaf]
      simp only [RufMaschineG.weltVon] at hstep
      simp only [hstep, kAusDann, kLokal, RufFadenG.kern, RufRahmenG.kern, GRest.kern]
      rfl
  | dannLeer l Γ Λ k ρ hhead =>
      kstart
      rfl
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
      rfl
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ τ b nutz hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hw
      rw [hw]
      rfl
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hw
      rw [hw]
      rfl
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      kstart
      subst hs₁ hw
      rfl
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      kstart
      subst hs₁
      rfl
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      kstart
      subst hs₁
      rfl
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [RufMaschineG.weltVon] at h
      simp only [kr, kDann]
      rw [dif_pos h]
      rfl
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kEnde]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | endeBindAxiomOpt l Γ Λ e a args he hp hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kEnde]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl

theorem schrittK_von_g2 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG2 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [RufMaschineG.weltVon] at h
      simp only [kr, kDann]
      rw [dif_neg h]
      rfl
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
      rfl
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      kstart
      rfl
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      kstart
      rfl
  | freiGib l Γ Λ L k ρ hhead =>
      kstart
      rfl
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      kstart
      rfl
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      kstart
      rfl
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | travFort l Γ Λ t inv body is k i ρ hhead =>
      kstart
      rfl
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      kstart
      rfl
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      kstart
      rfl
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
      rfl
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      kstart
      rfl
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      kstart
      rfl
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
      kstart
      rfl
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      kstart
      subst hs0 hrho
      rfl


end Gabbro.Grammatik
