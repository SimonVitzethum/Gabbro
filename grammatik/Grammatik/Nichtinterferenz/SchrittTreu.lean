/-
  File:      Grammatik/Nichtinterferenz/SchrittTreu.lean
  Subject:   EVERY RULE OF MACHINE G COMPUTES `kSchrittK` (`schrittK_von`).

  One case per rule (74): the head residue named by the rule's `hhead` is
  put into the ghost-free state (`kSchrittK_kern`), the side conditions are
  dropped, the value premises (`hw`, `hv`, `hstep`, …) decide the branch of
  the function, and both sides are the same term.
-/
import Grammatik.Nichtinterferenz.Schritt

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- `kSchrittK` of a thread state whose head residue is known. -/
theorem kSchrittK_kern (P : Programm D) (O : Orakel D) (passes : Nat) (z : RufFadenG D)
    (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (h : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    kSchrittK P O passes z.kern sp =
      kr P O passes (z.stapel.map RufRahmenG.kern) z.kopf.f z.kopf.rho z.spur sp ρ r := by
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

set_option hygiene false in
/-- The common start of every case of `schrittK_von`. -/
macro "kstart" : tactic => `(tactic| (
  rw [kSchrittK_kern _ _ _ _ _ ‹(M.faeden f).kopf.rest = _›]
  dsimp only
  rw [rufUpdateG_self]))

set_option maxHeartbeats 4000000 in
/-- **Every rule of machine G computes `kSchrittK`**: the ghost-free state
    of the acting thread after the step, and the memory after the step, are
    what `kSchrittK` returns from the ghost-free state and memory before. -/
theorem schrittK_von (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hk =>
      kstart
      simp only [kr, kEnde, kEndeCons, GEntfaltbar_blatt s hleaf, hleaf]
      simp only [RufMaschineG.weltVon] at hstep
      simp only [hstep, kAusEnde, kLokal, RufFadenG.kern, RufRahmenG.kern]
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
      rw [if_neg (by simpa [RufRahmenG.wartend, RufRahmenG.kern] using hnw)]
      rfl
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      kstart
      simp only [kr, kEnde, kEndeCons, hent, if_true]
      rfl
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hk =>
      kstart
      simp only [kr, kDann, kDannCons, GEntfaltbar_blatt s hleaf, hleaf]
      simp only [RufMaschineG.weltVon] at hstep
      simp only [hstep, kAusDann, kLokal, RufFadenG.kern, RufRahmenG.kern]
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
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
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
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      kstart
      subst hs0 hrho
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kRufDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      kstart
      subst hs0 hrho
      simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kRufEnde]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      kstart
      subst hs0 hrho
      rfl
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
      kstart
      subst hs0 hrho
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
      kstart
      subst hs0 hrho
      rfl
  | rueckBind caller rest hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hh g hfg rho hrho s0
      hs0 hΛ s1 hs1 v hv he neu hneu =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kEnde, kPop, List.map_cons]
      rcases hcaller with hc | ⟨n, err, hc⟩
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hk σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kLeave,
        Env.tail]
      rw [if_pos hw]
      rfl
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      rfl
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      rfl
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      kstart
      rfl
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      kstart
      rfl
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      kstart
      rfl
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      kstart
      rfl
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      kstart
      rfl
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      kstart
      rfl
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      kstart
      rfl
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      kstart
      rfl
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kPop,
        List.map_cons]
      rw [if_neg (by simpa [RufRahmenG.wartend, RufRahmenG.kern] using hnw)]
      rfl
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusEnde, execStmt, kPop,
        List.map_cons]
      rw [if_neg (by simpa [RufRahmenG.wartend, RufRahmenG.kern] using hnw)]
      rfl
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kPop,
        List.map_cons]
      rcases hcaller with hc | ⟨n, err, hc⟩
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusEnde, execStmt, kPop,
        List.map_cons]
      rcases hcaller with hc | ⟨n, err, hc⟩
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
      hrho s0 hs0 rg hrg hn =>
      subst hfg hrho hrg
      kstart
      rw [hpop]
      simp only [kr, kEnde, kPopGrund, List.map_cons]
      simp only [RufRahmenG.kern, hcaller]
      rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).gruende = n from hn)]
      rfl
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hrho hrg
      kstart
      rw [hpop]
      simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusEnde, execStmt, kPopGrund,
        List.map_cons]
      simp only [RufRahmenG.kern, hcaller]
      rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).gruende = n from hn)]
      rfl
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hrho hrg
      kstart
      rw [hpop]
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kPopGrund,
        List.map_cons]
      simp only [RufRahmenG.kern, hcaller]
      rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).gruende = n from hn)]
      rfl
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
      kstart
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      simp only [hz, if_true]
      rfl
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv hw
      rw [hv]
      simp only
      rw [if_pos hw]
      rfl
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv hw
      rw [hv]
      simp only
      rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
      rfl
  | dannAwaits l Γ Λ Λ' g payload hp hL rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hvis
      rw [if_pos hvis]
      rfl
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      kstart
      subst hs₂ hs₁
      rfl
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      kstart
      simp only [kr, kDann]
      rw [hv]
      rfl
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hn
      rw [hn]
      rfl
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl

end Gabbro.Grammatik
