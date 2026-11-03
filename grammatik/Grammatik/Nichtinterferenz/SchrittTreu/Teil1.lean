/-
  File:      Grammatik/Nichtinterferenz/SchrittTreu.lean
  Subject:   EVERY RULE OF MACHINE G COMPUTES `kSchrittK` (`schrittK_von`).

  One case per rule: the head residue named by the rule's `hhead` is
  put into the ghost-free state (`kSchrittK_kern`), the side conditions are
  dropped, the value premises (`hw`, `hv`, `hstep`, …) decide the branch of
  the function, and both sides are the same term.
-/
module
public import Grammatik.Nichtinterferenz.SchrittTreu.Teil1Basis
import all Grammatik.Nichtinterferenz.SchrittTreu.Teil1Basis
public import Grammatik.Nichtinterferenz.Schritt
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
theorem schrittK_von_g3 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG3 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
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
  | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
      hrho neu hneu =>
      kstart
      subst hs0 hrho
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
      hrho neu hneu =>
      kstart
      subst hs0 hrho
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannAxiomCallElseOk l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | dannAxiomCallElseGrund l Γ Λ Λ' e a args he hp hd hgd hr err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, kEntf, if_true]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
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
        simp only [RufRahmenG.kern, GRest.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, GRest.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hk σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      kstart
      cases hstep
      subst hs₁
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kLeave,
        Env.tail]
      simp only [RufMaschineG.weltVon] at hw
      rw [if_pos hw]
      rfl
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      cases hstep
      rfl
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      cases hstep
      rfl
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      cases hstep
      rfl
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
      cases hstep
      rfl

theorem schrittK_von_g4 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG4 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hk hΛ =>
      kstart
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
      rw [if_neg (by
        rw [kern_wartend (caller := caller) (r := caller.rest.2.2.2.2) rfl]
        change ¬caller.wartend = true
        rw [hnw]
        exact Bool.false_ne_true)]
      rfl
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu
      hnw =>
      subst hfg hrho hv hs1
      kstart
      rw [hpop]
      simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusEnde, execStmt, kPop,
        List.map_cons]
      rw [if_neg (by
        rw [kern_wartend (caller := caller) (r := caller.rest.2.2.2.2) rfl]
        change ¬caller.wartend = true
        rw [hnw]
        exact Bool.false_ne_true)]
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
        simp only [RufRahmenG.kern, GRest.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, GRest.kern, hc]
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
        simp only [RufRahmenG.kern, GRest.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
      · rw [if_pos (by rw [kern_wartend hc]; rfl)]
        unfold kBinde
        simp only [RufRahmenG.kern, GRest.kern, hc]
        rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).erg = some τ from he)]
        rfl
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
      hrho s0 hs0 rg hrg hn =>
      subst hfg hrho hrg
      kstart
      rw [hpop]
      simp only [kr, kEnde, kPopGrund, List.map_cons]
      simp only [RufRahmenG.kern, GRest.kern, hcaller]
      rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).gruende = n from hn)]
      rfl

end Gabbro.Grammatik
