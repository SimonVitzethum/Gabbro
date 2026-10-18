/- Part 4 of 7 of `RufMaschineG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufMaschineG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- One step preserves the invariant for the ACTING thread.
    `ruf` pushes the callee key with its entry event; `rueck` pops the
    head key with its return event; every other step keeps the key triple
    and the log, so `rufFadenPasstG_behalte` closes it. Every premise of
    the step is used: `hhead`/`hΛ` fix the firing frame, `hstep`/`hrho`/
    `hv` the computed data, `hpop`/`hfg`/`hrho`/`hs0` the popped frame. -/
theorem rufSchrittG_passt_acting (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f : Faden)
    (h : RufFadenPasstG (M.faeden f))
    (hs : RufSchrittG P O passes M f M') :
    RufFadenPasstG (M'.faeden f) := by
  cases hs with
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | rueck caller rest hpop Γ Λ e hperm ρ hh g hfg rho hr s0 hs0 hΛ s1 hs1 v hv
      neu hneu =>
      have hkeys : RufFadenPasstG
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        have hhead : RufSchluesselG (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselG]
        have hk : RufFadenSchluesselG (M.faeden f) =
            RufSchluesselG (M.faeden f).kopf ::
              ((caller :: rest).map RufSchluesselG) := by
          have e : RufFadenSchluesselG (M.faeden f) =
              RufSchluesselG (M.faeden f).kopf ::
                ((M.faeden f).stapel.map RufSchluesselG) := by
            simp [RufFadenSchluesselG]
          rw [e, hpop]
        have htail : RufFadenSchluesselG
            (⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
              RufFadenG D) =
            (caller :: rest).map RufSchluesselG := by
          simp [RufFadenSchluesselG]
        unfold RufFadenPasstG at h ⊢
        rw [hk, hhead] at h
        rw [htail]
        exact RufLogPasstG.rueck _ _ g rho s0 v s1 h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho
      neu hneu =>
      have hkeys : RufFadenPasstG
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        have e : RufFadenSchluesselG
            (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
                ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenG D) =
            (⟨g, rho, s0⟩ :
              Σ f : D.Fn, Env D (D.params f) × World D) ::
              RufFadenSchluesselG (M.faeden f) := by
          simp [RufFadenSchluesselG, RufSchluesselG]
        unfold RufFadenPasstG
        rw [e]
        exact RufLogPasstG.eintritt _ _ g rho s0 h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv
      rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv
      rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0
      rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0
      hs0 g hg hv rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0
      hs0 rho hrho neu hneu =>
      have hkeys := rufPushG_passt (M.faeden f)
        ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
         ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩
        ⟨g, rho, s0,
         ⟨false, D.params g, Signatur.anfang D (D.signatur g),
          rho, .ende (P.rumpf g)⟩⟩
        rfl g rho s0 rfl s0.spur h
      have heq : (⟨M.speicher,
          rufUpdateG M.faeden f
            ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
               ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ ::
               (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩ ::
              (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, .ende (P.rumpf g)⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rueckBind caller rest hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ
      hh g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      have hhead : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeyNeu : RufSchluesselG
          (⟨caller.f, caller.rho, caller.s0,
            ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
             .dann restb (.schrumpf k)⟩⟩ : RufRahmenG D) =
          RufSchluesselG caller := by
        simp [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rest hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
          .dann restb (.schrumpf k)⟩⟩
        hkeyNeu g rho v s0 s1 hhead s1.spur h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rest,
             ⟨caller.f, caller.rho, caller.s0,
              ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
               .dann restb (.schrumpf k)⟩⟩,
             s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rest,
           ⟨caller.f, caller.rho, caller.s0,
            ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc,
             .dann restb (.schrumpf k)⟩⟩,
           s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1
      g hfg rho hrho s0 hs0 v hv neu hneu =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rst hpop caller rfl
        g rho v s0 s1 hheadkey s1.spur h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rst, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rst, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hh g hfg rho hrho s0 hs0
      hΛ s1 hs1 v hv neu hneu =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rst hpop caller rfl
        g rho v s0 s1 hheadkey s1.spur h
      have heq : (⟨s1.speicher,
          rufUpdateG M.faeden f
            ⟨rst, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenG f neu,
          M.start⟩ : RufMaschineG D).faeden f =
          (⟨rst, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenG D) := by
        simp [rufUpdateG_self]
      rw [heq]
      exact hkeys
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hh caller rst hpop l Γ Λ Λ' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rst hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩
        (by simp [RufSchluesselG]) g rho v s0 s1 hheadkey s1.spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | rueckConsBind lk Γk Λk e hperm restk ρ hh caller rst hpop l Γ Λ Λ' τ restb
      k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopG_passt (M.faeden f) caller rst hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩
        (by simp [RufSchluesselG]) g rho v s0 s1 hheadkey s1.spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | rueckGrund r hperm ρ hh caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopGrundG_passt (M.faeden f) caller rst hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc, .ende err⟩⟩
        (by simp [RufSchluesselG]) g rho rg s0 (M.weltVon f) hheadkey (M.faeden f).spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | rueckConsGrund r hperm restk ρ hh caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopGrundG_passt (M.faeden f) caller rst hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc, .ende err⟩⟩
        (by simp [RufSchluesselG]) g rho rg s0 (M.weltVon f) hheadkey (M.faeden f).spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | dannRetGrund r hperm restk kk ρ hh caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      have hheadkey : RufSchluesselG (M.faeden f).kopf =
          (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
        cases hfg
        simp_all [RufSchluesselG]
      have hkeys := rufPopGrundG_passt (M.faeden f) caller rst hpop
        ⟨caller.f, caller.rho, caller.s0,
         ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc, .ende err⟩⟩
        (by simp [RufSchluesselG]) g rho rg s0 (M.weltVon f) hheadkey (M.faeden f).spur h
      simp only [rufUpdateG_self]
      exact hkeys
  | _ =>
      simp only [rufUpdateG_self]
      exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h

/-- One step preserves the invariant at an UNTOUCHED thread: the
    result machine's thread state equals the old one. `hne` selects the
    untouched side and is consumed by the simp set. -/
theorem rufSchrittG_passt_anders (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f f' : Faden) (hne : f' ≠ f)
    (hs : RufSchrittG P O passes M f M') :
    M'.faeden f' = M.faeden f' := by
  cases hs <;> (simp_all [rufUpdateG_noteq])

/-- One step preserves the invariant for EVERY thread. Both `hact`
    (acting side) and the untouched side feed the conclusion; `hne`
    selects the side. -/
theorem rufSchrittG_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) (f : Faden)
    (h : RufMaschinePasstG M)
    (hs : RufSchrittG P O passes M f M') :
    RufMaschinePasstG M' := by
  intro f'
  by_cases hne : f' = f
  · subst hne
    exact rufSchrittG_passt_acting P O passes M M' f' (h f') hs
  · rw [rufSchrittG_passt_anders P O passes M M' f f' hne hs]
    exact h f'

/-- The invariant holds at every reachable machine. Both `hbase` (start
    evidence) and the step evidence feed the conclusion. -/
theorem rufErreichbarG_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) :
    RufMaschinePasstG M := by
  induction h with
  | start => exact rufStartG_passt P sp init
  | schritt M M' f hbase hs ih =>
      exact rufSchrittG_passt P O passes M M' f ih hs

/-- **Return fidelity.** Every `rueck` event in a reachable thread log has
    its matching `eintritt` event in the same log. Every premise is used:
    `h` selects the reachable machine, `hmem` the log event. -/
theorem rufG_treu (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D)
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (f : Faden) :
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log →
      RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  have hmach := rufErreichbarG_passt P O passes sp init M h
  have hthread := hmach f
  unfold RufFadenPasstG at hthread
  have hged := rufLogPasstG_gedeckt (RufFadenSchluesselG (M.faeden f))
    (M.faeden f).log hthread
  unfold rufRueckGedecktG at hged
  intro g rho v s0 s1 hmem
  exact hged g rho v s0 s1 hmem

/-! ## 6a. No head ever waits: the deadlock of the verbatim pops is gone

    A waiting residue (`wartet`/`wartetSonst`) is created only in a PUSHED
    caller frame, and only a binding pop resumes it; the verbatim pops
    (`rueck`, `rueckCons`, `dannRet`) now demand a caller that does not
    wait (`hnw`). So the invariant "the head residue contains no waiting
    node, and every stacked residue is either clean or waits over a clean
    continuation" holds at the start and is kept by every rule; in
    particular no reachable head is a waiting residue (`rufG_nie_wartend`),
    the state in which only the bare lock steps could fire. -/

/-- A residue with no waiting node anywhere along its continuation. -/
def GRest.sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende _ => true
  | .dann _ k => k.sauber
  | .schrumpf k => k.sauber
  | .frei _ k => k.sauber
  | .trav _ _ _ _ k => k.sauber
  | .travRest _ _ _ _ k => k.sauber
  | .wieder _ _ _ _ k => k.sauber
  | .wiederRest _ _ _ _ k => k.sauber
  | .ewig _ _ _ _ k => k.sauber
  | .ewigRest _ _ _ _ k => k.sauber
  | .wartet _ _ => false
  | .wartetSonst _ _ _ _ => false
  | .abbruch k => k.sauber

/-- A stacked residue: clean, or waiting over a clean continuation. -/
def GRest.stapelSauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .wartet _ k => k.sauber
  | .wartetSonst _ _ _ k => k.sauber
  | r => r.sauber

theorem GRest.sauber_wartend {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} (h : r.sauber = true) : r.wartend = false := by
  cases r <;> simp_all [GRest.sauber, GRest.wartend]

theorem GRest.stapelSauber_sauber {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : GRest D V l Γ Λ} (hw : r.wartend = false) (h : r.stapelSauber = true) :
    r.sauber = true := by
  cases r <;> simp_all [GRest.sauber, GRest.stapelSauber, GRest.wartend]

/-- The thread invariant: a clean head, clean-or-waiting stacked frames. -/
def RufFadenSauberG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.sauber = true ∧ ∀ r ∈ z.stapel, r.rest.2.2.2.2.stapelSauber = true

/-- The invariant implies a head that does not wait. -/
theorem RufFadenSauberG.kopf_wartend {z : RufFadenG D} (h : RufFadenSauberG z) :
    z.kopf.wartend = false :=
  GRest.sauber_wartend h.1


end Gabbro.Grammatik
