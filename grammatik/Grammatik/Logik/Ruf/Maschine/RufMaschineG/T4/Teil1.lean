module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3

@[expose] public section



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
  | g1 hs =>
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
              simp only [RufFadenSchluesselG, List.map_cons]
            rw [e, hpop]
          have htail : RufFadenSchluesselG
              (⟨rest, caller, s1.spur,
               (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
                RufFadenG D) =
              (caller :: rest).map RufSchluesselG := by
            simp only [RufFadenSchluesselG, List.map_cons]
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
          simp only [rufUpdateG_self]
        rw [heq]
        exact hkeys
    | _ =>
        simp only [rufUpdateG_self]
        exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h
  | g2 hs =>
    cases hs with
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
            simp only [RufFadenSchluesselG, List.map_cons, RufSchluesselG]
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
          simp only [rufUpdateG_self]
        rw [heq]
        exact hkeys
    | _ =>
        simp only [rufUpdateG_self]
        exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h
  | g3 hs =>
    cases hs with
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
          simp only [rufUpdateG_self]
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
          simp only [rufUpdateG_self]
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
          simp only [rufUpdateG_self]
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
          simp only [rufUpdateG_self]
        rw [heq]
        exact hkeys
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0
        hs0 g hg hv rho hrho neu hneu =>
        have hkeys := rufPushG_passt (M.faeden f)
          ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
           ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩
          ⟨g, rho, s0,
           ⟨false, D.params g, Signatur.anfang D (D.signatur g),
            rho, .ende (P.rumpf g)⟩⟩
          rfl g rho s0 rfl s0.spur h
        have heq : (⟨M.speicher,
            rufUpdateG M.faeden f
              ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
                 ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩ ::
                 (M.faeden f).stapel,
               ⟨g, rho, s0,
                ⟨false, D.params g, Signatur.anfang D (D.signatur g),
                 rho, .ende (P.rumpf g)⟩⟩,
               s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
            M.lauf ++ rufEigenG f neu,
            M.start⟩ : RufMaschineG D).faeden f =
            (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
                ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err rest k⟩⟩ ::
                (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenG D) := by
          simp only [rufUpdateG_self]
        rw [heq]
        exact hkeys
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0
        hs0 g hg hv rho hrho neu hneu =>
        have hkeys := rufPushG_passt (M.faeden f)
          ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
           ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err .nil
             (.dann rest k)⟩⟩
          ⟨g, rho, s0,
           ⟨false, D.params g, Signatur.anfang D (D.signatur g),
            rho, .ende (P.rumpf g)⟩⟩
          rfl g rho s0 rfl s0.spur h
        have heq : (⟨M.speicher,
            rufUpdateG M.faeden f
              ⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
                 ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err .nil
                   (.dann rest k)⟩⟩ ::
                 (M.faeden f).stapel,
               ⟨g, rho, s0,
                ⟨false, D.params g, Signatur.anfang D (D.signatur g),
                 rho, .ende (P.rumpf g)⟩⟩,
               s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
            M.lauf ++ rufEigenG f neu,
            M.start⟩ : RufMaschineG D).faeden f =
            (⟨⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
                ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartetSonst (D.sigNr n).gruende err .nil
                  (.dann rest k)⟩⟩ ::
                (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, .ende (P.rumpf g)⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenG D) := by
          simp only [rufUpdateG_self]
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
          simp only [RufSchluesselG]
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
          simp only [rufUpdateG_self]
        rw [heq]
        exact hkeys
    | _ =>
        simp only [rufUpdateG_self]
        exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h
  | g4 hs =>
    cases hs with
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
          simp only [rufUpdateG_self]
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
          simp only [rufUpdateG_self]
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
          (by simp only [RufSchluesselG]) g rho v s0 s1 hheadkey s1.spur h
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
          (by simp only [RufSchluesselG]) g rho v s0 s1 hheadkey s1.spur h
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
          (by simp only [RufSchluesselG]) g rho rg s0 (M.weltVon f) hheadkey (M.faeden f).spur h
        simp only [rufUpdateG_self]
        exact hkeys
    | _ =>
        simp only [rufUpdateG_self]
        exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h
  | g5 hs =>
    cases hs with
    | rueckConsGrund =>
        rename_i ρ caller rst l Γ Λ Λ' τ n err restb k ρc hcaller g rho s0 rg hn r hperm restk hh hpop hΛ hfg hrho hs0 hrg
        have hheadkey : RufSchluesselG (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselG]
        have hkeys := rufPopGrundG_passt (M.faeden f) caller rst hpop
          ⟨caller.f, caller.rho, caller.s0,
           ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc, .ende err⟩⟩
          (by simp only [RufSchluesselG]) g rho rg s0 (M.weltVon f) hheadkey (M.faeden f).spur h
        simp only [rufUpdateG_self]
        exact hkeys
    | dannRetGrund =>
        rename_i ρ caller rst l Γ Λ Λ' τ n err restb k ρc hcaller g rho s0 rg hn r hperm restk kk hh hpop hΛ hfg hrho hs0 hrg
        have hheadkey : RufSchluesselG (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselG]
        have hkeys := rufPopGrundG_passt (M.faeden f) caller rst hpop
          ⟨caller.f, caller.rho, caller.s0,
           ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn rg) ρc, .ende err⟩⟩
          (by simp only [RufSchluesselG]) g rho rg s0 (M.weltVon f) hheadkey (M.faeden f).spur h
        simp only [rufUpdateG_self]
        exact hkeys
    | _ =>
        simp only [rufUpdateG_self]
        exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h
  | g6 hs =>
    cases hs with
    | _ =>
        simp only [rufUpdateG_self]
        exact rufFadenPasstG_behalte _ _ _ _ _ _ _ h

end Gabbro.Grammatik
