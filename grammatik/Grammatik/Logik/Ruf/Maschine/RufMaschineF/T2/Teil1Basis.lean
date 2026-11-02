module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineF.T1

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- One step preserves the invariant for the ACTING thread.
    `blatt`/`nimmt`/`gibt` keep the key stack (the residue moves, the key
    does not) and the log; `ruf` pushes the callee key with its entry event;
    `rueck` pops the head key with its return event. Every premise of the
    step is used: `hhead`/`hΛ` fix the firing frame, `hstep`/`hrho`/`hv`
    the computed data, `hpop`/`hfg`/`hrho`/`hs0` the popped frame identity,
    `hneu`/`hs0`/`hs1` the trace threading. -/
theorem rufSchrittF_passt_acting (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f : Faden)
    (h : RufFadenPasstF (M.faeden f))
    (hs : RufSchrittF P O passes M f M') :
    RufFadenPasstF (M'.faeden f) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel,
           ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
            ⟨l, Γ, Λ', ρ', rest⟩⟩,
           σ'.spur, (M.faeden f).log⟩ : RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel,
             ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, Λ', ρ', rest⟩⟩,
             σ'.spur, (M.faeden f).log⟩ : RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons, RufSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨σ'.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel,
             ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
              ⟨l, Γ, Λ', ρ', rest⟩⟩,
             σ'.spur, (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu, M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel,
           ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
            ⟨l, Γ, Λ', ρ', rest⟩⟩,
           σ'.spur, (M.faeden f).log⟩ : RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | nimmt L hself hrang hfrei =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
           (M.faeden f).log⟩ : RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
             (M.faeden f).log⟩ : RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
             (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f [Ereignis.nimmt L (offen (M.faeden f).spur)],
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.nimmt L (offen (M.faeden f).spur) :: (M.faeden f).spur,
           (M.faeden f).log⟩ : RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | gibt L hhaelt =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
            RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
              RufFadenF D) =
            RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons]
        unfold RufFadenPasstF
        rw [e]
        exact h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).stapel, (M.faeden f).kopf,
             Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f [Ereignis.gibt L], M.start⟩ :
          RufMaschineF D).faeden f =
          (⟨(M.faeden f).stapel, (M.faeden f).kopf,
           Ereignis.gibt L :: (M.faeden f).spur, (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      have hkeys : RufFadenPasstF
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, P.rumpf g⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        have e : RufFadenSchluesselF
            (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, P.rumpf g⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
              RufFadenF D) =
            (⟨g, rho, s0⟩ :
              Σ f : D.Fn, Env D (D.params f) × World D) ::
              RufFadenSchluesselF (M.faeden f) := by
          simp only [RufFadenSchluesselF, List.map_cons, RufSchluesselF]
        unfold RufFadenPasstF
        rw [e]
        exact RufLogPasstF.eintritt _ _ g rho s0 h
      have heq : (⟨M.speicher,
          rufUpdateF M.faeden f
            ⟨(M.faeden f).kopf :: (M.faeden f).stapel,
             ⟨g, rho, s0,
              ⟨false, D.params g, Signatur.anfang D (D.signatur g),
               rho, P.rumpf g⟩⟩,
             s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu,
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨(M.faeden f).kopf :: (M.faeden f).stapel,
           ⟨g, rho, s0,
            ⟨false, D.params g, Signatur.anfang D (D.signatur g),
             rho, P.rumpf g⟩⟩,
           s0.spur, (RufEreignisF.eintritt g rho s0) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys
  | rueck caller rest hpop Γ Λ e hperm ρ hh g hfg rho hr s0 hs0 hΛ s1 hs1 v hv neu hneu =>
      have hkeys : RufFadenPasstF
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        have hhead : RufSchluesselF (M.faeden f).kopf =
            (⟨g, rho, s0⟩ : Σ f : D.Fn, Env D (D.params f) × World D) := by
          cases hfg
          simp_all [RufSchluesselF]
        have hk : RufFadenSchluesselF (M.faeden f) =
            RufSchluesselF (M.faeden f).kopf ::
              ((caller :: rest).map RufSchluesselF) := by
          have e : RufFadenSchluesselF (M.faeden f) =
              RufSchluesselF (M.faeden f).kopf ::
                ((M.faeden f).stapel.map RufSchluesselF) := by
            simp only [RufFadenSchluesselF, List.map_cons]
          rw [e, hpop]
        have htail : RufFadenSchluesselF
            (⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
              RufFadenF D) =
            (caller :: rest).map RufSchluesselF := by
          simp only [RufFadenSchluesselF, List.map_cons]
        unfold RufFadenPasstF at h ⊢
        rw [hk, hhead] at h
        rw [htail]
        exact RufLogPasstF.rueck _ _ g rho s0 v s1 h
      have heq : (⟨s1.speicher,
          rufUpdateF M.faeden f
            ⟨rest, caller, s1.spur,
             (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩,
          M.lauf ++ rufEigenF f neu,
          M.start⟩ : RufMaschineF D).faeden f =
          (⟨rest, caller, s1.spur,
           (RufEreignisF.rueck g rho v s0 s1) :: (M.faeden f).log⟩ :
            RufFadenF D) := by
        simp only [rufUpdateF_self]
      rw [heq]
      exact hkeys

/-! ## 7. Preservation for all threads, reachability, the target -/

/-- One step preserves the invariant at an UNTOUCHED thread: the
    result machine's thread state equals the old one, since `rufUpdateF`
    only replaces the acting thread. Proved by case split on `hs` with
    `subst_vars` (learning `M'`'s shape) and `rufUpdateF_noteq`.
    `hne` selects the untouched side and is consumed by the simp set. -/
theorem rufSchrittF_passt_anders (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f f' : Faden) (hne : f' ≠ f)
    (hs : RufSchrittF P O passes M f M') :
    M'.faeden f' = M.faeden f' := by
  cases hs <;> (subst_vars; simp_all [rufUpdateF_noteq])

/-- One step preserves the invariant for EVERY thread: the acting thread by
    the case split above, every other thread by `rufSchrittF_passt_anders`.
    Both `hact` (acting side) and `hoth` (other side) feed the conclusion;
    `hne` selects the side. -/
theorem rufSchrittF_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineF D) (f : Faden)
    (h : RufMaschinePasstF M)
    (hs : RufSchrittF P O passes M f M') :
    RufMaschinePasstF M' := by
  intro f'
  by_cases hne : f' = f
  · subst hne
    exact rufSchrittF_passt_acting P O passes M M' f' (h f') hs
  · rw [rufSchrittF_passt_anders P O passes M M' f f' hne hs]
    exact h f'

/-- The invariant holds at every reachable machine: induction on `h`, with
    the start case by `rufStartF_passt` and the step case by
    `rufSchrittF_passt`. Both `hbase` (start evidence) and `hstep` (step
    evidence) feed the conclusion. -/
theorem rufErreichbarF_passt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineF D)
    (h : RufErreichbarF P O passes (RufStartF P sp init) M) :
    RufMaschinePasstF M := by
  induction h with
  | start => exact rufStartF_passt P sp init
  | schritt M M' f hbase hs ih =>
      exact rufSchrittF_passt P O passes M M' f ih hs

/-- **Return fidelity.** Every `rueck` event in a reachable thread log has
    its matching `eintritt` event in the same log. Proved by induction on
    `h` through the invariant: `rufErreichbarF_passt` gives the well-formed
    log, `rufLogPasstF_gedeckt` reads the match off it. Every premise is
    used: `h` selects the reachable machine, `hmem` the log event. -/
theorem rufF_treu (P : Programm D) (O : Orakel D) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineF D)
    (h : RufErreichbarF P O passes (RufStartF P sp init) M) (f : Faden) :
    ∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufEreignisF.rueck g rho v s0 s1 ∈ (M.faeden f).log →
      RufEreignisF.eintritt g rho s0 ∈ (M.faeden f).log := by
  have hmach := rufErreichbarF_passt P O passes sp init M h
  have hthread := hmach f
  unfold RufFadenPasstF at hthread
  have hged := rufLogPasstF_gedeckt (RufFadenSchluesselF (M.faeden f))
    (M.faeden f).log hthread
  unfold rufRueckGedecktF at hged
  intro g rho v s0 s1 hmem
  exact hged g rho v s0 s1 hmem


end Gabbro.Grammatik
