module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
public import Grammatik.Nebenlaeufigkeit.Allgemein.MehrfadenZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- `hauptA`: `ensures privA[0] == 7` from the two writes (the lock's move
    and the callees' frames leave `privA` alone); the caller duty of both
    calls from the lock invariant at the acquire and from the frames; no
    `logik` outcome because the release check follows from `setze`'s
    `ensures`. -/
theorem mP_koerper_A : KoerperGutS mP 0 (axWahr mD) mSI mHauptA := by
  have hr : mP.rumpf mHauptA = mRumpfA := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    have h := (mA_lauf hU hR σ ρ hrun).1
    show decide ((σ'.slots MTab.privA 0 ()).n = 7) = true
    simp only [h, decide_true]
  · rw [hr] at hrun
    obtain ⟨σ2, e2, h20, _⟩ := mA_schreib (S := mSI) (O := O') (U := U) (passes := 0)
      (R := torRuf mP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hU2 : (U () σ2).slots MTab.privA = σ2.slots MTab.privA :=
      (hU () σ2).2.1 (.inl MTab.privA) (fun h => by have := List.mem_singleton.mp h; cases this)
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m30 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    have htor : ∀ w a, ReqAmEintritt mP mSetze w a → torRuf mP R mSetze w a = R mSetze w a :=
      fun _ _ h => if_pos h
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := torRuf mP R)
      (l := false) (Γ := []) mSetze (.cons m30 .nil) mHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hR1' := (htor _ _ hreq).symm.trans hR1
      have hf1 := (hR.2 _ _ _ _ _ hR1').1.1 MTab.privA rfl
      cases hi : mSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true =>
        simp only [freiH, hi, if_true] at hrun
        simp only [mRestA, execEndH] at hrun
        have e0 : ((σ1.gibt ()).lese [] []).slots MTab.privA 0 () = σ2.slots MTab.privA 0 () :=
          (hf1 0 ()).trans (congrFun (congrFun hU2 0) ())
        have hreq3 : ReqAmEintritt mP mPruefeA ((σ1.gibt ()).lese [] []) .nil :=
          mA_req (by rw [e0]; exact h20)
        rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := torRuf mP R)
          (l := false) (Γ := []) mPruefeA .nil mHpPruefe rfl (σ1.gibt ()) ρ with
          ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
        · cases hrun
        · cases hrun
          have htor3 : torRuf mP R mPruefeA ((σ1.gibt ()).lese [] []) .nil =
              R mPruefeA ((σ1.gibt ()).lese [] []) .nil := if_pos hreq3
          exact hOV _ _ _ _ (htor3.symm.trans he3) g rfl
        · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOV _ _ _ _ ((htor _ _ hreq).symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2, _, _⟩ := mA_schreib (S := mSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksA] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m30 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) mSetze (.cons m30 .nil) mHpSetzeA rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := mInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      simp only [mRestA, execEndH] at hrun
      rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := R)
        (l := false) (Γ := []) mPruefeA .nil mHpPruefe rfl (σ1.gibt ()) ρ with
        ⟨σ3, v3, hR3, h3⟩ | ⟨e3, he3, h3⟩ | ⟨e3, h3⟩ <;> erw [h3] at hrun
      · cases hrun
      · cases hrun
        exact hOL _ _ _ _ he3
      · cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

/-- `hauptA` owes the invariant `privA[0] == privA[1]` and meets it. -/
theorem mP_inv_A : InvGutS mP 0 (axWahr mD) mSI mHauptA := by
  intro O' _ _ _ U hU R hR _ σ ρ _ σ' v hrun i _ _
  have hr : mP.rumpf mHauptA = mRumpfA := rfl
  rw [hr] at hrun
  have h := mA_lauf hU hR σ ρ hrun
  cases i
  show decide ((σ'.slots MTab.privA 0 ()).n = (σ'.slots MTab.privA 1 ()).n) = true
  simp only [h.1, h.2, decide_true]

theorem mB_schreib {S : SperrInv mD} {O : Orakel mD} {U : Umwelt mD} {passes : Nat}
    {R : ∀ f : mD.Fn, World mD → Env mD (mD.params f) → RufAusgang f} (σ : World mD)
    (ρ : Env mD (mD.params mHauptB)) :
    ∃ σ2 : World mD, execEndH S O U passes R mRumpfB σ ρ =
        execEndH S O U passes R (.cons mLocksB (.ret .empty List.Perm.nil)) σ2 ρ :=
  ⟨_, rfl⟩

/-- `hauptB`: the caller duty from the lock invariant at the acquire; the
    release check from `setze`'s `ensures`. -/
theorem mP_koerper_B : KoerperGutS mP 0 (axWahr mD) mSI mHauptB := by
  have hr : mP.rumpf mHauptB = mRumpfB := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := mB_schreib (S := mSI) (O := O') (U := U) (passes := 0)
      (R := torRuf mP R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m70 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := torRuf mP R)
      (l := false) (Γ := []) mSetze (.cons m70 .nil) mHpSetzeB rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hi : mSI.inv () σ1.speicher with
      | false => simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun; cases hrun
      | true => simp only [freiH, hi, if_true] at hrun; cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have htor : torRuf mP R mSetze _ _ = R mSetze _ _ := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun; cases hrun
  · rw [hr] at hrun
    obtain ⟨σ2, e2⟩ := mB_schreib (S := mSI) (O := O') (U := U) (passes := 0) (R := R) σ ρ
    erw [e2] at hrun
    simp only [execEndH, mLocksB] at hrun
    erw [execStmtH_locks_eins] at hrun
    have hreq : ReqAmEintritt mP mSetze (((U () σ2).nimmt ()).lese mL [])
        (evalArgs (((U () σ2).nimmt ()).lese mL []) (Args.cons (Λ := mL) (Γ := []) m70 .nil)
          (((U () σ2).nimmt ()).lese mL []) ρ) := (hU () σ2).2.2
    rcases execStmtH_call_fall (S := mSI) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := []) mSetze (.cons m70 .nil) mHpSetzeB rfl ((U () σ2).nimmt ()) ρ with
      ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hinv := mInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun; cases hrun

theorem mP_koerper_setze : KoerperGutS mP 0 (axWahr mD) mSI mSetze := by
  have hr : mP.rumpf mSetze = mRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [mRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      show wahr? (eval σ (mP.ensures mSetze) _ (ergEnv (mD.erg mSetze) () (Env.cons x Env.nil))) = true
      simp only [wahr?, mSetze, mP, mGleich, mI0, Int.reduceSub, mI1, World.lese, World.merke, World.schreibSlot,
  World.storeSlot, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append, List.nil_append, ergEnv,
  Int.reduceEq, ↓reduceIte, dite_eq_ite, ite_self, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, rfl⟩
  · rw [hr] at hrun
    simp only [mRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [mRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun

theorem mP_koerper_leer (f : mD.Fn) (hf : f = mPruefeA ∨ f = mRuhe) :
    KoerperGutS mP 0 (axWahr mD) mSI f := by
  rcases hf with rfl | rfl <;>
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩ <;> cases hrun

theorem mP_koerper : ∀ f : mD.Fn, KoerperGutS mP 0 (axWahr mD) mSI f := by
  intro f
  cases f
  · exact mP_koerper_setze
  · exact mP_koerper_A
  · exact mP_koerper_B
  · exact mP_koerper_leer _ (Or.inl rfl)
  · exact mP_koerper_leer _ (Or.inr rfl)

theorem mP_inv : ∀ f : mD.Fn, InvGutS mP 0 (axWahr mD) mSI f := by
  intro f
  cases f
  · exact invGutS_ohne fun i _ => by cases i; rfl
  · exact mP_inv_A
  · exact invGutS_ohne fun i _ => by cases i; rfl
  · exact invGutS_ohne fun i _ => by cases i; rfl
  · exact invGutS_ohne fun i _ => by cases i; rfl


/-! ## 5. Every premise, jointly -/

def mO : Orakel mD where
  wirktL := fun a => nomatch a
  regLiesL := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g => nomatch g

theorem mO_gut : GutO mO := fun a => nomatch a

theorem mO_lokal : RegLokal mO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- The start memory: every slot zero. -/
def mSp : Speicher mD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

theorem mP_start : StartGut mP mSp mInit := by
  intro t
  unfold mInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

/-- No start function holds a lock by signature. -/
theorem mInit_leer : ∀ t, mD.haelt (mInit t).1 = [] := by
  intro t
  unfold mInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem mInit_exklusiv : StartExklusiv (D := mD) mInit := startExklusiv_ohne_haelt mInit mInit_leer

/-- No start function declares a reason. -/
theorem mInit_ohneGrund : StartOhneGrund (D := mD) mInit := by
  intro t
  unfold mInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem mSI_start : ∀ L, mSI.inv L mSp = true := fun _ => rfl

/-- No body of the witness contains a `forever` loop: its obligation at
    budget `0` is its obligation at every budget (`koerperGutS_alle`). -/
theorem mP_ohneEwig : ohneEwigB mP mFs = true := by decide

theorem mP_koerper_alle : ∀ (passes : Nat) (f : mD.Fn), KoerperGutS mP passes (axWahr mD) mSI f :=
  koerperGutS_alle mFs_voll mP_ohneEwig mP_koerper

theorem mP_inv_alle : ∀ (passes : Nat) (f : mD.Fn), InvGutS mP passes (axWahr mD) mSI f :=
  invGutS_alle mFs_voll mP_ohneEwig mP_inv

/-- **`mP_zertifiziert` -- every premise of the flagship
    `ziel_ort_mehrfaden_ende` holds on the two-writer program with private
    tables** (the obligations at EVERY `forever` budget), hence its
    conclusion on every reachable machine of every budget: contracts at
    every logged entry and return, the lock invariant of every free lock,
    no stop at a `logik` check, owed invariants at every logged return,
    and at every finished thread the start function's `ensures` and owed
    invariants. -/
theorem mP_zertifiziert : ∀ (passes : Nat) (M : RufMaschineG mD),
    RufErreichbarG mP mO passes (RufStartG mP mSp mInit) M →
      ((VertragAmOrtG mP M ∧ SperrInvG mSI M ∧ KeinLogikHaltG mO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG mP mO passes M t M') ∧
      InvAmOrtG mP M) ∧ StartEndeG mP M ∧ KeinStartGrundG M :=
  ziel_ort_mehrfaden_ende mP mO (axWahr mD) mSI mFs mSp mInit mK mO_gut mO_lokal
    (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
    mP_koerper_alle mP_start mSI_start mInit_exklusiv mP_inv_alle mInit_ohneGrund

/-- **`mP_verklemmungsfrei` -- every premise of the deadlock theorem holds
    on the witness**: on every reachable machine, if every unfinished thread
    waits for a lock another thread holds, every thread is finished. -/
theorem mP_verklemmungsfrei : ∀ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M →
      (∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t :=
  fun _ hr hW => keine_verklemmungG mO_gut mP_stufen mSp mInit mInit_leer [()]
    (fun L => by cases L; exact List.mem_singleton_self _) hr hW

/-- The rank invariant on every reachable machine of the witness. -/
theorem mP_rang : ∀ M : RufMaschineG mD,
    RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) M → ∀ t, RangInvG (mInit t).1 (M.faeden t) :=
  fun _ hr => rangInvG_erreichbar mO_gut mP_stufen mSp mInit
    (fun t => by rw [startSpur, mInit_leer t]; exact List.nodup_nil) hr

/-- `ziel_ort_mehrfaden` (without the completion conjunct) on the witness,
    over every budget. -/
theorem mP_mehrfaden : ∀ (passes : Nat) (M : RufMaschineG mD),
    RufErreichbarG mP mO passes (RufStartG mP mSp mInit) M →
      (VertragAmOrtG mP M ∧ SperrInvG mSI M ∧ KeinLogikHaltG mO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG mP mO passes M t M') ∧ InvAmOrtG mP M :=
  ziel_ort_mehrfaden mP mO (axWahr mD) mSI mFs mSp mInit mK mO_gut mO_lokal
    (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
    mP_koerper_alle mP_start mSI_start mInit_exklusiv mP_inv_alle

theorem sP_ohneEwig : ohneEwigB sP sFs = true := by decide

/-- `ziel_ort_sperre_ende` (the old footprint check, with the completion
    conjunct) on the earlier two-writer program `sP`, over every budget:
    the two-writer witness of §14.5 carries over. -/
theorem sP_ende_zertifiziert : ∀ (passes : Nat) (M : RufMaschineG sD),
    RufErreichbarG sP sO passes (RufStartG sP sSp sInit) M →
      ((VertragAmOrtG sP M ∧ SperrInvG sS M ∧ KeinLogikHaltG sO passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG sP sO passes M t M') ∧ InvAmOrtG sP M) ∧
      StartEndeG sP M ∧ KeinStartGrundG M :=
  ziel_ort_sperre_ende sP sO (axWahr sD) sS sFs sSp sInit sO_gut sO_lokal
    (axVertragO_wahr sO) axEnsLokal_wahr sS_ok sFs_voll sP_fragmentG sP_fussS
    (koerperGutS_alle sFs_voll sP_ohneEwig sP_koerper) sP_start
    sS_start sInit_exklusiv (fun _ => invGutS_leer rfl) (fun _ => rfl)

#print axioms Gabbro.Grammatik.mP_mehrfaden
#print axioms Gabbro.Grammatik.sP_ende_zertifiziert
#print axioms Gabbro.Grammatik.mP_zertifiziert
#print axioms Gabbro.Grammatik.mP_verklemmungsfrei
#print axioms Gabbro.Grammatik.mP_fussMehr
#print axioms Gabbro.Grammatik.mP_fuss

end Gabbro.Grammatik
