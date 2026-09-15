/-
  File:      Grammatik/ZielOrtSperre.lean
  Subject:   THE GOAL THEOREM WITH LOCK INVARIANTS -- `ziel_ort_sperre`.
             Contracts over shared state across a lock boundary, and readers
             inside `locks L { … }` blocks (verdict item 2,
             `messung/URTEIL-OPUS-2026-09-13.md`, probes B and C).

  The rule-by-rule step of the replay (`akteurS`, as `akteurR` in
  `ZielOrtRahmen.lean`) over the semantics with lock invariants, the rely,
  the start, the invariant on every reachable machine -- the replay, the
  machine lock invariant `SperrInvG` and the log -- and the theorem. The
  acquire step records the environment's move (`fadenS_locks`), fed by the
  machine lock invariant; the release steps (`fadenS_frei`,
  `fadenS_peelFrei`) use the second clause of the obligation, and give the
  machine lock invariant back (`kopfS_frei_inv`).
-/
import Grammatik.SperreMaschine

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- The residue of a frame, read off its rest. -/
theorem rest_okS {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (h : F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f)) :
    r.okS P (fussOrteG P F.f) (sicher P lok F.f) := by
  rw [hF] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **The acting thread keeps its replay and its log** -- every rule of G
    (as `akteurR`), over the semantics with lock invariants: the acquire by
    recording the environment's move (the machine lock invariant `SperrInvG`
    gives the invariant of the free lock), the releases by the second
    clause of the obligation. -/
theorem akteurS (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
    (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel)
    (hSG : SperrInvG S M) :
    FadenS P O passes Q S lok (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_blatt hO hQ hlok hFS hF hhead s (.ende rest)
      (fun O' R U σ => semH_ende_cons S O' U passes R s rest σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okS_ende_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_blatt hO hQ hlok hFS hF hhead s (.dann rest k)
      (fun O' R U σ => semH_dann_cons S O' U passes R s rest k σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okS_dann_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann (.cons s .nil) (.ende rest)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_ende_cons hok
    refine ⟨σ, Nat.le_refl _, hg, ⟨by simp [Block.gOk, hks], ?_, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_endeEntf S O' U passes R s rest σ ρ)⟩
    simpa [blockOrteP] using hss
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok.2.2, fun R O' U => ZErgG.folgt_refl _⟩
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann t (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨ht, _⟩ := and_teile hks
    obtain ⟨hc, htS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => expr_stabil (hFS _) c (fun _ h' => hc h') h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨ht, htS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_ite S O' U passes R c t e rest k σ ρ true hw')⟩
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann e (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨_, he⟩ := and_teile hks
    obtain ⟨hc, _, heS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => expr_stabil (hFS _) c (fun _ h' => hc h') h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨he, heS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_ite S O' U passes R c t e rest k σ ρ false hw')⟩
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons v ρ) (.dann p (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨hp, _⟩ := and_teile hks
    obtain ⟨hc, hpS, _⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v := by
      rw [eval_gleichAuf o (fun _ h => expr_stabil (hFS _) o (fun _ h' => hc h') h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨hp, hpS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_optSome S O' U passes R o p a rest k σ ρ v hv')⟩
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann a (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨_, ha⟩ := and_teile hks
    obtain ⟨hc, _, haS⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none := by
      rw [eval_gleichAuf o (fun _ h => expr_stabil (hFS _) o (fun _ h' => hc h') h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨ha, haS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_optNone S O' U passes R o p a rest k σ ρ hv')⟩
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
        ⟨some (lo, hi), b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => expr_stabil (hFS _) v (fun _ h' => hss.1 h') h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_gOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_tagSome S O' U passes R v arms rest k σ ρ lo hi b nutz hw')⟩
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (armEnv nutz ρ) (.dann b (.dann rest k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => expr_stabil (hFS _) v (fun _ h' => hss.1 h') h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_gOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_tagNone S O' U passes R v arms rest k σ ρ b nutz hw')⟩
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann b (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hb : grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ) = b := by
      rw [eval_gleichAuf r (fun _ h => expr_stabil (hFS _) r (fun _ h' => hss.1 h') h) (hg.lese Λ Λ r.orte r.orte) ρ, ← hs₁]; exact hw
    refine ⟨σ.lese Λ r.orte, lese_laenge _ _ _, hg, ⟨?_, ?_, hrest⟩, fun R O' U => ?_⟩
    · rw [← hb]; exact grundWahlG_gOk arms _ hks
    · rw [← hb]; exact fun _ h => hss.2 (grundWahlG_orteP arms _ h)
    · rw [← hb]; exact ZErgG.folgt_of_eq (semH_grund S O' U passes R r arms rest k σ ρ)
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.ende rest) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss⟩ := hok
    simp only [endblockOrteP, List.append_subset] at hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hss.1 h') h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2⟩, fun R O' U => ?_⟩
    have h1 := semH_endeBind S O' U passes R e rest σ ρ
    rw [he'] at h1
    exact ZErgG.folgt_of_eq h1
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hss.1 h') h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩, fun R O' U => ?_⟩
    have h1 := semH_dannBind S O' U passes R e rest k σ ρ
    rw [he'] at h1
    exact ZErgG.folgt_of_eq h1
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead _ (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hes, _, hrS⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hes h') h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := by rw [he']; exact h
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩, fun R O' U => ?_⟩
    have h1 := semH_narrowOk S O' U passes R e lo' hi' sonst rest k σ ρ h'
    have hz : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h'.1, h'.2⟩ :
        Wert D (.int lo' hi')) = ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ := by
      simp only [he']
    rw [hz] at h1
    exact ZErgG.folgt_of_eq h1
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hes h') h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') := by rw [he']; exact h
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, okS_alsBlock sonst k rest.held_iff hkS hsS hrk,
      fun R O' U => semH_narrowElse S O' U passes R e lo' hi' sonst rest k σ ρ h'⟩
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann rest k) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hc, _, hrS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => expr_stabil (hFS _) c (fun _ h' => hc h') h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_pruefWahr S O' U passes R c sonst rest k σ ρ hw')⟩
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hc, hsS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => expr_stabil (hFS _) c (fun _ h' => hc h') h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, okS_alsBlock sonst k rest.held_iff hkS hsS hrk,
      fun R O' U => semH_pruefFalsch S O' U passes R c sonst rest k σ ρ hw'⟩
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_breaking S O' U passes R i body rest k σ ρ)⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hinv : S.inv L (M.weltVon u).speicher = true := by
      show S.inv L M.speicher = true
      refine hSG L fun t => ?_
      by_cases htu : t = u
      · subst htu
        exact hself
      · exact hfrei t htu
    exact ⟨fadenS_locks hF L hr body rest k ρ hhead hinv _, hL⟩
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenS_frei hO hRL hQ hS hsp hK hF L k ρ hhead _, hL⟩
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok, fun R O' U => ZErgG.folgt_refl _⟩
  -- loops
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.trav t inv body (alleIndizes (D.count t)) (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_dannTrav S O' U passes R t inv body rest k σ ρ)⟩
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons i ρ) (.dann body (.travRest t inv body is k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hinv h') h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hinv, hb, hbS, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_travNext S O' U passes R t inv body i is k σ ρ hw')⟩
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' U => ZErgG.folgt_of_eq (semH_travFort S O' U passes R t inv body is k i σ ρ)⟩
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ k σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, _, _, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hinv h') h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, hk,
      fun R O' U => ZErgG.folgt_of_eq (semH_travDone S O' U passes R t inv body k σ ρ hw')⟩
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.wieder n bis body ueber (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨hb, hu⟩ := and_teile hks
    obtain ⟨hbis, hbS, huS⟩ := teile2 hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hbis, hb, hbS, hu, huS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_dannRetry S O' U passes R n bis body ueber rest k σ ρ)⟩
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann (.cons (.ite bis .nil ueber) .nil) k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbS, _, _, hu, huS, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨by simp_all [Block.gOk, Stmt.gOk],
      fun x hx => by
        simp only [blockOrteP, stmtOrteP, List.append_nil, List.mem_append] at hx
        rcases hx with h | h <;> first | exact hbS h | exact huS h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_wiederUeber S O' U passes R bis body ueber k σ ρ)⟩
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ k σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, _, _, _, _, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true := by
      rw [eval_gleichAuf bis (fun _ h => expr_stabil (hFS _) bis (fun _ h' => hbis h') h) (hg.lese Λ Λ bis.orte bis.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ bis.orte, lese_laenge _ _ _, hg, hk,
      fun R O' U => ZErgG.folgt_of_eq (semH_wiederWeiter S O' U passes R n bis body ueber k σ ρ hw')⟩
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann body (.wiederRest n bis body ueber k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, hb, hbS, hu, huS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
      rw [eval_gleichAuf bis (fun _ h => expr_stabil (hFS _) bis (fun _ h' => hbis h') h) (hg.lese Λ Λ bis.orte bis.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ bis.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hbis, hb, hbS, hu, huS, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_wiederSchritt S O' U passes R n bis body ueber k σ ρ hw')⟩
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' U => ZErgG.folgt_of_eq (semH_wiederFort S O' U passes R n bis body ueber k σ ρ)⟩
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.ewig a passes inv body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_dannForever S O' U passes R a inv body rest k σ ρ)⟩
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann body (.ewigRest a n inv body k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hinv h') h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hinv, hb, hbS, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_ewigWeiter S O' U passes R a n inv body k σ ρ hw')⟩
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' U => ZErgG.folgt_of_eq (semH_ewigFort S O' U passes R a n inv body k σ ρ)⟩
  -- the exits
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    subst hs₁
    refine ⟨fadenS_lokal hF hhead ρ k _ (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    obtain ⟨hinv, _, _, hk⟩ := hTR
    have hg' := gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hinv h') h)
        (hg'.lese Λ Λ inv.orte inv.orte) ρ]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg', hk,
      fun R O' U => ZErgG.folgt_of_eq
        (semH_leaveTrav S O' U passes R t inv body is k rest i σ ρ hleave hw')⟩
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hTR,
      fun R O' U => ZErgG.folgt_of_eq (semH_nextTrav S O' U passes R t inv body is k rest i σ ρ hnext)⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    obtain ⟨_, _, _, _, _, hk⟩ := hWR
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
      fun R O' U => ZErgG.folgt_of_eq
        (semH_leaveWieder S O' U passes R n bis body ueber k rest σ ρ hleave)⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hWR,
      fun R O' U => ZErgG.folgt_of_eq
        (semH_nextWieder S O' U passes R n bis body ueber k rest σ ρ hnext)⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    obtain ⟨_, _, _, hk⟩ := hER
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
      fun R O' U => ZErgG.folgt_of_eq (semH_leaveEwig S O' U passes R a n inv body k rest σ ρ hleave)⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenS_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hER,
      fun R O' U => ZErgG.folgt_of_eq (semH_nextEwig S O' U passes R a n inv body k rest σ ρ hnext)⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _,
      gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelDann S O' U passes R rest b k σ ρ hleave true)⟩
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _,
      gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelDann S O' U passes R rest b k σ ρ hnext false)⟩
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelSchrumpf S O' U passes R rest k σ ρ hleave true)⟩
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelSchrumpf S O' U passes R rest k σ ρ hnext false)⟩
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenS_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hleave true hhead _, hL⟩
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenS_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hnext false hhead _, hL⟩
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hiff, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _,
      gleichAuf_stabil_iff (fun L => (hiff L).trans (Block.held_iff rest L)) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelAbbruch S O' U passes R rest k σ ρ hleave true)⟩
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hiff, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _,
      gleichAuf_stabil_iff (fun L => (hiff L).trans (Block.held_iff rest L)) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_peelAbbruch S O' U passes R rest k σ ρ hnext false)⟩
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.cons_subset, List.append_subset] at hss
    obtain ⟨⟨hgS, hnS⟩, hrS⟩ := hss
    subst hs₂ hs₁
    have hgl := hg.lese Λ Λ (.inr g :: neuE.orte) (.inr g :: neuE.orte)
    have hglob : (σ.lese Λ (.inr g :: neuE.orte)).globs g =
        ((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g := hgl.2 g (stabil_of_fuss (hFS _) hgS fun L hB => bewacht_held (c := .inr g) hLg hB)
    have hval : eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
        (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
        eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) :=
      eval_gleichAuf neuE (fun _ h => expr_stabil (hFS _) neuE (fun _ h' => hnS h') h) hgl _
    refine ⟨(σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
        (eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ)),
      spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _)),
      gleichAuf_schreibGlob hgl g Λ Λ _, ⟨hks, hrS, hrest⟩, fun R O' U => ?_⟩
    have h1 := semH_exchange S O' U passes R g neuE hw hLg rest k σ ρ
    rw [hglob, hval] at h1
    exact ZErgG.folgt_of_eq h1
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨haS, hbS, hrS⟩ := teile2 hss
    have hgl := hg.lese Λ Λ (a.orte ++ b.orte) (a.orte ++ b.orte)
    have hv' : gleitPasst lo hi (gleitRechne op
        (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
        (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v := by
      rw [eval_gleichAuf a (fun _ h => expr_stabil (hFS _) a (fun _ h' => haS h') h) hgl ρ, eval_gleichAuf b (fun _ h => expr_stabil (hFS _) b (fun _ h' => hbS h') h) hgl ρ,
        ← hs₁]
      exact hv
    exact ⟨σ.lese Λ (a.orte ++ b.orte), lese_laenge _ _ _, hg, ⟨hks, hrS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_gleit S O' U passes R op a b lo hi rest k σ ρ v hv')⟩
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_gleitLit S O' U passes R q lo hi rest k σ ρ v hv)⟩
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have hv' : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
        (σ.lese Λ e.orte) ρ).n) = some v := by
      rw [eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hss.1 h') h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_gleitVon S O' U passes R e lo hi rest k σ ρ v hv')⟩
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hes, _, hrS⟩ := teile2 hss
    have hv' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v := by
      rw [eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hes h') h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R O' U => ZErgG.folgt_of_eq (semH_gleitNarrowOk S O' U passes R e lo hi sonst rest k σ ρ v hv')⟩
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have hn' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none := by
      rw [eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => hes h') h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hn
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, okS_alsBlock sonst k rest.held_iff hkS hsS hrk,
      fun R O' U => semH_gleitNarrowElse S O' U passes R e lo hi sonst rest k σ ρ hn'⟩
  -- the axiom bind
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have e2 : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
      have := congrArg Prod.fst hax
      simp only [axiomAntwort] at this
      exact this.symm
    have hv : einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).2 = some v := by
      have := congrArg Prod.snd hax
      simp only [axiomAntwort] at this
      exact this
    have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
    rw [← e2] at hfr
    subst hs₁
    refine ⟨fadenS_ax hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => ⟨hok.1, by simpa [blockOrteP] using (teil_append hok.2.1).2, hok.2.2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ) = _
    simp only [execBlockH, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rfl
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact vertrag_stabil (hFS _) g hp (List.append_subset.mpr hss.2))
      (fun hok σ hgσ => by
        obtain ⟨_, hss, _⟩ := okS_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact evalArgs_gleichAuf args (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.1 h') h)
          (hgσ.lese Λ Λ _ _) ρ)
      ρ (.ende rest) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_ende_cons hok).2.2)
      (fun O' U R σ e _ h => by
        rw [semH_ende_cons]
        simp only [execStmtH, h]
        rfl)
      (fun O' U R σ _ => by
        rw [semH_ende_cons]
        simp only [execStmtH]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            exact ⟨fun _ => ZErgG.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact vertrag_stabil (hFS _) g hp (List.append_subset.mpr hss.2))
      (fun hok σ hgσ => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact evalArgs_gleichAuf args (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.1 h') h)
          (hgσ.lese Λ Λ _ _) ρ)
      ρ (.dann rest k) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_dann_cons hok).2.2)
      (fun O' U R σ e _ h => by
        rw [semH_dann_cons]
        simp only [execStmtH, h]
        exact weiterH_logik S O' U passes R _ e)
      (fun O' U R σ _ => by
        rw [semH_dann_cons]
        simp only [execStmtH]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            exact ⟨fun _ => ZErgG.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact vertrag_stabil (hFS _) g hp (List.append_subset.mpr hss.1.2))
      (fun hok σ hgσ => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact evalArgs_gleichAuf args
          (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.1.1 h') h) (hgσ.lese Λ Λ _ _) ρ)
      ρ (.wartet rest k) (fun L => held_nachSig_iff _ _ L)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks, hss.2, hk⟩)
      (fun O' U R σ e _ h => by
        rw [semH_dann]
        simp only [execBlockH, h]
        exact weiterH_logik S O' U passes R _ e)
      (fun O' U R σ _ => by
        rw [semH_dann]
        simp only [execBlockH]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            refine ⟨fun hw => by simp [RufRahmenG.wartend, GRest.wartend] at hw,
              fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
            rcases hc with hc | ⟨_, _, hc⟩
            · cases hc
              exact ZErgG.folgt_refl _
            · cases hc
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact vertrag_stabil (hFS _) g hp (List.append_subset.mpr hss.1.1.2))
      (fun hok σ hgσ => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact evalArgs_gleichAuf args
          (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.1.1.1 h') h) (hgσ.lese Λ Λ _ _) ρ)
      ρ (.wartetSonst (D.gruende g) err rest k) (fun L => held_nachSig_iff _ _ L)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [Block.gOk, Bool.and_eq_true] at hks
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks.1, hss.1.2, hks.2, hss.2, hk⟩)
      (fun O' U R σ e _ h => by
        rw [semH_dann]
        simp only [execBlockH, h]
        exact weiterH_logik S O' U passes R _ e)
      (fun O' U R σ _ => by
        rw [semH_dann]
        simp only [execBlockH]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            refine ⟨fun hw => by simp [RufRahmenG.wartend, GRest.wartend] at hw,
              fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
            rcases hc with hc | ⟨_, _, hc⟩
            · cases hc
            · cases hc
              exact ZErgG.folgt_refl _
        | grund σa r =>
            intro _ _ _ _ _ _ _ _ _ _ hc hn
            cases hc
            rw [semH_alsBlock_schrumpf]
            exact ZErgG.folgt_refl _
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  -- indirect calls: the pointer read at the key names the callee
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := okS_dann_cons (kopfS_okS hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => expr_stabil (hFS _) p (fun _ h' => hss.1 h') h)
        (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ))
      (fun _ => vertrag_stabil_ind (hFS _) g hg hp (hkand g hg))
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.2 h') h)
          (hgσ.lese Λ Λ _ _) ρ])
      ρ (.dann rest k) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_dann_cons hok).2.2)
      (fun O' U R σ e hgσ h => by
        rw [semH_dann_cons]
        simp only [execStmtH, hev σ hgσ, h]
        exact weiterH_logik S O' U passes R _ e)
      (fun O' U R σ hgσ => by
        rw [semH_dann_cons]
        simp only [execStmtH, hev σ hgσ]
        cases R g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σa v =>
            exact ⟨fun _ => ZErgG.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := okS_ende_cons (kopfS_okS hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => expr_stabil (hFS _) p (fun _ h' => hss.1 h') h)
        (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ))
      (fun _ => vertrag_stabil_ind (hFS _) g hg hp (hkand g hg))
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.2 h') h)
          (hgσ.lese Λ Λ _ _) ρ])
      ρ (.ende rest) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_ende_cons hok).2.2)
      (fun O' U R σ e hgσ h => by
        rw [semH_ende_cons]
        simp only [execStmtH, hev σ hgσ, h]
        rfl)
      (fun O' U R σ hgσ => by
        rw [semH_ende_cons]
        simp only [execStmtH, hev σ hgσ]
        cases R g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σa v =>
            exact ⟨fun _ => ZErgG.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu
      hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := kopfS_okS hF.1 hhead
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1
    have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => expr_stabil (hFS _) p (fun _ h' => hss.1.1 h') h)
        (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ))
      (fun _ => vertrag_stabil_ind (hFS _) g hg hp (hkand g hg))
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args
          (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.1.2 h') h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.wartet rest k) (fun L => held_nachSig_iff _ _ L)
      (fun hok => by
        obtain ⟨hks', hss', hk⟩ := hok
        simp only [Block.gOk, Bool.and_eq_true] at hks'
        simp only [blockOrteP, List.append_subset] at hss'
        exact ⟨hks'.2, hss'.2, hk⟩)
      (fun O' U R σ e hgσ h => by
        rw [semH_dann]
        simp only [execBlockH, hev σ hgσ, h]
        exact weiterH_logik S O' U passes R _ e)
      (fun O' U R σ hgσ => by
        rw [semH_dann]
        simp only [execBlockH, hev σ hgσ]
        cases R g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σa v =>
            refine ⟨fun hw => by simp [RufRahmenG.wartend, GRest.wartend] at hw,
              fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
            rcases hc with hc | ⟨_, _, hc⟩
            · cases hc
              exact ZErgG.folgt_refl _
            · cases hc
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  -- normal pops
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfS_okS hF.1 hhead
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_ende_cons (kopfS_okS hF.1 hhead)
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2.1)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_dann_cons (kopfS_okS hF.1 hhead)
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2.1)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfS_okS hF.1 hhead
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_dann_cons (kopfS_okS hF.1 hhead)
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2.1)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_dannRet S O' U passes R e hperm restk kk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_dannRet S O' U passes R e hperm restk kk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_ende_cons (kopfS_okS hF.1 hhead)
    have hens := popS_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabil (hFS _) e hok.2.1)
      (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueckCons S O' U passes R e hperm restk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popS_begr_ok hE hF.1 hhead e
        (fun O' R U σ => semH_rueckCons S O' U passes R e hperm restk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  -- reason pops
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
      hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_rueckGrund S O' U passes R rg hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_rueckConsGrund S O' U passes R rg hperm restk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_dannRetGrund S O' U passes R rg hperm restk kk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  -- register reads and `awaits`: the sequential oracle answers what the machine read
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP] at hss
    refine ⟨σ, Nat.le_refl _, hg, ⟨hks.2, hss, hrest⟩, fun R O' U hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_stabil (Λ := Λ) hks.1) hg
    exact ZErgG.folgt_of_eq
      (semH_regLies S O' U passes R r hk rest k σ ρ v (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hz)
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    obtain ⟨⟨hzS, _⟩, hrS⟩ := hss
    have hw' : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) =
        true := by
      rw [eval_gleichAuf zusage (fun _ h => expr_stabil (hFS _) zusage (fun _ h' => hzS h') h)
        (hg.lese Λ Λ zusage.orte zusage.orte), ← hs₁]
      exact hw
    refine ⟨σ.lese Λ zusage.orte, lese_laenge _ _ _, hg, ⟨hks.2.2, hrS, hrest⟩,
      fun R O' U hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_stabil (Λ := Λ) hks.1) hg
    exact ZErgG.folgt_of_eq (semH_regLiesElseWahr S O' U passes R r hk zusage sonst rest k σ ρ v
      (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hw')
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu
      hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokalQ hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    obtain ⟨⟨hzS, hsS⟩, _⟩ := hss
    have hw' : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) =
        false := by
      rw [eval_gleichAuf zusage (fun _ h => expr_stabil (hFS _) zusage (fun _ h' => hzS h') h)
        (hg.lese Λ Λ zusage.orte zusage.orte), ← hs₁]
      exact hw
    refine ⟨σ.lese Λ zusage.orte, lese_laenge _ _ _, hg,
      okS_alsBlock sonst k rest.held_iff hks.2.1 hsS hrk, fun R O' U hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_stabil (Λ := Λ) hks.1) hg
    exact semH_regLiesElseFalsch S O' U passes R r hk zusage sonst rest k σ ρ v
      (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hw'
  | dannAwaits l Γ Λ Λ' g payload hp hLg rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokalQ hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk] at hks
    simp only [blockOrteP, List.cons_subset] at hss
    have hgS : Sum.inr g ∈ stabilS P S lok (M.faeden u).kopf.f Λ :=
      stabil_of_fuss (hFS _) hss.1 fun L hB => bewacht_held (c := .inr g) hLg hB
    have hglob : (σ.lese Λ [.inr g]).globs g = σ₁.globs g := by
      rw [hs₁]
      exact hg.2 g hgS
    refine ⟨σ.lese Λ [.inr g], lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩, fun R O' U hQ => ?_⟩
    have hsv : O'.sichtbar g σ = true := by
      rw [sichtbar_gleich hRL hQ g hgS hg]
      exact hvis
    have h1 := semH_awaits S O' U passes R g payload hp hLg rest k σ ρ hsv
    rw [hglob] at h1
    exact ZErgG.folgt_of_eq h1

end Akteur

/-! ## 2. The other threads, the start, the invariant on every reachable machine -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **The rely for the replay**: a step of thread `u` leaves the stable
    carriers of the head frame of every other thread alone. -/
theorem andereS (hO : GutO O) (hS : SperrInvOk S) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hLok : LokOk P O passes lok sp init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) :
    FadenS P O passes Q S lok (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  exact fadenS_speicher hF (fun c hc =>
    stabilS_rely hO hS sp init hex hLok hr hs t htu _ List.mem_cons_self c hc)

/-- **The start machine is replayed.** -/
theorem zielInvS_start
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hStart : StartGut P sp init) :
    ZielInvS P O passes Q S lok (RufStartG P sp init) := by
  have hz : ∀ t, (RufStartG P sp init).faeden t =
      ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
        Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
        startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
    intro t
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
    cases init t
    rfl
  refine ⟨fun t => ?_, fun t => ?_⟩
  · unfold RufMaschineG.weltVon
    rw [hz t]
    exact ⟨⟨[], [], [], sp.welt [], hStart t, funkV_nil, vertraegeOkR_nil P, kurzVB_nil _,
      funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
      GleichAuf.vonSpeicher rfl, ⟨hFragS _, fuss_rumpfG P _⟩,
      fun R O' U _ _ _ _ => ZErgG.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- **One step keeps the replay, the log and the machine lock invariant.**
    The acting thread by `akteurS` (fed by the machine lock invariant at
    the acquire), the other threads by the rely; a lock that the step
    releases has its invariant at the new memory by the release check the
    obligation proves (`kopfS_frei_inv`). -/
theorem zielInvS_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hLok : LokOk P O passes lok sp init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvS P O passes Q S lok M)
    (hSG : SperrInvG S M) :
    ZielInvS P O passes Q S lok M' ∧ SperrInvG S M' := by
  have hRS := rufG_rahmenS hO hS sp init hex hLok hr
  have hA := akteurS hO hRL hQ hlok hS hsp hK hFragS hFS hs (hI.1 u) (hI.2 u) (hRS u) hSG
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact hA.1
    · exact andereS hO hS sp init hex hLok hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact hA.2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t
  · refine sperrInvG_schritt hO hS hs hSG (fun L hL hL' => ?_)
    rcases freigabe_schrittG hO hs with hgr | ⟨l, Γ, Λ, L', k, ρ, hhead, hsp', hoff⟩ |
        ⟨Γ, Λ, Λ1, L', rest, k, ρ, h, x, hhead, hsp', hoff⟩
    · exact absurd (hgr L hL) hL'
    · have hLL : L = L' := by
        refine Classical.byContradiction fun hne => hL' ?_
        rw [hoff]
        exact (List.mem_erase_of_ne hne).mpr hL
      subst hLL
      rw [hsp']
      exact kopfS_frei_inv hO hRL hQ hS hsp hK (hI.1 u).1 L List.mem_cons_self hhead
        (fun O' U R σ hi => semH_frei_falsch S O' U passes R L k σ ρ hi)
    · have hLL : L = L' := by
        refine Classical.byContradiction fun hne => hL' ?_
        rw [hoff]
        exact (List.mem_erase_of_ne hne).mpr hL
      subst hLL
      rw [hsp']
      exact kopfS_frei_inv hO hRL hQ hS hsp hK (hI.1 u).1 L
        ((Block.held_iff rest L).mp List.mem_cons_self) hhead
        (fun O' U R σ hi => semH_peelFrei_falsch S O' U passes R L rest k σ ρ h x hi)

/-- **The replay invariant and the machine lock invariant on every
    reachable machine**, generic in the local carriers `lok`. -/
theorem zielInvS_erreichbarL (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ZielInvS P O passes Q S lok M ∧ SperrInvG S M := by
  intro M hr
  induction hr with
  | start => exact ⟨zielInvS_start hFragS sp init hStart, sperrInvG_start P S sp init hsp⟩
  | schritt M M' u hr' hs ih =>
      exact zielInvS_schritt hO hRL hQ hlok hS hsp hK hFragS hFS init hex hLok hr' hs ih.1 ih.2

/-- **The replay invariant and the machine lock invariant on every
    reachable machine**, for the local carriers written by no function. -/
theorem zielInvS_erreichbar (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ZielInvS P O passes Q S (freiB fs) M ∧ SperrInvG S M := by
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  exact zielInvS_erreichbarL P O passes Q S (freiB fs) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFS) hFS (lokOk_frei hO hvoll sp init) hK hStart hsp hex

/-- **A replayed thread is stopped at no `logik` check** (as
    `fadenR_prueft`). -/
theorem fadenS_prueft (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f) {M : RufMaschineG D}
    (t : Faden) (hF : FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) :
    PrueftG O passes M t := by
  have hK' := hF.1
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semH_trav_falsch
    rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hok.1 h') h)
      (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semH_ewig_falsch
    rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hok.1 h') h)
      (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    have hg' := gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semH_leaveTrav_falsch
    rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hok.2.2.1 h') h)
      (hg'.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨_, hss, _⟩ := okS_ende_cons hok
    have hss' := orte_stabil (hFS _) (s.blatt_darf P hb) hss
    have h' := blatt_logik P s hb hss' hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    show zErgG (execEndH S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) (.cons s K) σ ρ) = _
    simp only [execEndH, execStmtH_blatt S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) s hb,
      h', zErgG]
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨_, hss, _⟩ := okS_dann_cons hok
    have hss' := orte_stabil (hFS _) (s.blatt_darf P hb) hss
    have h' := blatt_logik P s hb hss' hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    rw [semH_dann_cons, execStmtH_blatt S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) s hb,
      h']
    exact weiterH_logik _ _ _ _ _ _ e

end Ziel

/-! ## 3. The goal theorem -/

/-- **ZIEL AM ORT MIT SPERRINVARIANTEN -- THE goal theorem.** Over the
    repaired machine G, for every program in the widened fragment
    (`programmImFragmentG`) whose footprint check WITH LOCK INVARIANTS passes
    (`fussSperreB`: every footprint carrier is guarded by a signature lock,
    written by no function, or protected by the invariant of one of its
    guards), for a well-formed family of lock invariants `S` that holds at
    the start memory, from an exclusive start (no two threads START holding
    the same lock) that meets the entry contracts, with an oracle that keeps
    the declared axiom frames and the held locks (`GutO`), answers registers
    and `awaits` from the declared carriers (`RegLokal`) and meets the
    declared axiom ensures `Q`, and whose every function meets the user
    obligation `KoerperGutS` -- the SEQUENTIAL body triple, caller duty and
    no `logik` outcome, where each `locks L` may assume `S.inv L` of the
    protected carriers and must re-establish it at the release -- EVERY
    reachable machine satisfies
    * `VertragAmOrtG`: `requires` at every logged entry, `ensures` at every
      logged return, with the actual values -- also for contracts over
      carriers that are only protected by `locks` blocks (verdict probes B,
      C);
    * `SperrInvG`: the invariant of every lock that no thread holds holds in
      the live memory;
    * `KeinLogikHaltG`: no thread is stopped at a `logik` check of G;
    * progress at the checks (as `ziel_ort_ganz`).

    Premises, by class: (a) user logic `KoerperGutS` (per function, over the
    SEQUENTIAL semantics with acquire moves and release checks), `StartGut`,
    the lock invariants at the start memory (`hSstart`); (b) hardware `GutO`,
    `RegLokal`, `AxVertragO Q`; (c) decidable program facts `hvoll`,
    `programmImFragmentG`, `fussSperreB`, `StartExklusiv` (N240 for constant
    starts), `AxEnsLokal Q`, and the family's well-formedness `SperrInvOk`
    (its first half decidable; its second -- the invariant reads only the
    listed carriers -- by construction for an invariant written over them).
    No event is needed (`Begruendet`, SperreBeweis.lean §0b). -/
theorem ziel_ort_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  have hI := zielInvS_erreichbar P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss
    hK hStart hSstart hex M hr
  have hP : KeinLogikHaltG O passes M :=
    fun t => fadenS_prueft hO hRL hQ hS hSstart hK hFS t (hI.1.1 t)
  exact ⟨fun t ev hev => hI.1.2 t ev hev, hI.2, hP, fun t hH hA => schritt_an_pruefung t (hP t) hH hA⟩

/-- **Progress at every check, UNCONDITIONALLY** (held-set relaxation,
    2026-09-13): the rules of G now demand `HeldIn` of the head's holdings,
    which holds on every reachable machine (`rufG_haelt_statisch`), so the
    `HeldGenau` hypothesis of the progress conjunct of `ziel_ort_sperre` is
    no longer needed: on every reachable machine a thread standing at a
    `logik` check can step. -/
theorem ziel_ort_sperre_fortschritt (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ∀ t : Faden, AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr t hA
  have hZ := ziel_ort_sperre P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK
    hStart hSstart hex M hr
  exact schritt_an_pruefungI t (hZ.2.2.1 t)
    (fun L hL => rufG_haelt_statisch hO sp init hr t _ List.mem_cons_self L hL) hA

/-- **A start without signature locks is exclusive**: when every thread's
    root takes its locks in `locks` blocks (holds none by signature),
    `StartExklusiv` holds for ANY assignment -- the same routine may run on
    every thread. The premise of the goal theorem is exactly "no two
    threads START holding the same lock"; with the acquire steps of G and
    the lock invariants, a routine that takes its lock in a block needs no
    more. -/
theorem startExklusiv_ohne_haelt (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (h : ∀ t, D.haelt (init t).1 = []) : StartExklusiv init :=
  fun t _ _ L hL _ => by
    rw [h t] at hL
    exact absurd hL List.not_mem_nil

/-- **`ziel_ort_ganz` is the special case of the empty family** (no
    protected carriers, invariant `true`): its footprint check gives the new
    one (`fussSperreB_of_G`), its obligation gives the new one
    (`koerperGutS_leer`: every environment move is the identity and the
    semantics is `execStmt`). -/
theorem ziel_ort_ganz_aus_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  obtain ⟨h1, _, h3, h4⟩ := ziel_ort_sperre P O passes Q (SperrInv.leer D) fs sp init hO hRL hQ
    hlok sperrInvOk_leer hvoll hFrag (fussSperreB_of_G P _ fs hFuss)
    (fun f => koerperGutS_leer (hK f)) hStart (fun _ => rfl) hex M hr
  exact ⟨h1, h3, h4⟩

/-! ## CUTS:

  What is proved: `ziel_ort_sperre` -- over the repaired G, with a
  well-formed family of lock invariants `S` (protected carriers per lock,
  guarded by it; an invariant over them), the footprint check
  `fussSperreB` (a footprint carrier may be protected by the invariant of
  one of its guards instead of a signature lock), and the user obligation
  `KoerperGutS` (the sequential triple, caller duty and no `logik`
  outcome over the semantics in which every acquire may move the protected
  carriers within the invariant and every release checks it), every
  reachable machine satisfies `VertragAmOrtG`, `SperrInvG` (the invariant
  of every free lock holds in live memory), `KeinLogikHaltG` and progress at
  the checks. `ziel_ort_ganz` is its instance at the empty family
  (`ziel_ort_ganz_aus_sperre`). Every premise is used: `SperrInvOk` (the
  record moves are in the class, the rely on protected carriers, the
  machine invariant), `hSstart` (the machine invariant at the start, the
  default of the record moves), `fussSperreB` (reads inside stable
  carriers), `KoerperGutS` (both clauses: returns, calls, releases), the
  rest as in `ziel_ort_ganz`.

  What is NOT covered:

  - The invariant is a semantic family (`SperrInv.inv : Lock → Speicher →
    Bool`, local to its listed carriers), not a surface clause: nothing
    parses `lock L protects … invariant …`, and no checker rule computes
    `fussSperreB` or the first half of `SperrInvOk` (both decidable).
  - Precision of the environment's move: at an acquire of `L` the move may
    change EVERY carrier `L` protects, also one guarded by a second lock the
    frame already holds (no other thread can have changed it; the class is
    conservative, the user proves slightly more than needed for nested
    locks).
  - Held-set relaxation (2026-09-13, verdict note T): `RufPasst.hh` is now
    an inclusion (the callee's signature locks are among the caller's held
    locks), with lock floors (`Signatur.boden`, `RufPasst.hx`/`hb`) for the
    rank discipline across calls; G's side condition is `HeldIn`. The
    theorem above needed no change; `ziel_ort_sperre_fortschritt` drops the
    `HeldGenau` hypothesis of the progress conjunct. Witness: `helfer_zeuge`
    (`HelferZeuge.lean`).
  - A carrier read from only ONE thread still needs a guard, a signature
    lock or no writer (`sicher`); a concurrency-aware exemption needs the
    call graph of each thread, which no invariant of G carries yet.
  - Device carriers (register reads) are read without a guard at the
    access: they stay signature-guarded or unwritten.
  - Waiting at `dannLocks` (another thread holds `L`) is the named scheduler
    situation; no fairness or hold-time bound. Everything cut in
    `ZielOrtGanz.lean` (table invariants, termination, full progress) and
    `ZielOrtRahmen.lean` carries over.
-/

#print axioms Gabbro.Grammatik.akteurS
#print axioms Gabbro.Grammatik.zielInvS_erreichbar
#print axioms Gabbro.Grammatik.ziel_ort_sperre
#print axioms Gabbro.Grammatik.ziel_ort_sperre_fortschritt
#print axioms Gabbro.Grammatik.ziel_ort_ganz_aus_sperre

end Gabbro.Grammatik
