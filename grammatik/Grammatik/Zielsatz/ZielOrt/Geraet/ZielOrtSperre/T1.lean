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
import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine

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
  | endeForm l Γ Λ e ρ hl hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenS_lokal hF hhead ρ (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, okS_alsBlock e .leer (fun L => Iff.rfl) hok.1 hok.2 trivial,
      fun R O' U => ZErgG.folgt_of_eq (semH_endeForm S O' U passes R e σ ρ)⟩
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
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have e2 : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
      have := congrArg Prod.fst hax
      simp only [axiomAntwortSonst] at this
      exact this.symm
    have hv : sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).2 = some (Sum.inr r) := by
      have := congrArg Prod.snd hax
      simp only [axiomAntwortSonst] at this
      exact this
    have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
    rw [← e2] at hfr
    subst hs₁
    refine ⟨fadenS_ax hF hhead (Env.cons (τ := .why (D.agruende a)) r ρ) (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => okS_alsBlock err (.schrumpf k) rest.held_iff
        (by have h1 := hok.1; simp only [Block.gOk, Bool.and_eq_true] at h1; exact h1.1)
        (by have h2 := hok.2.1; simp only [blockOrteP] at h2; exact (teil_append (teil_append h2).1).2) hok.2.2)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) = _
    simp only [execBlockH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rw [semH_alsBlock_schrumpf]
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have e2 : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
      have := congrArg Prod.fst hax
      simp only [axiomAntwortSonst] at this
      exact this.symm
    have hv : sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).2 = some (Sum.inl v) := by
      have := congrArg Prod.snd hax
      simp only [axiomAntwortSonst] at this
      exact this
    have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
    rw [← e2] at hfr
    subst hs₁
    refine ⟨fadenS_ax hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Block.gOk, Bool.and_eq_true] at h1; exact h1.2,
        by have h2 := hok.2.1; simp only [blockOrteP] at h2; exact (teil_append h2).2, hok.2.2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterH S O' U passes R k
      (execBlockH S O' U passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) = _
    simp only [execBlockH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rfl
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
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
    refine ⟨fadenS_ax hF hhead (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => ⟨hok.1, by simpa [endblockOrteP] using (teil_append hok.2).2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show zErgG (execEndH S O' U passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ) = _
    simp only [execEndH, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rw [zErgG_schrumpf]
    rfl
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have e2 : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
      have := congrArg Prod.fst hax
      simp only [axiomAntwortSonst] at this
      exact this.symm
    have hv : sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).2 = some (Sum.inr r) := by
      have := congrArg Prod.snd hax
      simp only [axiomAntwortSonst] at this
      exact this
    have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
    rw [← e2] at hfr
    subst hs₁
    refine ⟨fadenS_ax hF hhead (Env.cons (τ := .why (D.agruende a)) r ρ) (.ende err) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Endblock.gOk, Bool.and_eq_true] at h1; exact h1.1,
        by have h2 := hok.2; simp only [endblockOrteP] at h2; exact (teil_append (teil_append h2).1).2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show zErgG (execEndH S O' U passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) = _
    simp only [execEndH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rw [zErgG_schrumpf]
    rfl
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have e2 : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
      have := congrArg Prod.fst hax
      simp only [axiomAntwortSonst] at this
      exact this.symm
    have hv : sonstPasst O.zeiger (D.aerg a) (D.agruende a) (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).2 = some (Sum.inl v) := by
      have := congrArg Prod.snd hax
      simp only [axiomAntwortSonst] at this
      exact this
    have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
    rw [← e2] at hfr
    subst hs₁
    refine ⟨fadenS_ax hF hhead (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => ⟨by have h1 := hok.1; simp only [Endblock.gOk, Bool.and_eq_true] at h1; exact h1.2,
        by have h2 := hok.2; simp only [endblockOrteP] at h2; exact (teil_append h2).2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U σ hz hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show zErgG (execEndH S O' U passes R (.bindAxiomElse a args he hr hw hg hd hgd err rest) σ ρ) = _
    simp only [execEndH, axiomAntwortSonst, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rw [zErgG_schrumpf]
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
        | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
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
        | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
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
        | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
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
        | why σa r =>
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
        | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
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
        | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
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
        | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
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
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_rueckGrund S O' U passes R rg hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
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
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_rueckConsGrund S O' U passes R rg hperm restk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
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
    refine ⟨⟨popS_kopf hWc (M.weltVon u) (fun σa => .why σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popS_begr_grund hE hF.1 hhead rg
        (fun O' R U σ => semH_dannRetGrund S O' U passes R rg hperm restk kk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .why n) (Fin.cast hn rg) ρc)
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
  | dannAwaits l Γ Λ Λ' g payload hp hLg hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
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
    have h1 := semH_awaits S O' U passes R g payload hp hLg hat rest k σ ρ hsv
    rw [hglob] at h1
    exact ZErgG.folgt_of_eq h1

end Akteur

end Gabbro.Grammatik
