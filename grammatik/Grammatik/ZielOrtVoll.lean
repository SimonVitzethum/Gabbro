/-
  File:      Grammatik/ZielOrtVoll.lean
  Subject:   `ziel_ort_voll` -- the acting thread keeps its replay under every
             rule of G, the other threads keep theirs by the rely, and the
             theorem.

  The replay invariants and the steps that record or pop are in
  `ZielOrtVollBeweis.lean`; the frame semantics of every residue in
  `ZielOrtVollSem.lean`.
-/
import Grammatik.ZielOrtVollBeweis

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The residue of a frame, read off its rest. -/
theorem rest_okV {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (h : F.rest.2.2.2.2.okV P (fussOrte P F.f)) : r.okV P (fussOrte P F.f) := by
  rw [hF] at h
  exact h

/-- **The acting thread keeps its replay and its log** -- every rule of G:
    the head-local steps by the residue step lemmas at the sequential
    world, the leaves by leaf locality or by recording an axiom answer, the
    pushes by `pushV_ok` (direct) and `pushV_gen` (indirect: the pointer
    read at the key names the callee, whose contract carriers the fragment
    puts in the footprint), the normal pops by `popV_ens` and `popV_kopf`,
    the reason pops by `popV_kopf`; the rules outside the fragment (register
    reads, `awaits`) find a head residue that is not in it. -/
theorem akteurV (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (e0 : Ereignis D)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenV P passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log) :
    FadenV P passes (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_blatt e0 hO hF hhead s (.ende rest)
      (fun O' R σ => semV_ende_cons O' passes R s rest σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okV_ende_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_blatt e0 hO hF hhead s (.dann rest k)
      (fun O' R σ => semV_dann_cons O' passes R s rest k σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okV_dann_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann (.cons s .nil) (.ende rest)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_ende_cons hok
    refine ⟨σ, Nat.le_refl _, hg, ⟨by simp [Block.vOk, hks], ?_, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_endeEntf O' passes R s rest σ ρ)⟩
    simpa [blockOrteP] using hss
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok.2.2, fun R O' => ZErg.folgt_refl _⟩
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann t (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    obtain ⟨ht, _⟩ := and_teile hks
    obtain ⟨hc, htS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨ht, htS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_ite O' passes R c t e rest k σ ρ true hw')⟩
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann e (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    obtain ⟨_, he⟩ := and_teile hks
    obtain ⟨hc, _, heS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨he, heS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_ite O' passes R c t e rest k σ ρ false hw')⟩
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons v ρ) (.dann p (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    obtain ⟨hp, _⟩ := and_teile hks
    obtain ⟨hc, hpS, _⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v := by
      rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨hp, hpS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_optSome O' passes R o p a rest k σ ρ v hv')⟩
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann a (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    obtain ⟨_, ha⟩ := and_teile hks
    obtain ⟨hc, _, haS⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none := by
      rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨ha, haS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_optNone O' passes R o p a rest k σ ρ hv')⟩
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
        ⟨some (lo, hi), b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_vOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_tagSome O' passes R v arms rest k σ ρ lo hi b nutz hw')⟩
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (armEnv nutz ρ) (.dann b (.dann rest k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_vOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_tagNone O' passes R v arms rest k σ ρ b nutz hw')⟩
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann b (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hb : grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ) = b := by
      rw [eval_gleichAuf r (fun _ h => hss.1 h) (hg.lese Λ Λ r.orte r.orte) ρ, ← hs₁]; exact hw
    refine ⟨σ.lese Λ r.orte, lese_laenge _ _ _, hg, ⟨?_, ?_, hrest⟩, fun R O' => ?_⟩
    · rw [← hb]; exact grundWahlG_vOk arms _ hks
    · rw [← hb]; exact fun _ h => hss.2 (grundWahlG_orteP arms _ h)
    · rw [← hb]; exact ZErg.folgt_of_eq (semV_grund O' passes R r arms rest k σ ρ)
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.ende rest) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss⟩ := hok
    simp only [endblockOrteP, List.append_subset] at hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2⟩, fun R O' => ?_⟩
    have h1 := semV_endeBind O' passes R e rest σ ρ
    rw [he'] at h1
    exact ZErg.folgt_of_eq h1
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩, fun R O' => ?_⟩
    have h1 := semV_dannBind O' passes R e rest k σ ρ
    rw [he'] at h1
    exact ZErg.folgt_of_eq h1
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead _ (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hes, _, hrS⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := by rw [he']; exact h
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩, fun R O' => ?_⟩
    have h1 := semV_narrowOk O' passes R e lo' hi' sonst rest k σ ρ h'
    have hz : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h'.1, h'.2⟩ :
        Wert D (.int lo' hi')) = ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ := by
      simp only [he']
    rw [hz] at h1
    exact ZErg.folgt_of_eq h1
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.ende sonst) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, _⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') := by rw [he']; exact h
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkS, hsS⟩,
      fun R O' => semV_narrowElse O' passes R e lo' hi' sonst rest k σ ρ h'⟩
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann rest k) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hc, _, hrS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_pruefWahr O' passes R c sonst rest k σ ρ hw')⟩
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.ende sonst) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, _⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hc, hsS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨hkS, hsS⟩,
      fun R O' => semV_pruefFalsch O' passes R c sonst rest k σ ρ hw'⟩
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_breaking O' passes R i body rest k σ ρ)⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann body (.frei L (.dann rest k)))
      (Ereignis.nimmt L (offen (M.faeden u).spur) :: (M.faeden u).spur) (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    exact ⟨σ.nimmt L, Nat.le_succ _, hg, ⟨hks, hss, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_locks O' passes R L hr body rest k σ ρ)⟩
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ k (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ.gibt L, Nat.le_succ _, hg, hok, fun R O' => ZErg.folgt_refl _⟩
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok, fun R O' => ZErg.folgt_refl _⟩
  -- loops
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.trav t inv body (alleIndizes (D.count t)) (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_dannTrav O' passes R t inv body rest k σ ρ)⟩
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons i ρ) (.dann body (.travRest t inv body is k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hinv, hb, hbS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_travNext O' passes R t inv body i is k σ ρ hw')⟩
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' => ZErg.folgt_of_eq (semV_travFort O' passes R t inv body is k i σ ρ)⟩
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ k σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, _, _, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, hk,
      fun R O' => ZErg.folgt_of_eq (semV_travDone O' passes R t inv body k σ ρ hw')⟩
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.wieder n bis body ueber (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    obtain ⟨hb, hu⟩ := and_teile hks
    obtain ⟨hbis, hbS, huS⟩ := teile2 hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hbis, hb, hbS, hu, huS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_dannRetry O' passes R n bis body ueber rest k σ ρ)⟩
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann ueber k) (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, hu, huS, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hu, huS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_wiederUeber O' passes R bis body ueber k σ ρ)⟩
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ k σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, _, _, _, _, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true := by
      rw [eval_gleichAuf bis (fun _ h => hbis h) (hg.lese Λ Λ bis.orte bis.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ bis.orte, lese_laenge _ _ _, hg, hk,
      fun R O' => ZErg.folgt_of_eq (semV_wiederWeiter O' passes R n bis body ueber k σ ρ hw')⟩
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann body (.wiederRest n bis body ueber k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, hb, hbS, hu, huS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
      rw [eval_gleichAuf bis (fun _ h => hbis h) (hg.lese Λ Λ bis.orte bis.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ bis.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hbis, hb, hbS, hu, huS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_wiederSchritt O' passes R n bis body ueber k σ ρ hw')⟩
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' => ZErg.folgt_of_eq (semV_wiederFort O' passes R n bis body ueber k σ ρ)⟩
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.ewig a passes inv body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okV_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_dannForever O' passes R a inv body rest k σ ρ)⟩
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.dann body (.ewigRest a n inv body k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hinv, hb, hbS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_ewigWeiter O' passes R a n inv body k σ ρ hw')⟩
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' => ZErg.folgt_of_eq (semV_ewigFort O' passes R a n inv body k σ ρ)⟩
  -- the exits
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    subst hs₁
    refine ⟨fadenV_lokal hF hhead ρ k _ (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    obtain ⟨hinv, _, _, hk⟩ := hTR
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, hk,
      fun R O' => ZErg.folgt_of_eq
        (semV_leaveTrav O' passes R t inv body is k rest i σ ρ hleave hw')⟩
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenV_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, hTR,
      fun R O' => ZErg.folgt_of_eq (semV_nextTrav O' passes R t inv body is k rest i σ ρ hnext)⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenV_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    obtain ⟨_, _, _, _, _, hk⟩ := hWR
    exact ⟨σ, Nat.le_refl _, hg, hk,
      fun R O' => ZErg.folgt_of_eq
        (semV_leaveWieder O' passes R n bis body ueber k rest σ ρ hleave)⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenV_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, hWR,
      fun R O' => ZErg.folgt_of_eq
        (semV_nextWieder O' passes R n bis body ueber k rest σ ρ hnext)⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenV_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    obtain ⟨_, _, _, hk⟩ := hER
    exact ⟨σ, Nat.le_refl _, hg, hk,
      fun R O' => ZErg.folgt_of_eq (semV_leaveEwig O' passes R a n inv body k rest σ ρ hleave)⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenV_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, hER,
      fun R O' => ZErg.folgt_of_eq (semV_nextEwig O' passes R a n inv body k rest σ ρ hnext)⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelDann O' passes R rest b k σ ρ hleave true)⟩
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelDann O' passes R rest b k σ ρ hnext false)⟩
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelSchrumpf O' passes R rest k σ ρ hleave true)⟩
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelSchrumpf O' passes R rest k σ ρ hnext false)⟩
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ _ (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ.gibt L, Nat.le_succ _, hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelFrei O' passes R L rest k σ ρ hleave true)⟩
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ _ (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ.gibt L, Nat.le_succ _, hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelFrei O' passes R L rest k σ ρ hnext false)⟩
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.cons_subset, List.append_subset] at hss
    obtain ⟨⟨hgS, hnS⟩, hrS⟩ := hss
    subst hs₂ hs₁
    have hgl := hg.lese Λ Λ (.inr g :: neuE.orte) (.inr g :: neuE.orte)
    have hglob : (σ.lese Λ (.inr g :: neuE.orte)).globs g =
        ((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g := hgl.2 g hgS
    have hval : eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
        (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
        eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) :=
      eval_gleichAuf neuE (fun _ h => hnS h) hgl _
    refine ⟨(σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
        (eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ)),
      spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _)),
      gleichAuf_schreibGlob hgl g Λ Λ _, ⟨hks, hrS, hrest⟩, fun R O' => ?_⟩
    have h1 := semV_exchange O' passes R g neuE hw hLg rest k σ ρ
    rw [hglob, hval] at h1
    exact ZErg.folgt_of_eq h1
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨haS, hbS, hrS⟩ := teile2 hss
    have hgl := hg.lese Λ Λ (a.orte ++ b.orte) (a.orte ++ b.orte)
    have hv' : gleitPasst lo hi (gleitRechne op
        (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
        (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v := by
      rw [eval_gleichAuf a (fun _ h => haS h) hgl ρ, eval_gleichAuf b (fun _ h => hbS h) hgl ρ,
        ← hs₁]
      exact hv
    exact ⟨σ.lese Λ (a.orte ++ b.orte), lese_laenge _ _ _, hg, ⟨hks, hrS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_gleit O' passes R op a b lo hi rest k σ ρ v hv')⟩
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_gleitLit O' passes R q lo hi rest k σ ρ v hv)⟩
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have hv' : gleitPasst lo hi (Float.ofInt (eval (σ.lese Λ e.orte) e
        (σ.lese Λ e.orte) ρ).n) = some v := by
      rw [eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_gleitVon O' passes R e lo hi rest k σ ρ v hv')⟩
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hes, _, hrS⟩ := teile2 hss
    have hv' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v := by
      rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_gleitNarrowOk O' passes R e lo hi sonst rest k σ ρ v hv')⟩
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenV_lokal hF hhead ρ (.ende sonst) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, _⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have hn' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none := by
      rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hn
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkS, hsS⟩,
      fun R O' => semV_gleitNarrowElse O' passes R e lo hi sonst rest k σ ρ hn'⟩
  -- the axiom bind
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have e2 : σ₂ = (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).1 := by
      have := congrArg Prod.fst hax
      simp only [axiomAntwort] at this
      exact this.symm
    have hv : einpassenErg (D.aerg a) (O.wirkt a σ₁ (evalArgs σ₁ args σ₁ ρ)).2 = some v := by
      have := congrArg Prod.snd hax
      simp only [axiomAntwort] at this
      exact this
    have hfr := (hO a σ₁ (evalArgs σ₁ args σ₁ ρ)).1
    rw [← e2] at hfr
    subst hs₁
    refine ⟨fadenV_ax e0 hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur a args
      (fun hok => ⟨hok.1, by simpa [blockOrteP] using (teil_append hok.2.1).2, hok.2.2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun O' R σ hwk => ?_), hL⟩
    apply ZErg.folgt_of_eq
    show weiterZ O' passes R k (execBlock O' passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ) = _
    simp only [execBlock, axiomAntwort, hwk, hv]
    rfl
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushV_ok hO hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okV_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact ⟨hss.1, List.append_subset.mpr hss.2⟩)
      ρ (.ende rest) (fun hok => (okV_ende_cons hok).2.2)
      (fun O' R σ e h => by
        rw [semV_ende_cons]
        simp only [execStmt, h]
        rfl)
      (fun O' R σ => by
        rw [semV_ende_cons]
        simp only [execStmt]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            exact ⟨fun _ => ZErg.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushV_ok hO hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okV_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact ⟨hss.1, List.append_subset.mpr hss.2⟩)
      ρ (.dann rest k) (fun hok => (okV_dann_cons hok).2.2)
      (fun O' R σ e h => by
        rw [semV_dann_cons]
        simp only [execStmt, h]
        exact weiterZ_logik O' passes R _ e)
      (fun O' R σ => by
        rw [semV_dann_cons]
        simp only [execStmt]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            exact ⟨fun _ => ZErg.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushV_ok hO hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hss.1.1, List.append_subset.mpr hss.1.2⟩)
      ρ (.wartet rest k)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks, hss.2, hk⟩)
      (fun O' R σ e h => by
        rw [semV_dann]
        simp only [execBlock, h]
        exact weiterZ_logik O' passes R _ e)
      (fun O' R σ => by
        rw [semV_dann]
        simp only [execBlock]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            refine ⟨fun hw => by simp [RufRahmenG.wartend, GRest.wartend] at hw,
              fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
            rcases hc with hc | ⟨_, _, hc⟩
            · cases hc
              exact ZErg.folgt_refl _
            · cases hc
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
      hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushV_ok hO hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hss.1.1.1, List.append_subset.mpr hss.1.1.2⟩)
      ρ (.wartetSonst (D.gruende g) err rest k)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [Block.vOk, Bool.and_eq_true] at hks
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks.1, hss.1.2, hks.2, hss.2, hk⟩)
      (fun O' R σ e h => by
        rw [semV_dann]
        simp only [execBlock, h]
        exact weiterZ_logik O' passes R _ e)
      (fun O' R σ => by
        rw [semV_dann]
        simp only [execBlock]
        cases R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
          with
        | ok σa v =>
            refine ⟨fun hw => by simp [RufRahmenG.wartend, GRest.wartend] at hw,
              fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
            rcases hc with hc | ⟨_, _, hc⟩
            · cases hc
            · cases hc
              exact ZErg.folgt_refl _
        | grund σa r =>
            intro _ _ _ _ _ _ _ _ _ _ hc hn
            cases hc
            have h1 := weiterZ_ende_folgt O' passes R k
              (execEnd O' passes R err σa (.cons r ρ)).schrumpf
            rw [zErg_schrumpf] at h1
            exact h1
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  -- indirect calls: the pointer read at the key names the callee
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := okV_dann_cons (kopfV_okV hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrte P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (fussOrte P (M.faeden u).kopf.f) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => hss.1 h) (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushV_gen hO hK hFrag hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => hss.2 h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.dann rest k) (fun hok => (okV_dann_cons hok).2.2)
      (fun O' R σ e hgσ h => by
        rw [semV_dann_cons]
        simp only [execStmt, hev σ hgσ, h]
        exact weiterZ_logik O' passes R _ e)
      (fun O' R σ hgσ => by
        rw [semV_dann_cons]
        simp only [execStmt, hev σ hgσ]
        cases R g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σa v =>
            exact ⟨fun _ => ZErg.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := okV_ende_cons (kopfV_okV hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrte P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (fussOrte P (M.faeden u).kopf.f) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => hss.1 h) (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushV_gen hO hK hFrag hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => hss.2 h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.ende rest) (fun hok => (okV_ende_cons hok).2.2)
      (fun O' R σ e hgσ h => by
        rw [semV_ende_cons]
        simp only [execStmt, hev σ hgσ, h]
        rfl)
      (fun O' R σ hgσ => by
        rw [semV_ende_cons]
        simp only [execStmt, hev σ hgσ]
        cases R g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σa v =>
            exact ⟨fun _ => ZErg.folgt_refl _,
              fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
        | grund σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu
      hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := kopfV_okV hF.1 hhead
    simp only [Block.vOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrte P (M.faeden u).kopf.f) n := kandP_ok hks.1
    have hev : ∀ σ : World D, GleichAuf (fussOrte P (M.faeden u).kopf.f) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => hss.1.1 h) (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushV_gen hO hK hFrag hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => hss.1.2 h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.wartet rest k)
      (fun hok => by
        obtain ⟨hks', hss', hk⟩ := hok
        simp only [Block.vOk, Bool.and_eq_true] at hks'
        simp only [blockOrteP, List.append_subset] at hss'
        exact ⟨hks'.2, hss'.2, hk⟩)
      (fun O' R σ e hgσ h => by
        rw [semV_dann]
        simp only [execBlock, hev σ hgσ, h]
        exact weiterZ_logik O' passes R _ e)
      (fun O' R σ hgσ => by
        rw [semV_dann]
        simp only [execBlock, hev σ hgσ]
        cases R g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
        | ok σa v =>
            refine ⟨fun hw => by simp [RufRahmenG.wartend, GRest.wartend] at hw,
              fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
            rcases hc with hc | ⟨_, _, hc⟩
            · cases hc
              exact ZErg.folgt_refl _
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
    have hok := kopfV_okV hF.1 hhead
    have hens := popV_ens hO hK hF.1 hhead e hok.2
      (fun O' R σ => semV_rueck O' passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okV_ende_cons (kopfV_okV hF.1 hhead)
    have hens := popV_ens hO hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_rueckCons O' passes R e hperm rest σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okV_dann_cons (kopfV_okV hF.1 hhead)
    have hens := popV_ens hO hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_dannRet O' passes R e hperm rest k σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfV_okV hF.1 hhead
    have hens := popV_ens hO hK hF.1 hhead e hok.2
      (fun O' R σ => semV_rueck O' passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okV hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okV hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okV_dann_cons (kopfV_okV hF.1 hhead)
    have hens := popV_ens hO hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_dannRet O' passes R e hperm restk kk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okV hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okV hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okV_ende_cons (kopfV_okV hF.1 hhead)
    have hens := popV_ens hO hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_rueckCons O' passes R e hperm restk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okV hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okV hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
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
    refine ⟨⟨popV_kopf e0 hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc) (.ende err)
      (fun hokc => ⟨(rest_okV hcaller hokc).1, (rest_okV hcaller hokc).2.1⟩)
      (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc) (.ende err)
      (fun hokc => ⟨(rest_okV hcaller hokc).1, (rest_okV hcaller hokc).2.1⟩)
      (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    subst hfg hs0 hrg
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popV_kopf e0 hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc) (.ende err)
      (fun hokc => ⟨(rest_okV hcaller hokc).1, (rest_okV hcaller hokc).2.1⟩)
      (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  -- every other rule: the head residue is outside the fragment
  | _ =>
    exact absurd (kopfV_okV hF.1 ‹(M.faeden u).kopf.rest = _›)
      (by simp [GRest.okV, Block.vOk, Stmt.vOk, Endblock.vOk])

end Akteur

/-! ## 2. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for the replay** (as `andere_ok`): a step of thread `u`
    leaves the footprint of every head frame of another thread alone. -/
theorem andereV (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenV P passes (M.faeden t) (M.weltVon t)) :
    FadenV P passes (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenV_speicher hF (fun c hc => ?_)
  rcases fussOrtB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** -/
theorem zielInvV_start (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInvV P passes (RufStartG P sp init) := by
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
    exact ⟨⟨[], [], sp.welt [], hStart t, funkV_nil, vertraegeOkV_nil P, kurzV_nil _, funkA_nil,
      rahmenA_nil, kurzA_nil _, GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpf P _⟩,
      fun R O' _ _ => ZErg.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant. -/
theorem zielInvV_schritt (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvV P passes M) :
    ZielInvV P passes M' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteurV hO hK hFrag e0 hs (hI.1 t) (hI.2 t)).1
    · exact andereV hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteurV hO hK hFrag e0 hs (hI.1 t) (hI.2 t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **ZIEL AM ORT, FULL LANGUAGE -- contracts hold at their place on every
    machine of the repaired concurrent call machine G, for bodies with
    loops, exits, the error channel and axiom calls.**

    Premises, by class:
    * (a) user obligations: `KoerperGutV P passes f` for every function
      (the body's Hoare triple over the SEQUENTIAL semantics with any
      contract-respecting call handler AND any oracle respecting the
      declared axiom frames, and its caller duty), `StartGut` and
      `StartExklusiv` (the boot assignment);
    * (b) hardware: `GutO O`;
    * (c) decidable program facts over a complete member list `fs`: the
      covered fragment (`programmImFragmentV`: no register read, no
      `awaits`; an indirect call only where every function of its
      signature has its contract carriers in the caller's footprint) and
      the footprint check (`fussOrtB`);
    * the declaration declares a table, a global or a lock (`e0`: an event
      exists; it gives each recorded call answer and each recorded axiom
      answer a fresh trace position).

    Conclusion: on EVERY machine reachable from the start machine, at every
    `eintritt` of every thread log the callee's `requires` holds with the
    actual parameters at the actual entry world, and at every `rueck` the
    `ensures` holds with the actual entry world, return world, parameters
    and result. -/
theorem ziel_ort_voll (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutV P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  have hFragF : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true :=
    programmImFragmentV_ok P hvoll hFrag
  intro M hr
  have hI : ZielInvV P passes M := by
    induction hr with
    | start => exact zielInvV_start hFragF sp init hStart
    | schritt M M' u hr' hs ih =>
        exact zielInvV_schritt hO hvoll hFuss hK hFragF e0 sp init hex hr' hs ih
  exact fun t ev hev => hI.2 t ev hev

end Ziel

/-! ## 3. Reason returns: what the machine logs and where the caller goes

    Contracts say nothing about a reason return (`RespektiertVertraege` and
    `EnsAmRueck` are about normal returns; `VertragAmOrtG` checks entries
    and normal returns). The statement for reasons is the machine's own:
    every step that logs `grund g rho r s0 s1` pops a head frame of `g`
    whose residue is returning exactly that reason, into a caller waiting in
    `let x = g(…) else { err }`, which continues with `err` and the reason
    bound. -/

/-- The reason a residue returns right now, if its head is a reason return. -/
def GRest.grundJetzt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option (Fin V.gruende)
  | .ende (.retGrund r _) => some r
  | .ende (.cons (.retGrund r _) _) => some r
  | .dann (.cons (.retGrund r _) _) _ => some r
  | _ => none

/-- **Reason returns are logged faithfully.** -/
theorem rufG_grund_treu {P : Programm D} {O : Orakel D} {passes : Nat} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O passes M u M') (g : D.Fn) (rho : Env D (D.params g))
    (r : Fin (D.gruende g)) (s0 s1 : World D)
    (hlog : (M'.faeden u).log = RufEreignisF.grund g rho r s0 s1 :: (M.faeden u).log) :
    (M.faeden u).kopf.f = g ∧
    (∃ r' : Fin (vertragVon D (M.faeden u).kopf.f).gruende,
      (M.faeden u).kopf.rest.2.2.2.2.grundJetzt = some r' ∧ HEq r' r) ∧
    ∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (l : Bool) (Γ : Ctx)
      (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D caller.f) l (.grund n :: Γ) Λ)
      (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ) (hn : D.gruende g = n),
      (M.faeden u).stapel = caller :: rst ∧
      caller.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧
      (M'.faeden u).stapel = rst ∧
      (M'.faeden u).kopf =
        ⟨caller.f, caller.rho, caller.s0,
          ⟨l, .grund n :: Γ, Λ, Env.cons (τ := .grund n) (Fin.cast hn r) ρc, .ende err⟩⟩ := by
  cases hs with
  | rueckGrund r0 hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g' hfg rho'
      hrho s0' hs0 rg hrg hn =>
    simp only [rufUpdateG_self, List.cons.injEq, RufEreignisF.grund.injEq] at hlog ⊢
    obtain ⟨⟨hg, hrho', hr, _, _⟩, _⟩ := hlog
    subst hg
    subst hfg
    subst hrg
    refine ⟨rfl, ⟨rg, by rw [hhead]; rfl, hr⟩, caller, rst, l, Γ, Λ, Λ', τ, n, err, restb, k, ρc,
      hn, hpop, hcaller, rfl, ?_⟩
    cases hr
    rfl
  | rueckConsGrund r0 hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g'
      hfg rho' hrho s0' hs0 rg hrg hn =>
    simp only [rufUpdateG_self, List.cons.injEq, RufEreignisF.grund.injEq] at hlog ⊢
    obtain ⟨⟨hg, hrho', hr, _, _⟩, _⟩ := hlog
    subst hg
    subst hfg
    subst hrg
    refine ⟨rfl, ⟨rg, by rw [hhead]; rfl, hr⟩, caller, rst, l, Γ, Λ, Λ', τ, n, err, restb, k, ρc,
      hn, hpop, hcaller, rfl, ?_⟩
    cases hr
    rfl
  | dannRetGrund r0 hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g'
      hfg rho' hrho s0' hs0 rg hrg hn =>
    simp only [rufUpdateG_self, List.cons.injEq, RufEreignisF.grund.injEq] at hlog ⊢
    obtain ⟨⟨hg, hrho', hr, _, _⟩, _⟩ := hlog
    subst hg
    subst hfg
    subst hrg
    refine ⟨rfl, ⟨rg, by rw [hhead]; rfl, hr⟩, caller, rst, l, Γ, Λ, Λ', τ, n, err, restb, k, ρc,
      hn, hpop, hcaller, rfl, ?_⟩
    cases hr
    rfl
  | _ =>
    simp only [rufUpdateG_self] at hlog
    first
      | exact absurd hlog.symm (List.cons_ne_self _ _)
      | (simp only [List.cons.injEq, reduceCtorEq, false_and] at hlog)

/-! ## 4. The old theorem is a special case -/

section Orakelfrei

variable (O O' : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

mutual

/-- A statement of the old fragment does not consult the oracle. -/
theorem Stmt.orakel_kOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.kOk = true → ∀ (σ : World D) (ρ : Env D Γ),
      execStmt O passes R s σ ρ = execStmt O' passes R s σ ρ
  | .ite _ t e, h, σ, ρ => by
      simp only [Stmt.kOk, Bool.and_eq_true] at h
      simp only [execStmt, Block.orakel_kOk t h.1, Block.orakel_kOk e h.2]
  | .onOption _ p a, h, σ, ρ => by
      simp only [Stmt.kOk, Bool.and_eq_true] at h
      simp only [execStmt, Block.orakel_kOk p h.1, Block.orakel_kOk a h.2]
  | .onTag _ arms, h, σ, ρ => by
      simp only [Stmt.kOk] at h
      simp only [execStmt, Arms.orakel_kOk arms h]
  | .onGrund _ arms, h, σ, ρ => by
      simp only [Stmt.kOk] at h
      simp only [execStmt]
      exact GrundArms.orakel_kOk arms h _ _ _
  | .locks _ _ body, h, σ, ρ => by
      simp only [Stmt.kOk] at h
      simp only [execStmt, Block.orakel_kOk body h]
  | .breaking _ body, h, σ, ρ => by
      simp only [Stmt.kOk] at h
      simp only [execStmt, Block.orakel_kOk body h]
  | .traverse .., h, _, _ => by simp [Stmt.kOk] at h
  | .retry .., h, _, _ => by simp [Stmt.kOk] at h
  | .forever .., h, _, _ => by simp [Stmt.kOk] at h
  | .axiomCall .., h, _, _ => by simp [Stmt.kOk] at h
  | .callInd .., h, _, _ => by simp [Stmt.kOk] at h
  | .assignSlot .., _, _, _ => rfl
  | .assignDurch .., _, _, _ => rfl
  | .assignGlob .., _, _, _ => rfl
  | .schreibBytes .., _, _, _ => rfl
  | .assignVar .., _, _, _ => rfl
  | .uebergang .., _, _, _ => rfl
  | .call .., _, _, _ => rfl
  | .regSchreib .., _, _, _ => rfl
  | .transition .., _, _, _ => rfl
  | .publish .., _, _, _ => rfl
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret .., _, _, _ => rfl
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.orakel_kOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.kOk = true → ∀ (σ : World D) (ρ : Env D Γ),
      execBlock O passes R b σ ρ = execBlock O' passes R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Block.kOk, Bool.and_eq_true] at h
      simp only [execBlock, Stmt.orakel_kOk s h.1, Block.orakel_kOk rest h.2]
  | .bind _ rest, h, σ, ρ => by
      simp only [Block.kOk] at h
      simp only [execBlock, Block.orakel_kOk rest h]
  | .bindCall _ _ _ _ _ rest, h, σ, ρ => by
      simp only [Block.kOk] at h
      simp only [execBlock, Block.orakel_kOk rest h]
  | .bindCallInd .., h, _, _ => by simp [Block.kOk] at h
  | .bindCallElse .., h, _, _ => by simp [Block.kOk] at h
  | .bindAxiom .., h, _, _ => by simp [Block.kOk] at h
  | .regLies .., h, _, _ => by simp [Block.kOk] at h
  | .regLiesElse .., h, _, _ => by simp [Block.kOk] at h
  | .awaits .., h, _, _ => by simp [Block.kOk] at h
  | .exchange _ _ _ _ rest, h, σ, ρ => by
      simp only [Block.kOk] at h
      simp only [execBlock, Block.orakel_kOk rest h]
  | .narrow _ _ _ sonst rest, h, σ, ρ => by
      simp only [Block.kOk, Bool.and_eq_true] at h
      simp only [execBlock, Endblock.orakel_kOk sonst h.1, Block.orakel_kOk rest h.2]
  | .pruefung _ sonst rest, h, σ, ρ => by
      simp only [Block.kOk, Bool.and_eq_true] at h
      simp only [execBlock, Endblock.orakel_kOk sonst h.1, Block.orakel_kOk rest h.2]
  | .gleit _ _ _ _ _ rest, h, σ, ρ => by
      simp only [Block.kOk] at h
      simp only [execBlock, Block.orakel_kOk rest h]
  | .gleitLit _ _ _ rest, h, σ, ρ => by
      simp only [Block.kOk] at h
      simp only [execBlock, Block.orakel_kOk rest h]
  | .gleitVon _ _ _ rest, h, σ, ρ => by
      simp only [Block.kOk] at h
      simp only [execBlock, Block.orakel_kOk rest h]
  | .gleitNarrow _ _ _ sonst rest, h, σ, ρ => by
      simp only [Block.kOk, Bool.and_eq_true] at h
      simp only [execBlock, Endblock.orakel_kOk sonst h.1, Block.orakel_kOk rest h.2]

theorem Endblock.orakel_kOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.kOk = true → ∀ (σ : World D) (ρ : Env D Γ),
      execEnd O passes R e σ ρ = execEnd O' passes R e σ ρ
  | .ret .., _, _, _ => rfl
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Endblock.kOk, Bool.and_eq_true] at h
      simp only [execEnd, Stmt.orakel_kOk s h.1, Endblock.orakel_kOk rest h.2]
  | .bind _ rest, h, σ, ρ => by
      simp only [Endblock.kOk] at h
      simp only [execEnd, Endblock.orakel_kOk rest h]

theorem Arms.orakel_kOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    {cs : List (Option (Int × Int))} → (arms : Arms D V l Γ Λ Λ' cs) → arms.kOk = true →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
        execArms O passes R arms v σ ρ = execArms O' passes R arms v σ ρ
  | _, .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, h, ⟨⟨0, _⟩, _⟩, σ, ρ => by
      simp only [Arms.kOk, Bool.and_eq_true] at h
      simp only [execArms, Block.orakel_kOk b h.1]
  | _, .cons b rest, h, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ => by
      simp only [Arms.kOk, Bool.and_eq_true] at h
      simp only [execArms]
      exact Arms.orakel_kOk rest h.2 _ σ ρ

theorem GrundArms.orakel_kOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    {n : Nat} → (arms : GrundArms D V l Γ Λ Λ' n) → arms.kOk = true →
      ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
        execGrund O passes R arms r σ ρ = execGrund O' passes R arms r σ ρ
  | _, .nil, _, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, h, ⟨0, _⟩, σ, ρ => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at h
      simp only [execGrund, Block.orakel_kOk b h.1]
  | _, .cons b rest, h, ⟨_ + 1, _⟩, σ, ρ => by
      simp only [GrundArms.kOk, Bool.and_eq_true] at h
      simp only [execGrund]
      exact GrundArms.orakel_kOk rest h.2 _ σ ρ

end

end Orakelfrei

/-- **For a body of the old fragment the new obligation is the old one**:
    the body never consults the oracle, so its triple for the machine's
    oracle is its triple for every oracle. -/
theorem koerperGutV_of_kOk (P : Programm D) (O : Orakel D) (passes : Nat) (f : D.Fn)
    (hk : (P.rumpf f).kOk = true) (h : KoerperGut P O passes f) : KoerperGutV P passes f := by
  intro O' _ R hR hOV σ ρ hreq
  have e : ∀ R' : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f,
      execEnd O' passes R' (P.rumpf f) σ ρ = execEnd O passes R' (P.rumpf f) σ ρ :=
    fun R' => Endblock.orakel_kOk O' O passes R' _ hk σ ρ
  obtain ⟨h1, h2⟩ := h R hR hOV σ ρ hreq
  exact ⟨fun σ' v hx => h1 σ' v (by rw [← e]; exact hx),
    fun g hx => h2 g (by rw [← e]; exact hx)⟩

/-- **`ziel_ort` follows from `ziel_ort_voll`**: with exactly the premises
    of `ziel_ort` (`ZielOrtBeweis.lean`), the old fragment is inside the new
    one and the old obligation gives the new one. -/
theorem ziel_ort_aus_voll (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragment P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGut P O passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_voll P O passes fs sp init e0 hO hvoll (programmImFragmentV_of P fs hFrag) hFuss
    (fun f => koerperGutV_of_kOk P O passes f ((List.all_eq_true.mp hFrag) f (hvoll f)) (hK f))
    hStart hex

/-! ## CUTS:

  What is proved: `ziel_ort_voll` -- over the repaired G, for every program
  whose bodies are in the fragment `vOk` (loops `traverse`/`retry`/
  `forever` with the `forever` budget `passes`, the exits `leave`/`next`,
  reason returns and `let … else`, axiom calls in statement and binding
  position, indirect calls whose candidates' contract carriers are in the
  caller's footprint, and everything `ziel_ort` covered), whose footprint
  check
  passes, whose bodies satisfy `KoerperGutV`, whose start assignment is
  exclusive and meets `StartGut`, with an oracle satisfying `GutO`, every
  reachable machine satisfies `VertragAmOrtG`. Every premise is used:
  `GutO` (rely, held locks, the frame of the machine's axiom answers and of
  the recorded oracle), `hvoll` and `programmImFragmentV` (every residue in
  the fragment), `fussOrtB` (`andereV`), `KoerperGutV` (`popV_ens`,
  `pushV_req`), `StartGut`, `StartExklusiv`, `e0` (fresh trace positions of
  recorded answers). Reason returns: `rufG_grund_treu` (the logged `grund`
  event carries the returned reason; the caller continues in its `else`
  block with it bound). The old theorem is a special case
  (`ziel_ort_aus_voll`, via `koerperGutV_of_kOk`: a body of the old
  fragment never consults the oracle). The witness with all premises
  jointly and a reached run through the loop, the exit, the reason pop and
  the axiom is `ziel_ort_voll_zeuge` (`ZielOrtVollZeuge.lean`).

  What is NOT covered:

  - Register reads (`regLies`, `regLiesElse`) and `awaits`. The sequential
    semantics reads a register as `O.regLies r σ`, a function of the world:
    two reads at the same sequential world give the same answer, so a
    user can prove `let x = R; let y = R; return x == y` returns `true` for
    EVERY oracle. On G the thread world between the two reads changes
    whenever another thread writes any memory (outside the footprint too),
    and a `GutO` oracle may read that memory: the two machine answers
    differ. The premise that would make the extension true -- "register
    and visibility answers do not depend on memory outside the reader's
    footprint" -- is a statement about the ORACLE relative to a PROGRAM'S
    footprint: neither a user obligation, nor a program-independent
    hardware assumption, nor a decidable program fact. Stopped there. The
    counterexample is proved: `ziel_ort_register_falsch`
    (`ZielOrtRegister.lean`) -- the statement of `ziel_ort_voll` with the
    fragment widened by the register forms is false on a two-thread
    program satisfying every other premise. (Axiom calls do not have this
    problem: every recorded axiom answer appends to the sequential trace,
    so no two consultations share a key.)
    Repaired in `ziel_ort_geraet` (`ZielOrtGeraet.lean`): the hardware
    class `RegLokal` (a register answers from its device's carriers) plus
    the widened footprint check `fussOrtGB` admit register reads and
    `awaits`; on register-local oracles `ziel_ort_voll` is a special case
    (`ziel_ort_voll_lokal`).
  - Indirect calls are covered only where every function of the
    pointer's signature has its contract carriers in the caller's footprint
    (`KandOk`, decided by `kandB` over the complete list `fs`); the
    footprint `fussOrte` itself is unchanged, so an indirect caller that
    wants a candidate's contract in its footprint must read those carriers
    (or name them in its own contract).
  - Declarations without any table, global and lock (the `e0` premise):
    recorded answers need a fresh trace position; without events every
    world has the empty trace, keys collapse to (callee, parameters), and
    the replay would need a determinism lemma for G (two returns of a
    callee with equal parameters return equal values). Not proved.
  - A stuck state of G is not a violation: where G replaces a residue by an
    end block that leaves a loop (`leave`/`next` inside an `else` block),
    or a loop invariant is false, or the `forever` budget is spent, G does
    not step, and `VertragAmOrtG` is about the logs of the steps it does.
  - The converse adequacy `rufG_adaequat_ruf_umkehr` (single thread,
    body-running handler) is NOT extended by loops here; the replay above
    is the concurrent converse that `ziel_ort_voll` needs, with the frame
    semantics of every residue (`semV`, `ZielOrtVollSem.lean`).
-/

#print axioms Gabbro.Grammatik.akteurV
#print axioms Gabbro.Grammatik.andereV
#print axioms Gabbro.Grammatik.ziel_ort_voll
#print axioms Gabbro.Grammatik.rufG_grund_treu
#print axioms Gabbro.Grammatik.koerperGutV_of_kOk
#print axioms Gabbro.Grammatik.ziel_ort_aus_voll

end Gabbro.Grammatik
