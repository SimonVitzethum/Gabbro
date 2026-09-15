/-
  File:      Grammatik/ZielOrtGeraet.lean
  Subject:   `ziel_ort_geraet` -- `ziel_ort_voll` with the device forms:
             register reads (with and without `else`), `awaits`, and (as
             before) register writes, `transition`, `exchange`; the acting
             thread keeps its replay under every rule of G, the other threads
             keep theirs by the rely over the widened footprint.

  The replay invariants and steps are in `ZielOrtGeraetBeweis.lean`, the
  hardware class, the widened fragment and footprint, and the frame
  semantics of the device forms in `ZielOrtGeraetSem.lean`.
-/
import Grammatik.ZielOrtGeraetBeweis

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The residue of a frame, read off its rest. -/
theorem rest_okG {F : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hF : F.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (h : F.rest.2.2.2.2.okG P (fussOrteG P F.f)) : r.okG P (fussOrteG P F.f) := by
  rw [hF] at h
  exact h

/-- **The acting thread keeps its replay and its log** -- every rule of G:
    the head-local steps by the residue step lemmas at the sequential
    world, the leaves by leaf locality or by recording an axiom answer, the
    pushes by `pushG_ok` (direct) and `pushG_gen` (indirect: the pointer
    read at the key names the callee, whose contract carriers the fragment
    puts in the footprint), the normal pops by `popG_ens` and `popG_kopf`,
    the reason pops by `popG_kopf`; the register reads and `awaits` by the
    frame semantics of the device forms at the sequential world, whose
    oracle gives the machine's answer there (`regLies_gleich`,
    `sichtbar_gleich`: the device carriers and the awaited global are in
    the footprint, on which the sequential world agrees with the machine
    world). -/
theorem akteurG (hO : GutO O) (hRL : RegLokal O) (hK : ∀ f, KoerperGutG P passes f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (e0 : Ereignis D)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenG P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log) :
    FadenG P O passes (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_blatt e0 hO hF hhead s (.ende rest)
      (fun O' R σ => semV_ende_cons O' passes R s rest σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okG_ende_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_blatt e0 hO hF hhead s (.dann rest k)
      (fun O' R σ => semV_dann_cons O' passes R s rest k σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okG_dann_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann (.cons s .nil) (.ende rest)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_ende_cons hok
    refine ⟨σ, Nat.le_refl _, hg, ⟨by simp [Block.gOk, hks], ?_, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_endeEntf O' passes R s rest σ ρ)⟩
    simpa [blockOrteP] using hss
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok.2.2, fun R O' => ZErg.folgt_refl _⟩
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann t (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    obtain ⟨ht, _⟩ := and_teile hks
    obtain ⟨hc, htS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨ht, htS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_ite O' passes R c t e rest k σ ρ true hw')⟩
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann e (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    obtain ⟨_, he⟩ := and_teile hks
    obtain ⟨hc, _, heS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨he, heS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_ite O' passes R c t e rest k σ ρ false hw')⟩
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (.cons v ρ) (.dann p (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    obtain ⟨hp, _⟩ := and_teile hks
    obtain ⟨hc, hpS, _⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v := by
      rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨hp, hpS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_optSome O' passes R o p a rest k σ ρ v hv')⟩
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann a (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    obtain ⟨_, ha⟩ := and_teile hks
    obtain ⟨hc, _, haS⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none := by
      rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨ha, haS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_optNone O' passes R o p a rest k σ ρ hv')⟩
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
        ⟨some (lo, hi), b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_gOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_tagSome O' passes R v arms rest k σ ρ lo hi b nutz hw')⟩
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (armEnv nutz ρ) (.dann b (.dann rest k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_gOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_tagNone O' passes R v arms rest k σ ρ b nutz hw')⟩
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann b (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hb : grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ) = b := by
      rw [eval_gleichAuf r (fun _ h => hss.1 h) (hg.lese Λ Λ r.orte r.orte) ρ, ← hs₁]; exact hw
    refine ⟨σ.lese Λ r.orte, lese_laenge _ _ _, hg, ⟨?_, ?_, hrest⟩, fun R O' => ?_⟩
    · rw [← hb]; exact grundWahlG_gOk arms _ hks
    · rw [← hb]; exact fun _ h => hss.2 (grundWahlG_orteP arms _ h)
    · rw [← hb]; exact ZErg.folgt_of_eq (semV_grund O' passes R r arms rest k σ ρ)
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.ende rest) σ₁.spur
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
    refine ⟨fadenG_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.dann rest (.schrumpf k)) σ₁.spur
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
    refine ⟨fadenG_lokal hF hhead _ (.dann rest (.schrumpf k)) σ₁.spur
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
    refine ⟨fadenG_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') := by rw [he']; exact h
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, okG_alsBlock sonst k rest.held_iff hkS hsS hrk,
      fun R O' => semV_narrowElse O' passes R e lo' hi' sonst rest k σ ρ h'⟩
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann rest k) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hc, _, hrS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_pruefWahr O' passes R c sonst rest k σ ρ hw')⟩
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hc, hsS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, okG_alsBlock sonst k rest.held_iff hkS hsS hrk,
      fun R O' => semV_pruefFalsch O' passes R c sonst rest k σ ρ hw'⟩
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_breaking O' passes R i body rest k σ ρ)⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann body (.frei L (.dann rest k)))
      (Ereignis.nimmt L (offen (M.faeden u).spur) :: (M.faeden u).spur) (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    exact ⟨σ.nimmt L, Nat.le_succ _, hg, ⟨hks, hss, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_locks O' passes R L hr body rest k σ ρ)⟩
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ k (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ.gibt L, Nat.le_succ _, hg, hok, fun R O' => ZErg.folgt_refl _⟩
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok, fun R O' => ZErg.folgt_refl _⟩
  -- loops
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.trav t inv body (alleIndizes (D.count t)) (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_dannTrav O' passes R t inv body rest k σ ρ)⟩
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (.cons i ρ) (.dann body (.travRest t inv body is k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hinv, hb, hbS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_travNext O' passes R t inv body i is k σ ρ hw')⟩
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' => ZErg.folgt_of_eq (semV_travFort O' passes R t inv body is k i σ ρ)⟩
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ k σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, _, _, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, hk,
      fun R O' => ZErg.folgt_of_eq (semV_travDone O' passes R t inv body k σ ρ hw')⟩
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.wieder n bis body ueber (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    obtain ⟨hb, hu⟩ := and_teile hks
    obtain ⟨hbis, hbS, huS⟩ := teile2 hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hbis, hb, hbS, hu, huS, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_dannRetry O' passes R n bis body ueber rest k σ ρ)⟩
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann (.cons (.ite bis .nil ueber) .nil) k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbS, _, _, hu, huS, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨by simp_all [Block.gOk, Stmt.gOk],
      fun x hx => by
        simp only [blockOrteP, stmtOrteP, List.append_nil, List.mem_append] at hx
        rcases hx with h | h <;> first | exact hbS h | exact huS h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_wiederUeber O' passes R bis body ueber k σ ρ)⟩
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ k σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, _, _, _, _, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true := by
      rw [eval_gleichAuf bis (fun _ h => hbis h) (hg.lese Λ Λ bis.orte bis.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ bis.orte, lese_laenge _ _ _, hg, hk,
      fun R O' => ZErg.folgt_of_eq (semV_wiederWeiter O' passes R n bis body ueber k σ ρ hw')⟩
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann body (.wiederRest n bis body ueber k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, hb, hbS, hu, huS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
      rw [eval_gleichAuf bis (fun _ h => hbis h) (hg.lese Λ Λ bis.orte bis.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ bis.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hbis, hb, hbS, hu, huS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_wiederSchritt O' passes R n bis body ueber k σ ρ hw')⟩
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok,
      fun R O' => ZErg.folgt_of_eq (semV_wiederFort O' passes R n bis body ueber k σ ρ)⟩
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.ewig a passes inv body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okG_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨σ, Nat.le_refl _, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_dannForever O' passes R a inv body rest k σ ρ)⟩
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.dann body (.ewigRest a n inv body k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => hinv h) (hg.lese Λ Λ inv.orte inv.orte) ρ, ← hs₁]
      exact hw
    exact ⟨σ.lese Λ inv.orte, lese_laenge _ _ _, hg, ⟨hb, hbS, hinv, hb, hbS, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_ewigWeiter O' passes R a n inv body k σ ρ hw')⟩
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
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
    refine ⟨fadenG_lokal hF hhead ρ k _ (fun σ hg hok => ?_), hL⟩
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
    refine ⟨fadenG_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, hTR,
      fun R O' => ZErg.folgt_of_eq (semV_nextTrav O' passes R t inv body is k rest i σ ρ hnext)⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenG_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    obtain ⟨_, _, _, _, _, hk⟩ := hWR
    exact ⟨σ, Nat.le_refl _, hg, hk,
      fun R O' => ZErg.folgt_of_eq
        (semV_leaveWieder O' passes R n bis body ueber k rest σ ρ hleave)⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenG_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, hWR,
      fun R O' => ZErg.folgt_of_eq
        (semV_nextWieder O' passes R n bis body ueber k rest σ ρ hnext)⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenG_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    obtain ⟨_, _, _, hk⟩ := hER
    exact ⟨σ, Nat.le_refl _, hg, hk,
      fun R O' => ZErg.folgt_of_eq (semV_leaveEwig O' passes R a n inv body k rest σ ρ hleave)⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenG_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, hER,
      fun R O' => ZErg.folgt_of_eq (semV_nextEwig O' passes R a n inv body k rest σ ρ hnext)⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelDann O' passes R rest b k σ ρ hleave true)⟩
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelDann O' passes R rest b k σ ρ hnext false)⟩
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelSchrumpf O' passes R rest k σ ρ hleave true)⟩
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelSchrumpf O' passes R rest k σ ρ hnext false)⟩
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ _ (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ.gibt L, Nat.le_succ _, hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelFrei O' passes R L rest k σ ρ hleave true)⟩
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ _ (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨σ.gibt L, Nat.le_succ _, hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelFrei O' passes R L rest k σ ρ hnext false)⟩
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelAbbruch O' passes R rest k σ ρ hleave true)⟩
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, hk⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' => ZErg.folgt_of_eq (semV_peelAbbruch O' passes R rest k σ ρ hnext false)⟩
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₂.spur
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
    refine ⟨fadenG_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
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
    refine ⟨fadenG_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_gleitLit O' passes R q lo hi rest k σ ρ v hv)⟩
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have hv' : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
        (σ.lese Λ e.orte) ρ).n) = some v := by
      rw [eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩,
      fun R O' => ZErg.folgt_of_eq (semV_gleitVon O' passes R e lo hi rest k σ ρ v hv')⟩
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
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
    refine ⟨fadenG_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have hn' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none := by
      rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hn
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, okG_alsBlock sonst k rest.held_iff hkS hsS hrk,
      fun R O' => semV_gleitNarrowElse O' passes R e lo hi sonst rest k σ ρ hn'⟩
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
    refine ⟨fadenG_ax e0 hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur a args
      (fun hok => ⟨hok.1, by simpa [blockOrteP] using (teil_append hok.2.1).2, hok.2.2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun O' R σ hz hwk => ?_), hL⟩
    apply ZErg.folgt_of_eq
    show weiterZ O' passes R k (execBlock O' passes R (.bindAxiom a args he hw hg hd hgd rest) σ ρ) = _
    simp only [execBlock, axiomAntwort, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rfl
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushG_ok hO hRL hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okG_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact ⟨hss.1, List.append_subset.mpr hss.2⟩)
      ρ (.ende rest) (fun hok => (okG_ende_cons hok).2.2)
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
    obtain ⟨hFad, hReq⟩ := pushG_ok hO hRL hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okG_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact ⟨hss.1, List.append_subset.mpr hss.2⟩)
      ρ (.dann rest k) (fun hok => (okG_dann_cons hok).2.2)
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
    obtain ⟨hFad, hReq⟩ := pushG_ok hO hRL hK hFrag hF hhead g args
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
    obtain ⟨hFad, hReq⟩ := pushG_ok hO hRL hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hss.1.1.1, List.append_subset.mpr hss.1.1.2⟩)
      ρ (.wartetSonst (D.gruende g) err rest k)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [Block.gOk, Bool.and_eq_true] at hks
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
            rw [semV_alsBlock_schrumpf]
            exact ZErg.folgt_refl _
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  -- indirect calls: the pointer read at the key names the callee
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := okG_dann_cons (kopfG_okG hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (fussOrteG P (M.faeden u).kopf.f) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => hss.1 h) (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushG_gen hO hRL hK hFrag hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => hss.2 h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.dann rest k) (fun hok => (okG_dann_cons hok).2.2)
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
    obtain ⟨hks, hss, _⟩ := okG_ende_cons (kopfG_okG hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (fussOrteG P (M.faeden u).kopf.f) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => hss.1 h) (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushG_gen hO hRL hK hFrag hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => hss.2 h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.ende rest) (fun hok => (okG_ende_cons hok).2.2)
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
    obtain ⟨hks, hss, _⟩ := kopfG_okG hF.1 hhead
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1
    have hev : ∀ σ : World D, GleichAuf (fussOrteG P (M.faeden u).kopf.f) σ (M.weltVon u) →
        eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => hss.1.1 h) (hgσ.lese Λ Λ _ _) ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushG_gen hO hRL hK hFrag hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args (fun _ h => hss.1.2 h) (hgσ.lese Λ Λ _ _) ρ])
      ρ (.wartet rest k)
      (fun hok => by
        obtain ⟨hks', hss', hk⟩ := hok
        simp only [Block.gOk, Bool.and_eq_true] at hks'
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
    have hok := kopfG_okG hF.1 hhead
    have hens := popG_ens hO hRL hK hF.1 hhead e hok.2
      (fun O' R σ => semV_rueck O' passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okG_ende_cons (kopfG_okG hF.1 hhead)
    have hens := popG_ens hO hRL hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_rueckCons O' passes R e hperm rest σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okG_dann_cons (kopfG_okG hF.1 hhead)
    have hens := popG_ens hO hRL hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_dannRet O' passes R e hperm rest k σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 id (fun R O' σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfG_okG hF.1 hhead
    have hens := popG_ens hO hRL hK hF.1 hhead e hok.2
      (fun O' R σ => semV_rueck O' passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okG hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okG hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okG_dann_cons (kopfG_okG hF.1 hhead)
    have hens := popG_ens hO hRL hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_dannRet O' passes R e hperm restk kk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okG hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okG hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okG_ende_cons (kopfG_okG hF.1 hhead)
    have hens := popG_ens hO hRL hK hF.1 hhead e hok.2.1
      (fun O' R σ => semV_rueckCons O' passes R e hperm restk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨popG_kopf e0 hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okG hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okG hc hokc
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
    refine ⟨⟨popG_kopf e0 hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun hokc => okG_alsBlock err (.schrumpf k) restb.held_iff (rest_okG hcaller hokc).1
        (rest_okG hcaller hokc).2.1 (rest_okG hcaller hokc).2.2.2.2)
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
    refine ⟨⟨popG_kopf e0 hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun hokc => okG_alsBlock err (.schrumpf k) restb.held_iff (rest_okG hcaller hokc).1
        (rest_okG hcaller hokc).2.1 (rest_okG hcaller hokc).2.2.2.2)
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
    refine ⟨⟨popG_kopf e0 hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun hokc => okG_alsBlock err (.schrumpf k) restb.held_iff (rest_okG hcaller hokc).1
        (rest_okG hcaller hokc).2.1 (rest_okG hcaller hokc).2.2.2.2)
      (fun R O' σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  -- register reads and `awaits`: the sequential oracle answers what the machine read
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP] at hss
    refine ⟨σ, Nat.le_refl _, hg, ⟨hks.2, hss, hrest⟩, fun R O' hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_ok hks.1) hg
    exact ZErg.folgt_of_eq
      (semV_regLies O' passes R r hk rest k σ ρ v (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hz)
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    obtain ⟨⟨hzS, _⟩, hrS⟩ := hss
    have hw' : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) =
        true := by
      rw [eval_gleichAuf zusage (fun _ h => hzS h) (hg.lese Λ Λ zusage.orte zusage.orte), ← hs₁]
      exact hw
    refine ⟨σ.lese Λ zusage.orte, lese_laenge _ _ _, hg, ⟨hks.2.2, hrS, hrest⟩,
      fun R O' hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_ok hks.1) hg
    exact ZErg.folgt_of_eq (semV_regLiesElseWahr O' passes R r hk zusage sonst rest k σ ρ v
      (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hw')
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu
      hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokalQ hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    obtain ⟨⟨hzS, hsS⟩, _⟩ := hss
    have hw' : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) =
        false := by
      rw [eval_gleichAuf zusage (fun _ h => hzS h) (hg.lese Λ Λ zusage.orte zusage.orte), ← hs₁]
      exact hw
    refine ⟨σ.lese Λ zusage.orte, lese_laenge _ _ _, hg,
      okG_alsBlock sonst k rest.held_iff hks.2.1 hsS hrk, fun R O' hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_ok hks.1) hg
    exact semV_regLiesElseFalsch O' passes R r hk zusage sonst rest k σ ρ v
      (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hw'
  | dannAwaits l Γ Λ Λ' g payload hp hLg rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenG_lokalQ hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk] at hks
    simp only [blockOrteP, List.cons_subset] at hss
    have hglob : (σ.lese Λ [.inr g]).globs g = σ₁.globs g := by
      rw [hs₁]
      exact hg.2 g hss.1
    refine ⟨σ.lese Λ [.inr g], lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩, fun R O' hQ => ?_⟩
    have hsv : O'.sichtbar g σ = true := by
      rw [sichtbar_gleich hRL hQ g hss.1 hg]
      exact hvis
    have h1 := semV_awaits O' passes R g payload hp hLg rest k σ ρ hsv
    rw [hglob] at h1
    exact ZErg.folgt_of_eq h1

end Akteur

/-! ## 2. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for the replay** (as `andere_ok`): a step of thread `u`
    leaves the footprint of every head frame of another thread alone. -/
theorem andereG (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenG P O passes (M.faeden t) (M.weltVon t)) :
    FadenG P O passes (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenG_speicher hF (fun c hc => ?_)
  rcases fussOrtGB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** -/
theorem zielInvG_start
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInvG P O passes (RufStartG P sp init) := by
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
      rahmenA_nil, kurzA_nil _, GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpfG P _⟩,
      fun R O' _ _ _ => ZErg.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant. -/
theorem zielInvG_schritt (hO : GutO O) (hRL : RegLokal O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (hK : ∀ f, KoerperGutG P passes f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvG P O passes M) :
    ZielInvG P O passes M' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteurG hO hRL hK hFrag e0 hs (hI.1 t) (hI.2 t)).1
    · exact andereG hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteurG hO hRL hK hFrag e0 hs (hI.1 t) (hI.2 t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **ZIEL AM ORT WITH DEVICES -- contracts hold at their place on every
    machine of the repaired concurrent call machine G, for bodies with
    loops, exits, the error channel, axiom calls, indirect calls, register
    reads (with and without `else`), register writes, `transition`,
    `exchange` and `awaits`.**

    Premises, by class:
    * (a) user obligations: `KoerperGutG P passes f` for every function
      (the body's Hoare triple over the SEQUENTIAL semantics with any
      contract-respecting call handler AND any oracle that respects the
      declared axiom frames and is register-local, and its caller duty),
      `StartGut` and `StartExklusiv` (the boot assignment);
    * (b) hardware: `GutO O` (axiom answers inside their declared frames)
      and `RegLokal O` (a register answers from its device's carriers
      `D.rtraeger r`, the visibility answer of `awaits g` from `g`);
    * (c) decidable program facts over a complete member list `fs`: the
      widened fragment (`programmImFragmentG`: every form; an indirect call
      only where every function of its signature has its contract carriers
      in the caller's widened footprint) and the widened footprint check
      (`fussOrtGB`: every carrier of `fussOrteG` -- the footprint of
      `ziel_ort_voll` plus the device carriers of every register the body
      reads -- is guarded by a signature lock of the function or written by
      no function);
    * the declaration declares a table, a global or a lock (`e0`, as in
      `ziel_ort_voll`).

    Conclusion: `VertragAmOrtG` on EVERY machine reachable from the start
    machine. -/
theorem ziel_ort_geraet (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutG P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  have hFragF : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true :=
    programmImFragmentG_ok P hvoll hFrag
  intro M hr
  have hI : ZielInvG P O passes M := by
    induction hr with
    | start => exact zielInvG_start hFragF sp init hStart
    | schritt M M' u hr' hs ih =>
        exact zielInvG_schritt hO hRL hvoll hFuss hK hFragF e0 sp init hex hr' hs ih
  exact fun t ev hev => hI.2 t ev hev

end Ziel

/-! ## 3. `ziel_ort_voll` on register-local oracles is a special case -/

/-- **`ziel_ort_voll` follows from `ziel_ort_geraet` for every
    register-local oracle**: with the premises of `ziel_ort_voll` and
    `RegLokal O`, the old fragment is inside the widened one, the old
    footprint check is the widened one there (no register is read), and the
    old obligation gives the new one. (`ziel_ort_voll` itself, without
    `RegLokal`, stays as it is.) -/
theorem ziel_ort_voll_lokal (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutV P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_geraet P O passes fs sp init e0 hO hRL hvoll (programmImFragmentG_of_V P fs hFrag)
    (fussOrtGB_of_V P fs hFrag hFuss) (fun f => koerperGutG_of_V (hK f)) hStart hex

/-! ## CUTS:

  What is proved: `ziel_ort_geraet` -- over the repaired G, for every
  program in the widened fragment (every form of `ziel_ort_voll`'s fragment
  plus `let x = R`, `let x = R else …` and `awaits`; register writes,
  `transition` and `exchange` were already in), whose widened footprint
  check passes, whose bodies satisfy `KoerperGutG`, whose start assignment
  is exclusive and meets `StartGut`, with an oracle satisfying `GutO` and
  `RegLokal`, every reachable machine satisfies `VertragAmOrtG`. Every
  premise is used: `GutO` (rely, held locks, axiom frames), `RegLokal` (the
  register and visibility steps of `akteurG`; the record oracle is local
  for the user obligation in `popG_ens`/`pushG_req`), `hvoll` and
  `programmImFragmentG` (every residue in the widened fragment, every
  register read with its device carriers in the footprint), `fussOrtGB`
  (`andereG`: the device carriers are protected like every footprint
  carrier), `KoerperGutG`, `StartGut`, `StartExklusiv`, `e0`. On
  register-local oracles `ziel_ort_voll` is a special case
  (`ziel_ort_voll_lokal`). The counterexample of `ZielOrtRegister.lean` is
  excluded by `RegLokal` (`ziel_ort_register_ausgeschlossen`,
  `ZielOrtGeraetAus.lean`); the witness with all premises jointly is
  `ziel_ort_geraet_zeuge` (`ZielOrtGeraetZeuge.lean`).

  What is NOT covered:

  - Device-driven change as a machine step of its own. A device that
    changes its state by itself is modelled by a declared write to its
    carriers (an axiom whose frame names them, recorded like every axiom
    answer); G has no asynchronous device step (`GeraetSchreibt` in
    `Semantik.lean` is a shape beside the run), so a register whose answer
    changes between two reads with NO write to its carriers violates
    `RegLokal` and is outside the theorem.
  - The device carriers must be protected like every footprint carrier: a
    lock the reader holds BY SIGNATURE, or no writer at all
    (`fussOrtGB`). A reader that takes the device lock in a `locks` block
    only is not covered (the same restriction as `fussOrtB`).
  - `RegLokal`'s visibility half is minimal (the awaited global only); an
    answer that depends on the payload globals of `publishes` is outside it.
  - `ziel_ort_voll` for NON-local oracles is not derived from
    `ziel_ort_geraet` (it stays as proved); the other cuts of
    `ziel_ort_voll` (no-event declarations, stuck states, the converse
    adequacy) carry over unchanged.
-/

#print axioms Gabbro.Grammatik.akteurG
#print axioms Gabbro.Grammatik.andereG
#print axioms Gabbro.Grammatik.ziel_ort_geraet
#print axioms Gabbro.Grammatik.ziel_ort_voll_lokal

end Gabbro.Grammatik
