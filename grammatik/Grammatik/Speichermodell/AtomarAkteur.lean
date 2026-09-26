/-
  File:      Grammatik/Speichermodell/AtomarAkteur.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 3: the acting thread keeps its replay, every
             rule of G (`akteurSA`, the twin of `akteurS` in ZielOrtSperre.lean). Every rule
             that READS goes through `fadenSA_lese` (or records its read in `pushSA_gen`,
             `fadenSA_ax`, `popSA_ens`): the read is answered from the machine's presented
             memory at the shared atomics it touches. Opus lane O25b, 2026-09-26. Standalone.

  The step is a step of G from ANY machine `M` -- in particular from a machine whose memory at
  the shared atomics is what the weak memory presented (machine GA, Atomar.lean). Nothing here
  depends on how `M` was reached: the replay invariant `FadenSA` is the whole premise.
-/
import Grammatik.Speichermodell.AtomarReplay

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

set_option maxHeartbeats 8000000 in
/-- **The acting thread keeps its replay and its log** -- every rule of G, over the semantics
    with the atomic rely. -/
theorem akteurSA (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenSA P O passes Q S lok Tg (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
    (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel)
    (hSG : SperrInvG S M) :
    FadenSA P O passes Q S lok Tg (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_blatt hO hQ hlok hFS hF hhead s (.ende rest)
      (fun O' R U A σ => semHA_ende_cons S O' U A passes R s rest σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okS_ende_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_blatt hO hQ hlok hFS hF hhead s (.dann rest k)
      (fun O' R U A σ => semHA_dann_cons S O' U A passes R s rest k σ ρ)
      (fun hok => by
        obtain ⟨_, hss, hrest⟩ := okS_dann_cons hok
        exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.dann (.cons s .nil) (.ende rest)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_ende_cons hok
    refine ⟨rfl, hg, ⟨by simp [Block.gOk, hks], ?_, hrest⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_endeEntf S O' U A passes R s rest σ ρ)⟩
    simpa [blockOrteP] using hss
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨rfl, hg, hok.2.2, fun R O' U A => ZErgG.folgt_refl _⟩
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann t (.dann rest k)) _ Λ c.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        obtain ⟨hc, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) c hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨ht, _⟩ := and_teile hks
    obtain ⟨_, htS, _⟩ := teile2 hss
    have hw' : wahr? (eval σ c σ ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨ht, htS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_ite S O' U A passes R c t e rest k σ0 ρ true (by rw [hσ0]; exact hw'), hσ0] <;> rfl)⟩
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann e (.dann rest k)) _ Λ c.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        obtain ⟨hc, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) c hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨_, he⟩ := and_teile hks
    obtain ⟨_, _, heS⟩ := teile2 hss
    have hw' : wahr? (eval σ c σ ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨he, heS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_ite S O' U A passes R c t e rest k σ0 ρ false (by rw [hσ0]; exact hw'), hσ0] <;> rfl)⟩
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons v ρ) (.dann p (.schrumpf (.dann rest k))) _ Λ o.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        obtain ⟨hc, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) o hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨hp, _⟩ := and_teile hks
    obtain ⟨_, hpS, _⟩ := teile2 hss
    have hv' : eval σ o σ ρ = Option.some v := by
      rw [eval_gleichAuf o (fun _ h => List.mem_append_right _ h) hg ρ]; exact hv
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hp, hpS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_optSome S O' U A passes R o p a rest k σ0 ρ v (by rw [hσ0]; exact hv'), hσ0])⟩
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann a (.dann rest k)) _ Λ o.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        obtain ⟨hc, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) o hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨_, ha⟩ := and_teile hks
    obtain ⟨_, _, haS⟩ := teile2 hss
    have hv' : eval σ o σ ρ = Option.none := by
      rw [eval_gleichAuf o (fun _ h => List.mem_append_right _ h) hg ρ]; exact hv
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨ha, haS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_optNone S O' U A passes R o p a rest k σ0 ρ (by rw [hσ0]; exact hv'), hσ0])⟩
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k))) _ Λ v.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) v hss.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval σ v σ ρ) = ⟨some (lo, hi), b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨armWahlG_gOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_tagSome S O' U A passes R v arms rest k σ0 ρ lo hi b nutz
          (by rw [hσ0]; exact hw'), hσ0] <;> rfl)⟩
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (armEnv nutz ρ) (.dann b (.dann rest k)) _ Λ v.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) v hss.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval σ v σ ρ) = ⟨none, b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨armWahlG_gOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_tagNone S O' U A passes R v arms rest k σ0 ρ b nutz
          (by rw [hσ0]; exact hw'), hσ0] <;> rfl)⟩
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann b (.dann rest k)) _ Λ r.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) r hss.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hb : grundWahlG arms (eval σ r σ ρ) = b := by
      rw [eval_gleichAuf r (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨?_, ?_, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    · rw [← hb]; exact grundWahlG_gOk arms _ hks
    · rw [← hb]; exact fun _ h => hss.2 (grundWahlG_orteP arms _ h)
    · rw [← hb]
      refine ZErgG.folgt_of_eq ?_
      rw [semHA_grund S O' U A passes R r arms rest k σ0 ρ, hσ0]
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons (eval _ e _ ρ) ρ) (.ende rest) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss⟩ := hok
        simp only [endblockOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) e hss.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss⟩ := hok
    simp only [endblockOrteP, List.append_subset] at hss
    have he' : eval σ e σ ρ = eval ((M.weltVon u).lese Λ e.orte) e ((M.weltVon u).lese Λ e.orte) ρ :=
      eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hks, hss.2⟩, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_endeBind S O' U A passes R e rest σ0 ρ
    rw [hσ0, he'] at h1
    exact ZErgG.folgt_of_eq h1
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons (eval _ e _ ρ) ρ) (.dann rest (.schrumpf k)) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) e hss.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have he' : eval σ e σ ρ = eval ((M.weltVon u).lese Λ e.orte) e ((M.weltVon u).lese Λ e.orte) ρ :=
      eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hks, hss.2, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_dannBind S O' U A passes R e rest k σ0 ρ
    rw [hσ0, he'] at h1
    exact ZErgG.folgt_of_eq h1
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead _ (.dann rest (.schrumpf k)) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨hes, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) e hes)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨_, _, hrS⟩ := teile2 hss
    have he' : eval σ e σ ρ = eval ((M.weltVon u).lese Λ e.orte) e ((M.weltVon u).lese Λ e.orte) ρ :=
      eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ
    have h' : lo' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ hi' := by rw [he']; exact h
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hkr, hrS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_narrowOk S O' U A passes R e lo' hi' sonst rest k σ0 ρ (by rw [hσ0]; exact h')
    have hz : (⟨(eval (leseA A σ0 Λ e.orte) e (leseA A σ0 Λ e.orte) ρ).n,
        (by rw [hσ0]; exact h' : lo' ≤ (eval (leseA A σ0 Λ e.orte) e (leseA A σ0 Λ e.orte) ρ).n ∧
          (eval (leseA A σ0 Λ e.orte) e (leseA A σ0 Λ e.orte) ρ).n ≤ hi').1,
        (by rw [hσ0]; exact h' : lo' ≤ (eval (leseA A σ0 Λ e.orte) e (leseA A σ0 Λ e.orte) ρ).n ∧
          (eval (leseA A σ0 Λ e.orte) e (leseA A σ0 Λ e.orte) ρ).n ≤ hi').2⟩ :
        Wert D (.int lo' hi')) =
        ⟨(eval ((M.weltVon u).lese Λ e.orte) e ((M.weltVon u).lese Λ e.orte) ρ).n, h.1, h.2⟩ := by
      simp only [hσ0, he']
    rw [hz, hσ0] at h1
    exact ZErgG.folgt_of_eq h1
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨hes, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) e hes)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨_, hsS, _⟩ := teile2 hss
    have he' : eval σ e σ ρ = eval ((M.weltVon u).lese Λ e.orte) e ((M.weltVon u).lese Λ e.orte) ρ :=
      eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ
    have h' : ¬ (lo' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ hi') := by rw [he']; exact h
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      okS_alsBlock sonst k rest.held_iff hkS hsS hrk, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_narrowElse S O' U A passes R e lo' hi' sonst rest k σ0 ρ (by rw [hσ0]; exact h')
    rw [hσ0] at h1
    exact h1
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann rest k) _ Λ c.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨hc, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) c hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨_, _, hrS⟩ := teile2 hss
    have hw' : wahr? (eval σ c σ ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hkr, hrS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_pruefWahr S O' U A passes R c sonst rest k σ0 ρ (by rw [hσ0]; exact hw'), hσ0])⟩
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) _ Λ c.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨hc, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) c hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨_, hsS, _⟩ := teile2 hss
    have hw' : wahr? (eval σ c σ ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      okS_alsBlock sonst k rest.held_iff hkS hsS hrk, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_pruefFalsch S O' U A passes R c sonst rest k σ0 ρ (by rw [hσ0]; exact hw')
    rw [hσ0] at h1
    exact h1
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.dann body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    exact ⟨rfl, hg, ⟨hks, hss, hrest⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_breaking S O' U A passes R i body rest k σ ρ)⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hinv : S.inv L (M.weltVon u).speicher = true := by
      show S.inv L M.speicher = true
      refine hSG L fun t => ?_
      by_cases htu : t = u
      · subst htu
        exact hself
      · exact hfrei t htu
    exact ⟨fadenSA_locks hF L hr body rest k ρ hhead hinv _, hL⟩
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenSA_frei hO hRL hQ hS hsp hK hF L k ρ hhead _, hL⟩
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨rfl, hg, hok, fun R O' U A => ZErgG.folgt_refl _⟩
  -- loops
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.trav t inv body (alleIndizes (D.count t)) (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨rfl, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_dannTrav S O' U A passes R t inv body rest k σ ρ)⟩
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons i ρ) (.dann body (.travRest t inv body is k)) _ Λ inv.orte
      (fun hok => expr_stabilX (hFS _) inv hok.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval σ inv σ ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hb, hbS, hinv, hb, hbS, hk⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_travNext S O' U A passes R t inv body i is k σ0 ρ (by rw [hσ0]; exact hw'), hσ0])⟩
  | travFort l Γ Λ t inv body is k i ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨rfl, hg, hok,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_travFort S O' U A passes R t inv body is k i σ ρ)⟩
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ k _ Λ inv.orte (fun hok => expr_stabilX (hFS _) inv hok.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, _, _, hk⟩ := hok
    have hw' : wahr? (eval σ inv σ ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg, hk,
      fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_travDone S O' U A passes R t inv body k σ0 ρ (by rw [hσ0]; exact hw'), hσ0])⟩
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.wieder n bis body ueber (.dann rest k))
      (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    obtain ⟨hb, hu⟩ := and_teile hks
    obtain ⟨hbis, hbS, huS⟩ := teile2 hss
    exact ⟨rfl, hg, ⟨hbis, hb, hbS, hu, huS, hrest⟩,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_dannRetry S O' U A passes R n bis body ueber rest k σ ρ)⟩
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.dann (.cons (.ite bis .nil ueber) .nil) k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbS, _, _, hu, huS, hk⟩ := hok
    exact ⟨rfl, hg, ⟨by simp_all [Block.gOk, Stmt.gOk],
      fun x hx => by
        simp only [blockOrteP, stmtOrteP, List.append_nil, List.mem_append] at hx
        rcases hx with h | h <;> first | exact hbS h | exact huS h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_wiederUeber S O' U A passes R bis body ueber k σ ρ)⟩
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ k _ Λ bis.orte (fun hok => expr_stabilX (hFS _) bis hok.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, _, _, _, _, hk⟩ := hok
    have hw' : wahr? (eval σ bis σ ρ) = true := by
      rw [eval_gleichAuf bis (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg, hk,
      fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_wiederWeiter S O' U A passes R n bis body ueber k σ0 ρ
          (by rw [hσ0]; exact hw'), hσ0])⟩
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann body (.wiederRest n bis body ueber k)) _ Λ bis.orte
      (fun hok => expr_stabilX (hFS _) bis hok.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hbis, hb, hbS, hu, huS, hk⟩ := hok
    have hw' : wahr? (eval σ bis σ ρ) = false := by
      rw [eval_gleichAuf bis (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hb, hbS, hbis, hb, hbS, hu, huS, hk⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_wiederSchritt S O' U A passes R n bis body ueber k σ0 ρ
          (by rw [hσ0]; exact hw'), hσ0])⟩
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨rfl, hg, hok,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_wiederFort S O' U A passes R n bis body ueber k σ ρ)⟩
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.ewig a passes inv body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okS_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    exact ⟨rfl, hg, ⟨hss.1, hks, hss.2, hrest⟩,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_dannForever S O' U A passes R a inv body rest k σ ρ)⟩
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann body (.ewigRest a n inv body k)) _ Λ inv.orte
      (fun hok => expr_stabilX (hFS _) inv hok.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hinv, hb, hbS, hk⟩ := hok
    have hw' : wahr? (eval σ inv σ ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hb, hbS, hinv, hb, hbS, hk⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_ewigWeiter S O' U A passes R a n inv body k σ0 ρ (by rw [hσ0]; exact hw'), hσ0])⟩
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    exact ⟨rfl, hg, hok,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_ewigFort S O' U A passes R a n inv body k σ ρ)⟩
  -- the exits
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ k _ Λ inv.orte
      (fun hok => by
        obtain ⟨_, _, hTR⟩ := hok
        obtain ⟨hinv, _, _, _⟩ := hTR
        intro c hc
        rcases expr_stabilX (hFS _) inv hinv c hc with h | h
        · exact Or.inl (stabilS_iff (fun L => Block.held_iff rest L) h)
        · exact Or.inr h)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    obtain ⟨_, _, _, hk⟩ := hTR
    have hw' : wahr? (eval σ inv σ ρ) = true := by
      rw [eval_gleichAuf inv (fun _ h => List.mem_append_right _ h) hg ρ]; exact hw
    exact ⟨σ, Nat.le_refl _, gleichAuf_stabil_iff (fun L => Block.held_iff rest L)
      (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg), hk,
      fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_leaveTrav S O' U A passes R t inv body is k rest i σ0 ρ hleave
          (by rw [hσ0]; exact hw'), hσ0])⟩
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenSA_lokal hF hhead ρ (.trav t inv body is k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hTR⟩ := hok
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hTR,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_nextTrav S O' U A passes R t inv body is k rest i σ ρ hnext)⟩
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    obtain ⟨_, _, _, _, _, hk⟩ := hWR
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_leaveWieder S O' U A passes R n bis body ueber k rest σ ρ hleave)⟩
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenSA_lokal hF hhead ρ (.wieder n bis body ueber k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hWR⟩ := hok
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hWR,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_nextWieder S O' U A passes R n bis body ueber k rest σ ρ hnext)⟩
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    obtain ⟨_, _, _, hk⟩ := hER
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hk,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_leaveEwig S O' U A passes R a n inv body k rest σ ρ hleave)⟩
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    simp only [execStmt] at hstep
    cases hstep
    refine ⟨fadenSA_lokal hF hhead ρ (.ewig a n inv body k) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hER⟩ := hok
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg, hER,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_nextEwig S O' U A passes R a n inv body k rest σ ρ hnext)⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨rfl,
      gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_peelDann S O' U A passes R rest b k σ ρ hleave true)⟩
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, _, _, hk⟩ := hok
    exact ⟨rfl,
      gleichAuf_stabil_iff (fun L => (Block.held_iff b L).trans (Block.held_iff rest L)) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_peelDann S O' U A passes R rest b k σ ρ hnext false)⟩
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_peelSchrumpf S O' U A passes R rest k σ ρ hleave true)⟩
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ.tail _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hk⟩ := hok
    exact ⟨rfl, gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_peelSchrumpf S O' U A passes R rest k σ ρ hnext false)⟩
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenSA_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hleave true hhead _, hL⟩
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenSA_peelFrei hO hRL hQ hS hsp hK hF L rest k ρ hnext false hhead _, hL⟩
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hiff, hk⟩ := hok
    exact ⟨rfl,
      gleichAuf_stabil_iff (fun L => (hiff L).trans (Block.held_iff rest L)) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_peelAbbruch S O' U A passes R rest k σ ρ hleave true)⟩
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead ρ _ (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨_, _, hiff, hk⟩ := hok
    exact ⟨rfl,
      gleichAuf_stabil_iff (fun L => (hiff L).trans (Block.held_iff rest L)) hg,
      ⟨rfl, fun _ h => by simp [blockOrteP, stmtOrteP] at h, hk⟩,
      fun R O' U A => ZErgG.folgt_of_eq
        (semHA_peelAbbruch S O' U A passes R rest k σ ρ hnext false)⟩
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₂ hs₁
    refine ⟨fadenSA_lese hF hhead _ (.dann rest (.schrumpf k)) _ Λ (.inr g :: neuE.orte)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.cons_subset, List.append_subset] at hss
        obtain ⟨⟨hgS, hnS⟩, _⟩ := hss
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact stabil_of_fussX (hFS _) hgS fun L hB => bewacht_held (c := .inr g) hLg hB
        · exact expr_stabilX (hFS _) neuE hnS c hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.cons_subset, List.append_subset] at hss
    obtain ⟨_, hrS⟩ := hss
    have hglob : σ.globs g = ((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g :=
      hg.2 g (List.mem_append_right _ List.mem_cons_self)
    have hval : eval σ neuE σ (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
        eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) :=
      eval_gleichAuf neuE (fun _ h => List.mem_append_right _ (List.mem_cons_of_mem _ h)) hg _
    refine ⟨σ.schreibGlob g Λ
        (eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ)),
      spur_laenge_erw (Erw.schreibGlob _ _ _ _),
      gleichAuf_schreibGlob (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg) g Λ Λ _,
      ⟨hks, hrS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_exchange S O' U A passes R g neuE hw hLg rest k σ0 ρ
    rw [hσ0, hglob, hval] at h1
    exact ZErgG.folgt_of_eq h1
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) _ Λ (a.orte ++ b.orte)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨haS, hbS, _⟩ := teile2 hss
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact expr_stabilX (hFS _) a haS c hc
        · exact expr_stabilX (hFS _) b hbS c hc)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, _, hrS⟩ := teile2 hss
    have hv' : gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) = some v := by
      rw [eval_gleichAuf a (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) hg ρ,
        eval_gleichAuf b (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) hg ρ]
      exact hv
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hks, hrS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_gleit S O' U A passes R op a b lo hi rest k σ0 ρ v (by rw [hσ0]; exact hv'),
          hσ0])⟩
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    exact ⟨rfl, hg, ⟨hks, hss, hrest⟩,
      fun R O' U A => ZErgG.folgt_of_eq (semHA_gleitLit S O' U A passes R q lo hi rest k σ ρ v hv)⟩
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) e hss.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have hv' : gleitPasst lo hi (gleitAusInt (eval σ e σ ρ).n) = some v := by
      rw [eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ]; exact hv
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hks, hss.2, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_gleitVon S O' U A passes R e lo hi rest k σ0 ρ v (by rw [hσ0]; exact hv'), hσ0])⟩
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨hes, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) e hes)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨_, _, hrS⟩ := teile2 hss
    have hv' : gleitPasst lo hi (eval σ e σ ρ).x = some v := by
      rw [eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ]; exact hv
    exact ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hkr, hrS, hrest⟩, fun R O' U A σ0 _ _ hσ0 => ZErgG.folgt_of_eq (by
        rw [semHA_gleitNarrowOk S O' U A passes R e lo hi sonst rest k σ0 ρ v
          (by rw [hσ0]; exact hv'), hσ0])⟩
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) _ Λ e.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        obtain ⟨hes, _, _⟩ := teile2 hss
        exact expr_stabilX (hFS _) e hes)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨_, hsS, _⟩ := teile2 hss
    have hn' : gleitPasst lo hi (eval σ e σ ρ).x = none := by
      rw [eval_gleichAuf e (fun _ h => List.mem_append_right _ h) hg ρ]; exact hn
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      okS_alsBlock sonst k rest.held_iff hkS hsS hrk, fun R O' U A σ0 _ _ hσ0 => ?_⟩
    have h1 := semHA_gleitNarrowElse S O' U A passes R e lo hi sonst rest k σ0 ρ
      (by rw [hσ0]; exact hn')
    rw [hσ0] at h1
    exact h1
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
    refine ⟨fadenSA_ax hF hhead (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun _ => Iff.rfl) a args
      (fun hok => args_stabilX (hFS _) args
        (by simpa [blockOrteP] using (teil_append hok.2.1).1))
      (fun hok => ⟨hok.1, by simpa [blockOrteP] using (teil_append hok.2.1).2, hok.2.2⟩)
      (σ₂, (O.wirkt a ((M.weltVon u).lese Λ args.orte)
        (evalArgs ((M.weltVon u).lese Λ args.orte) args ((M.weltVon u).lese Λ args.orte) ρ)).2)
      hfr (fun _ => rfl) hlok (fun w hw' => by rw [e2]; exact hQ a _ _ w hw')
      (fun O' R U A σ0 κ hz hκ hwk => ?_), hL⟩
    apply ZErgG.folgt_of_eq
    show weiterHA S O' U A passes R k
      (execBlockHA S O' U A passes R (.bindAxiom a args he hw hg hd hgd rest) σ0 ρ) = _
    simp only [execBlockHA, axiomAntwort, hκ, hwk, (show O'.zeiger = O.zeiger from hz), hv]
    rfl
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact args_stabilX (hFS _) args hss.1)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact vertrag_stabilX (hFS _) hTV g hp (List.append_subset.mpr hss.2))
      (fun _ σ hgσ => evalArgs_gleichAuf args (fun _ h => List.mem_append_right _ h) hgσ ρ)
      ρ (.ende rest) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_ende_cons hok).2.2)
      (fun O' U A R σ κ e _ hκ h => by
        rw [semHA_ende_cons]
        simp only [execStmtHA, hκ, h]
        rfl)
      (fun O' U A R σ κ _ hκ => by
        rw [semHA_ende_cons]
        simp only [execStmtHA, hκ]
        cases R g κ (evalArgs κ args κ ρ) with
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
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact args_stabilX (hFS _) args hss.1)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okS_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact vertrag_stabilX (hFS _) hTV g hp (List.append_subset.mpr hss.2))
      (fun _ σ hgσ => evalArgs_gleichAuf args (fun _ h => List.mem_append_right _ h) hgσ ρ)
      ρ (.dann rest k) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_dann_cons hok).2.2)
      (fun O' U A R σ κ e _ hκ h => by
        rw [semHA_dann_cons]
        simp only [execStmtHA, hκ, h]
        exact weiterHA_logik S O' U A passes R _ e)
      (fun O' U A R σ κ _ hκ => by
        rw [semHA_dann_cons]
        simp only [execStmtHA, hκ]
        cases R g κ (evalArgs κ args κ ρ) with
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
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact args_stabilX (hFS _) args hss.1.1)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact vertrag_stabilX (hFS _) hTV g hp (List.append_subset.mpr hss.1.2))
      (fun _ σ hgσ => evalArgs_gleichAuf args (fun _ h => List.mem_append_right _ h) hgσ ρ)
      ρ (.wartet rest k) (fun L => held_nachSig_iff _ _ L)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks, hss.2, hk⟩)
      (fun O' U A R σ κ e _ hκ h => by
        rw [semHA_dann]
        simp only [execBlockHA, hκ, h]
        exact weiterHA_logik S O' U A passes R _ e)
      (fun O' U A R σ κ _ hκ => by
        rw [semHA_dann]
        simp only [execBlockHA, hκ]
        cases R g κ (evalArgs κ args κ ρ) with
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
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead args.orte g
      (fun κ => evalArgs κ args κ ρ)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact args_stabilX (hFS _) args hss.1.1.1)
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact vertrag_stabilX (hFS _) hTV g hp (List.append_subset.mpr hss.1.1.2))
      (fun _ σ hgσ => evalArgs_gleichAuf args (fun _ h => List.mem_append_right _ h) hgσ ρ)
      ρ (.wartetSonst (D.gruende g) err rest k) (fun L => held_nachSig_iff _ _ L)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [Block.gOk, Bool.and_eq_true] at hks
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks.1, hss.1.2, hks.2, hss.2, hk⟩)
      (fun O' U A R σ κ e _ hκ h => by
        rw [semHA_dann]
        simp only [execBlockHA, hκ, h]
        exact weiterHA_logik S O' U A passes R _ e)
      (fun O' U A R σ κ _ hκ => by
        rw [semHA_dann]
        simp only [execBlockHA, hκ]
        cases R g κ (evalArgs κ args κ ρ) with
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
            rw [semHA_alsBlock_schrumpf]
            exact ZErgG.folgt_refl _
        | logik e => trivial
        | hardware e => trivial)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  -- indirect calls: the pointer read at the key names the callee
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hks, hss, _⟩ := okS_dann_cons (kopfSA_okS hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++
        (p.orte ++ args.orte)) σ ((M.weltVon u).lese Λ (p.orte ++ args.orte)) →
        eval σ p σ ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) hgσ ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ))
      (fun _ c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact expr_stabilX (hFS _) p hss.1 c hc
        · exact args_stabilX (hFS _) args hss.2 c hc)
      (fun _ => vertrag_stabilX_ind (hFS _) hTV g hg hp (hkand g hg))
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args
          (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) hgσ ρ])
      ρ (.dann rest k) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_dann_cons hok).2.2)
      (fun O' U A R σ κ e hgκ hκ h => by
        rw [semHA_dann_cons]
        simp only [execStmtHA, hκ, hev κ hgκ, h]
        exact weiterHA_logik S O' U A passes R _ e)
      (fun O' U A R σ κ hgκ hκ => by
        rw [semHA_dann_cons]
        simp only [execStmtHA, hκ, hev κ hgκ]
        cases R g κ (umsig hg (evalArgs κ args κ ρ)) with
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
    obtain ⟨hks, hss, _⟩ := okS_ende_cons (kopfSA_okS hF.1 hhead)
    simp only [stmtOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
    have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++
        (p.orte ++ args.orte)) σ ((M.weltVon u).lese Λ (p.orte ++ args.orte)) →
        eval σ p σ ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) hgσ ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ))
      (fun _ c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact expr_stabilX (hFS _) p hss.1 c hc
        · exact args_stabilX (hFS _) args hss.2 c hc)
      (fun _ => vertrag_stabilX_ind (hFS _) hTV g hg hp (hkand g hg))
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args
          (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) hgσ ρ])
      ρ (.ende rest) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_ende_cons hok).2.2)
      (fun O' U A R σ κ e hgκ hκ h => by
        rw [semHA_ende_cons]
        simp only [execStmtHA, hκ, hev κ hgκ, h]
        rfl)
      (fun O' U A R σ κ hgκ hκ => by
        rw [semHA_ende_cons]
        simp only [execStmtHA, hκ, hev κ hgκ]
        cases R g κ (umsig hg (evalArgs κ args κ ρ)) with
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
    obtain ⟨hks, hss, _⟩ := kopfSA_okS hF.1 hhead
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1
    have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++
        (p.orte ++ args.orte)) σ ((M.weltVon u).lese Λ (p.orte ++ args.orte)) →
        eval σ p σ ρ = ⟨g, hg⟩ := by
      intro σ hgσ
      rw [eval_gleichAuf p (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) hgσ ρ]
      exact hv
    obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
      (fun κ => umsig hg (evalArgs κ args κ ρ))
      (fun _ c hc => by
        rcases List.mem_append.mp hc with hc | hc
        · exact expr_stabilX (hFS _) p hss.1.1 c hc
        · exact args_stabilX (hFS _) args hss.1.2 c hc)
      (fun _ => vertrag_stabilX_ind (hFS _) hTV g hg hp (hkand g hg))
      (fun _ σ hgσ => by
        show umsig hg _ = umsig hg _
        rw [evalArgs_gleichAuf args
          (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) hgσ ρ])
      ρ (.wartet rest k) (fun L => held_nachSig_iff _ _ L)
      (fun hok => by
        obtain ⟨hks', hss', hk⟩ := hok
        simp only [Block.gOk, Bool.and_eq_true] at hks'
        simp only [blockOrteP, List.append_subset] at hss'
        exact ⟨hks'.2, hss'.2, hk⟩)
      (fun O' U A R σ κ e hgκ hκ h => by
        rw [semHA_dann]
        simp only [execBlockHA, hκ, hev κ hgκ, h]
        exact weiterHA_logik S O' U A passes R _ e)
      (fun O' U A R σ κ hgκ hκ => by
        rw [semHA_dann]
        simp only [execBlockHA, hκ, hev κ hgκ]
        cases R g κ (umsig hg (evalArgs κ args κ ρ)) with
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
    have hok := kopfSA_okS hF.1 hhead
    have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2)
      (ens_stabilX (hFS _) hTV hperm) (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popSA_begr_ok hE hF.1 hhead e
        (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U A σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_ende_cons (kopfSA_okS hF.1 hhead)
    have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
      (ens_stabilX (hFS _) hTV hperm)
      (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popSA_begr_ok hE hF.1 hhead e
        (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm rest σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U A σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_dann_cons (kopfSA_okS hF.1 hhead)
    have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
      (ens_stabilX (hFS _) hTV hperm)
      (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popSA_begr_ok hE hF.1 hhead e
        (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
      (fun R O' U A σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopfSA_okS hF.1 hhead
    have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2)
      (ens_stabilX (hFS _) hTV hperm) (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popSA_begr_ok hE hF.1 hhead e
        (fun O' R U A σ => semHA_rueck S O' U A passes R e hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U A σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_dann_cons (kopfSA_okS hF.1 hhead)
    have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
      (ens_stabilX (hFS _) hTV hperm)
      (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm restk kk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popSA_begr_ok hE hF.1 hhead e
        (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm restk kk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U A σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okS_ende_cons (kopfSA_okS hF.1 hhead)
    have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
      (ens_stabilX (hFS _) hTV hperm)
      (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm restk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hRS' := hRS
    rw [hpop] at hRS'
    refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
      (fun hE => popSA_begr_ok hE hF.1 hhead e
        (fun O' R U A σ => semHA_rueckCons S O' U A passes R e hperm restk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
      (fun hokc => by
        rcases hcaller with hc | ⟨n, err, hc⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.1, h'.2.1, h'.2.2⟩
        · have h' := rest_okS hc hokc
          exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
      (fun R O' U A σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
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
    refine ⟨⟨popSA_kopf hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popSA_begr_grund hE hF.1 hhead rg
        (fun O' R U A σ => semHA_rueckGrund S O' U A passes R rg hperm σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U A σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
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
    refine ⟨⟨popSA_kopf hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popSA_begr_grund hE hF.1 hhead rg
        (fun O' R U A σ => semHA_rueckConsGrund S O' U A passes R rg hperm restk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U A σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
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
    refine ⟨⟨popSA_kopf hWc (M.weltVon u) (fun σa => .grund σa rg) (Or.inr ⟨rg, fun _ => rfl⟩)
      (fun hE => popSA_begr_grund hE hF.1 hhead rg
        (fun O' R U A σ => semHA_dannRetGrund S O' U A passes R rg hperm restk kk σ ρ))
      (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
      (Env.cons (τ := .grund n) (Fin.cast hn rg) ρc)
      (.dann err.alsBlock.2 (.abbruch (.schrumpf k)))
      (fun L h => by rw [hcaller]; exact h)
      (fun hokc => okS_alsBlock err (.schrumpf k) restb.held_iff (rest_okS hcaller hokc).1
        (rest_okS hcaller hokc).2.1 (rest_okS hcaller hokc).2.2.2.2)
      (fun R O' U A σa X h => h l Γ Λ Λ' τ n err restb k ρc hcaller hn) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_grund hL⟩
  -- register reads and `awaits`
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenSA_lokalQ hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ HX hfx hkx hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP] at hss
    refine ⟨σ, HX, hfx, hkx, fun _ h => h, Nat.le_refl _, hg, ⟨hks.2, hss, hrest⟩,
      fun R O' U A _ _ hQ => ?_⟩
    have hrl : O'.regLies r σ = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_stabil (Λ := Λ) hks.1) hg
    exact ZErgG.folgt_of_eq
      (semHA_regLies S O' U A passes R r hk rest k σ ρ v
        (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) hz)
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) _ Λ zusage.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) zusage hss.1.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    obtain ⟨_, hrS⟩ := hss
    have hw' : wahr? (eval σ zusage σ (.cons v ρ)) = true := by
      rw [eval_gleichAuf zusage (fun _ h => List.mem_append_right _ h) hg]; exact hw
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hks.2.2, hrS, hrest⟩, fun R O' U A σ0 hQ hg0 hσ0 => ?_⟩
    have hrl : O'.regLies r σ0 = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_stabil (Λ := Λ) hks.1) hg0
    exact ZErgG.folgt_of_eq (by
      rw [semHA_regLiesElseWahr S O' U A passes R r hk zusage sonst rest k σ0 ρ v
        (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) (by rw [hσ0]; exact hw'),
        hσ0])
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu
      hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) _ Λ zusage.orte
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact expr_stabilX (hFS _) zusage hss.1.1)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    simp only [Block.gOk, Bool.and_eq_true] at hks
    simp only [blockOrteP, List.append_subset] at hss
    obtain ⟨⟨_, hsS⟩, _⟩ := hss
    have hw' : wahr? (eval σ zusage σ (.cons v ρ)) = false := by
      rw [eval_gleichAuf zusage (fun _ h => List.mem_append_right _ h) hg]; exact hw
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      okS_alsBlock sonst k rest.held_iff hks.2.1 hsS hrk, fun R O' U A σ0 hQ hg0 hσ0 => ?_⟩
    have hrl : O'.regLies r σ0 = O.regLies r (M.weltVon u) :=
      regLies_gleich hRL hQ r (regP_stabil (Λ := Λ) hks.1) hg0
    have h1 := semHA_regLiesElseFalsch S O' U A passes R r hk zusage sonst rest k σ0 ρ v
      (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) (by rw [hσ0]; exact hw')
    rw [hσ0] at h1
    exact h1
  | dannAwaits l Γ Λ Λ' g payload hp hLg rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    subst hs₁
    refine ⟨fadenSA_lese hF hhead _ (.dann rest (.schrumpf k)) _ Λ [.inr g]
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.cons_subset] at hss
        intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        exact stabil_of_fussX (hFS _) hss.1 fun L hB => bewacht_held (c := .inr g) hLg hB)
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [Block.gOk] at hks
    simp only [blockOrteP, List.cons_subset] at hss
    have hglob : σ.globs g = ((M.weltVon u).lese Λ [.inr g]).globs g :=
      hg.2 g (List.mem_append_right _ List.mem_cons_self)
    refine ⟨σ, Nat.le_refl _, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
      ⟨hks, hss.2, hrest⟩, fun R O' U A σ0 hQ _ hσ0 => ?_⟩
    have hsv : O'.sichtbar g (leseA A σ0 Λ [.inr g]) = true := by
      rw [hσ0, sichtbar_gleich hRL hQ g (List.mem_append_right _ List.mem_cons_self) hg,
        sichtbar_lese hRL.2]
      exact hvis
    have h1 := semHA_awaits S O' U A passes R g payload hp hLg rest k σ0 ρ hsv
    rw [hσ0, hglob] at h1
    exact ZErgG.folgt_of_eq h1

end Akteur

#print axioms Gabbro.Grammatik.akteurSA

end Gabbro.Grammatik
