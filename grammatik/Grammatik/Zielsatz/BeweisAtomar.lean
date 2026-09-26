/-
  File:      Grammatik/Zielsatz/BeweisAtomar.lean
  Subject:   THE GOAL WITH THE ATOMIC RELY, PROVED (Opus lane O25c, 2026-09-26, OFFEN O25).

  * `zielX_aus` -- every leg of `ZielX` at every machine GX reaches, from the four premise groups
    with the rely (generic in the declaration);
  * `zielFX_aus` -- every leg of `ZielFX` on every thread machine over GX (spawns and joins);
  * `geteiltV_mitRuhe_eq` -- the admitted shared atomics of `P.mitRuhe` are those of `P`;
  * `gabbro_zielX` -- the statement;
  * `geteiltV_leer` / `zielF_of_X` / `gabbroZiel_aus_X` -- THE EMBEDDING: on every unit the
    checker of before accepts there is no admitted shared atomic, GX is G there, and the
    statement of before follows word for word;
  * `akzeptiertSpec_verbindeX`, `gabbro_ziel_verbundX`, `verbund_aus_X` -- the same for linked
    units.
-/
import Grammatik.Zielsatz.AtomarZiel
import Grammatik.Speichermodell.GXMaschine
import Grammatik.Zielsatz.Verbund

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-! ## 1. Facts of the thread machine over GX -/

section Faden

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

theorem wartet_leer_of_haeltX {M0 : RufMaschineG D} {K : FadenMaschine D}
    (hI : FadenInvX P O passes Tg M0 K) {u : Faden} {L : D.Lock}
    (hL : L ∈ offen (K.m.faeden u).spur) : K.wartet u = [] := by
  refine Classical.byContradiction fun h => ?_
  rw [hI.joinFrei u h] at hL
  exact List.not_mem_nil hL

theorem lebt_of_haeltX {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {K : FadenMaschine D} (hI : FadenInvX P O passes Tg (RufStartG P sp init) K)
    (hLeer : ∀ t, D.haelt (init t).1 = []) {u : Faden} {L : D.Lock}
    (hL : L ∈ offen (K.m.faeden u).spur) : K.lebt u = true := by
  cases h : K.lebt u with
  | true => rfl
  | false =>
      rw [faden_schlafend_freiX hI u h (hLeer u)] at hL
      exact absurd hL List.not_mem_nil

/-- **NO DEADLOCK WITH JOIN WAITS, over GX** (the argument of `keine_verklemmungF`, with the rank
    invariant of GA runs). -/
theorem keine_verklemmungFX (hO : GutO O) (hSt : StufenM P) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hLeer : ∀ t, D.haelt (init t).1 = [])
    (ls : List D.Lock) (hls : ∀ L : D.Lock, L ∈ ls) {K : FadenMaschine D}
    (hI : FadenInvX P O passes Tg (RufStartG P sp init) K)
    (hW : ∀ t, K.lebt t = true → ¬ FertigG K.m t →
      (K.wartet t = [] ∧ WartetG K.m t) ∨ JoinWartet K t) :
    ∀ t, K.lebt t = true → FertigG K.m t := by
  have hR := gaInv_rang hO hSt sp init (startSpur_nodup_leer init hLeer) (gx_ga_lauf hTA hI.lauf)
  intro t0 ht0
  refine Classical.byContradiction fun hF0 => ?_
  by_cases hA : ∃ t, K.lebt t = true ∧ ¬ FertigG K.m t ∧ K.wartet t = []
  · obtain ⟨t1, hl1, hf1, hw1⟩ := hA
    let W := ls.filter fun L => @decide (∃ t, K.lebt t = true ∧ ¬ FertigG K.m t ∧
      K.wartet t = [] ∧ AnSperre K.m t L) (Classical.propDecidable _)
    have hWmem : ∀ L, L ∈ W ↔ ∃ t, K.lebt t = true ∧ ¬ FertigG K.m t ∧
        K.wartet t = [] ∧ AnSperre K.m t L := by
      intro L
      simp only [W, List.mem_filter, hls L, true_and]
      exact ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
        fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩
    have hwarte : ∀ t, K.lebt t = true → ¬ FertigG K.m t → K.wartet t = [] → WartetG K.m t := by
      intro t hl hf hw
      rcases hW t hl hf with ⟨_, h⟩ | ⟨u, hu, _⟩
      · exact h
      · rw [hw] at hu; exact absurd hu List.not_mem_nil
    obtain ⟨L1, hL1⟩ := (hwarte t1 hl1 hf1 hw1).1
    have hne : W ≠ [] := fun he => by
      have := (hWmem L1).mpr ⟨t1, hl1, hf1, hw1, hL1⟩
      rw [he] at this
      exact List.not_mem_nil this
    obtain ⟨Lm, hLm, hmax⟩ := rang_max W hne
    obtain ⟨tm, hlm, hfm, hwm, hAm⟩ := (hWmem Lm).mp hLm
    obtain ⟨u, _, hLu⟩ := (hwarte tm hlm hfm hwm).2 Lm hAm
    have hlu := lebt_of_haeltX hI hLeer hLu
    have hwu := wartet_leer_of_haeltX hI hLu
    by_cases hFu : FertigG K.m u
    · rw [fertig_leer (hR u) (hLeer u) hFu] at hLu
      exact List.not_mem_nil hLu
    · obtain ⟨Lu, hAu⟩ := (hwarte u hlu hFu hwu).1
      have hlt := (sperre_rang (hR u) hAu).2 Lm hLu
      have hle := hmax Lu ((hWmem Lu).mpr ⟨u, hlu, hFu, hwu, hAu⟩)
      omega
  · have hjoin : ∀ t, K.lebt t = true → ¬ FertigG K.m t →
        ∃ u, K.lebt u = true ∧ ¬ FertigG K.m u ∧ K.rang t < K.rang u := by
      intro t hl hf
      have hw : K.wartet t ≠ [] := fun hw => hA ⟨t, hl, hf, hw⟩
      rcases hW t hl hf with ⟨hw0, _⟩ | ⟨u, hu, hfu⟩
      · exact absurd hw0 hw
      · exact ⟨u, hI.kindLebt t u hu, hfu, hI.rangSteigt t u hu⟩
    have schranke : ∀ k t, K.lebt t = true → ¬ FertigG K.m t → K.uhr - K.rang t ≤ k → False := by
      intro k
      induction k with
      | zero =>
          intro t hl hf hk
          obtain ⟨u, _, _, hlt⟩ := hjoin t hl hf
          have := hI.rangUhr u
          omega
      | succ k ih =>
          intro t hl hf hk
          obtain ⟨u, hlu, hfu, hlt⟩ := hjoin t hl hf
          have := hI.rangUhr u
          exact ih u hlu hfu (by omega)
    exact schranke _ t0 ht0 hF0 (Nat.le_refl _)

/-- **PROGRESS ON THE THREAD MACHINE OVER GX**, from `FortschrittG` on the G state. -/
theorem fortschrittFX_aus {K : FadenMaschine D}
    (hF : FortschrittG P O passes K.m) : FortschrittFX P O passes Tg K := by
  intro t
  cases hl : K.lebt t with
  | false => exact Or.inl rfl
  | true =>
      right
      by_cases hw : K.wartet t = []
      · right
        refine ⟨hw, ?_⟩
        rcases hF t with h | h | h | h | h | h | ⟨M', hs⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨M', hs, FadenSchrittX.lauf K t M' hl hw (gx_aus_g hs)⟩)))))
      · left
        refine ⟨hw, ?_⟩
        by_cases hj : JoinWartet K t
        · exact Or.inl hj
        · refine Or.inr ⟨_, FadenSchrittX.join K t hl hw fun u hu =>
            Classical.byContradiction fun hfu => hj ⟨u, hu, hfu⟩, rfl, ?_⟩
          show (if t = t then [] else K.wartet t) = []
          simp

end Faden

/-- **The order leg (Opus agent G) at every machine GX reaches**: the order invariant reads the
    threads' own states only, which a GX step moves as its inner G step does. -/
theorem folgeG_erreichbarX {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} (hTA : ∀ c, Tg c → AtomarAusgenommen c) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (hX : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) : FolgeG P M := by
  intro Φ hΦ t
  have hI : ∀ t, FolgeInvG Φ (M.faeden t) :=
    gaInv (I := fun M => ∀ t, FolgeInvG Φ (M.faeden t)) (fun M M' e h t => by rw [← e]; exact h t)
      (folgeInvG_start Φ hΦ sp init) (fun M M' u h hs t => by
        by_cases htu : t = u
        · subst htu
          exact folgeInvG_schritt Φ hΦ hs (h t)
        · rw [rufSchrittG_fremd hs t htu]
          exact h t) (gx_ga_lauf hTA hX)
  exact ⟨(hI t).2.2, fun _ ha he => fR_anRueck Φ _ _ _ ha (hI t).1 he⟩

/-! ## 2. Every leg, for any program meeting the premise groups with the rely -/

section Aus

variable [DecidableEq D.Fn]

/-- **Every leg of `ZielX` at every machine GX reaches**, from (a) `AkzeptiertSpecX`, (b) the
    user's logic with the rely, (c) the hardware assumptions and an admissible start. -/
theorem zielX_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {ls : List D.Lock} (hls : ∀ L : D.Lock, L ∈ ls) (ws : List D.Fn)
    (hA : AkzeptiertSpecX P S fs ws) (hN : LogikPflichtA P S Q (GeteiltA P ws)) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init)
    (M : RufMaschineG D)
    (hX : RufErreichbarGX P O passes (GeteiltV P ws) (RufStartG P sp init) M) :
    ZielX P S O passes (GeteiltV P ws) (RufStartG P sp init) M := by
  have hW : ∀ t, D.haelt (init t).1 = [] ∧ D.gruende (init t).1 = 0 := fun t => by
    rcases hZ.wurzel t with h | h
    · exact hA.wurzeln _ h
    · exact ⟨h.1, h.2.1⟩
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => (hW t).1
  have hS : SperrInvOk S := ⟨hA.sperrOrte, hN.2.1⟩
  have hT : ∀ c, GeteiltV P ws c → GeteiltA P ws c := fun c h => h.1
  have hTA : ∀ c, GeteiltV P ws c → AtomarAusgenommen c := fun c h => h.1.1
  have hTV : ∀ c, GeteiltV P ws c → VertragsFrei P c := fun c h => h.2
  have hTS : ∀ c, GeteiltV P ws c → ∀ f Λ, c ∉ stabilS P S (lokW P fs ws) f Λ :=
    fun c h f Λ => geteiltV_nicht_stabil hvoll hA h f Λ
  have hTO : ∀ c, GeteiltV P ws c → ∀ L, c ∉ S.orte L :=
    fun c h L hL => h.1.2.1 L (hA.sperrOrte L c hL)
  have hlokK : ∀ c, lokW P fs ws c = true → GetrenntK P (kVon P fs init) c := fun c hc =>
    getrenntK_of hZ (by
      unfold lokW at hc
      exact @of_decide_eq_true _ (Classical.propDecidable _) hc)
  have hK := fun f => koerperGutSA_mono hT ((hN.1 passes f).1)
  have hI := fun f => invGutSA_mono hT ((hN.1 passes f).2.1)
  have hIG := fun f => invGutGrundA_mono hT ((hN.1 passes f).2.2)
  have hex := startExklusiv_ohne_haelt init hLeer
  have hGA := gx_ga_lauf hTA hX
  have hV := ziel_ort_atomar_voll P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) M hX
  have hInv := invarianten_atomar P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) M hX
  have hZI := zielInvSA_erreichbarGX P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2 hN.2.2 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hZ.req hZ.sperren hex M hX
  exact
    { speicherSicher := gaInv_spur hH.1 sp init hGA
      rennfrei := fun ms fs' n hl _ i j c hij hjn hfg hzi hzj hw hAt =>
        rennfreiGA hH.1 hvoll sp init hex (kVon P fs init) (fun t => hA.abg _)
          (fun t => reachB_wurzel P fs _)
          (fun c hB hAt => schreibGetrenntK_of hZ hA.einzeln hB hAt (hA.renn c hB hAt))
          ms fs' n hl i j c hij hjn hfg hzi hzj hw hAt
      schwach := fun ord W W' u σ M'' wahl neu hr hWg h => by
        have h' := schwach_ist_gX (S := S) hH.1 hvoll (fun t => hA.abg _)
          (fun t => reachB_wurzel P fs _) hA.fuss hlokK hTA hex hr h
        rw [hWg] at h'
        exact h'
      vertrag := hV.1
      sperrInv := hV.2.1
      invRueck := hV.2.2.2.1
      invGrund := hV.2.2.2.2.1
      invRuhe := hInv.1
      invSicht := hInv.2.1
      sperrWechsel := hInv.2.2.1
      sperrSicht := hInv.2.2.2
      startEnde := hV.2.2.2.2.2.1
      keinStartGrund := hV.2.2.2.2.2.2
      keinLogikHalt := hV.2.2.1
      keineVerklemmung := keine_verklemmungGA hH.1 hA.stufen sp init hLeer ls hls hGA
      keinZyklus := kein_warteZyklusGA hH.1 hA.stufen sp init hLeer hGA
      keinKernHalt := kernHaltGA_gilt P O passes _ _
      fortschritt := fortschrittG_GA hH.1 hA.stufen sp init (startSpur_nodup_leer init hLeer) hGA
        hV.2.2.1 (fun t => fadenSA_bereich hH.1 hH.2.1 hH.2.2 hS hZ.sperren hK hA.fuss t
          (hZI.1.1 t)) hA.antworten
      zeit := fun f g n _ _ _ hadm hE _ run hA' =>
        frame_schritte_beschraenktX f g n hadm hE run hA'
      folge := folgeG_erreichbarX hTA sp init hX }

/-- **Every leg of `ZielFX` on every thread machine over GX.** -/
theorem zielFX_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {ls : List D.Lock} (hls : ∀ L : D.Lock, L ∈ ls) (ws : List D.Fn)
    (hA : AkzeptiertSpecX P S fs ws) (hN : LogikPflichtA P S Q (GeteiltA P ws)) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init)
    (lebt0 : Faden → Bool) (K : FadenMaschine D)
    (hK : FadenErreichbarX P O passes (GeteiltV P ws) (FadenStart P sp init lebt0) K) :
    ZielFX P S O passes (GeteiltV P ws) (RufStartG P sp init) K := by
  have hLeer : ∀ t, D.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hA.wurzeln _ h).1
    · exact h.1
  have hI := fadenInvX_erreichbar hK
  have hG := zielX_aus P S Q hvoll hls ws hA hN O hH passes sp init hZ K.m hI.lauf
  exact {
    g := hG
    schlafendUnberuehrt := hI.schlaeft
    schlafendFrei := fun t ht L hL => by
      rw [faden_schlafend_freiX hI t ht (hLeer t)] at hL
      exact List.not_mem_nil hL
    joinFrei := fun t ht L hL => by
      rw [hI.joinFrei t ht] at hL
      exact List.not_mem_nil hL
    keineVerklemmung := keine_verklemmungFX hH.1 hA.stufen (fun c h => h.1.1) sp init hLeer ls
      hls hI
    keinZyklus := by
      have h := kein_warteZyklusF hI.ohneLauf hG.keinZyklus
      exact h
    fortschritt := fortschrittFX_aus hG.fortschritt
    spawnSicht := fun K' t hs h0 h1 => by
      rw [fadenX_spawn_m hs h0 h1]
      refine ⟨rfl, fun L hL => ?_, hG.sperrInv, hG.invRuhe⟩
      rw [faden_schlafend_freiX hI t h0 (hLeer t)] at hL
      exact List.not_mem_nil hL }

end Aus

/-! ## 3. The idle root: the admitted shared atomics of `P.mitRuhe` are those of `P` -/

section Ruhe

variable [DecidableEq D.Fn] (P : Programm D) {fs ws : List D.Fn}

omit [DecidableEq D.Fn] in
theorem vertragsFrei_mitRuhe_rueck {c : D.Tab ⊕ D.Glob} (h : VertragsFrei P.mitRuhe c) :
    VertragsFrei P c := fun f => by
  obtain ⟨h1, h2, h3⟩ := h (some f)
  rw [requires_mitRuhe_orte] at h1
  rw [ensures_mitRuhe_orte] at h2
  rw [invOrteP_mitRuhe] at h3
  exact ⟨h1, h2, h3⟩

theorem geteiltV_mitRuhe_eq (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w)) :
    GeteiltV P.mitRuhe (wsRuhe ws) = GeteiltV P ws := by
  funext c
  apply propext
  constructor
  · rintro ⟨hA, hV⟩
    exact ⟨geteiltA_mitRuhe_rueck P hvoll hAbg hA, vertragsFrei_mitRuhe_rueck P hV⟩
  · rintro ⟨⟨⟨g, e, ha⟩, hB, hR⟩, hV⟩
    refine ⟨⟨⟨g, e, ha⟩, fun L hL => hB L ((bewacht_mitRuhe (D := D) c L).mp hL), fun hR' => hR ?_⟩,
      vertragsFrei_mitRuhe P hV⟩
    exact (getrenntR_iff hvoll hAbg c).mpr (getrennt_mitRuhe_rueck P hvoll hAbg
      ((getrenntR_iff (fsRuhe_voll hvoll) (abg_mitRuhe P hvoll hAbg) c).mp hR'))

end Ruhe

/-! ## 4. The statement -/

/-- **GABBRO_ZIEL WITH THE ATOMIC RELY, PROVED.** -/
theorem gabbro_ziel : GabbroZiel := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL lebt0 K hK
  have hA0 := C.korrekt E fs ls cs hC
  have hA := akzeptiertSpecX_mitRuhe E.P fs.2 hA0
  have heq := geteiltV_mitRuhe_eq E.P (ws := E.ws) fs.2 hA0.abg
  have hN' : LogikPflichtA E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q)
      (GeteiltA E.P.mitRuhe (wsRuhe E.ws)) := by
    have h := logikPflichtA_mitRuhe hN.logik
    exact ⟨fun passes f => ⟨koerperGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc)
        (h.1 passes f).1,
      invGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.1,
      invGutGrundA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.2⟩,
      h.2⟩
  have h := zielFX_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2
    (wsRuhe E.ws) hA hN' O.mitRuhe (hardware_mitRuhe hH) passes sp init
    (startZulaessig_aus E fs.1 hN.start hL) lebt0 K (heq ▸ hK)
  exact heq ▸ h

/-- **The goal on every run of machine GX** (every thread live, nothing spawned): the reading
    of `GabbroZiel` over plain GX runs, as `gabbro_ziel_g` is the reading of the statement of
    before over G runs. -/
theorem gabbro_ziel_gx (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (M : RufMaschineG D.mitRuhe)
    (hr : RufErreichbarGX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) M) :
    ZielX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) M :=
  (gabbro_ziel C D E fs ls cs hC hN O hH passes sp init hL (fun _ => true)
    (FadenMaschine.alleLebend M) (fadenErreichbarX_von_GX hr)).g

/-- **On a declaration without an `atomic` global, (b) with the rely is (b)**: no read of a
    shared atomic exists. -/
theorem nutzerPflichtA_ohne_atomar {D : Deklaration} [DecidableEq D.Fn] {E : Einheit D}
    (hat : ∀ g : D.Glob, D.atomar g = false) (h : NutzerPflicht E) : NutzerPflichtA E :=
  ⟨logikPflichtA_of_frei (fun f c _ hc => by
      obtain ⟨g, _, hg⟩ := hc.1
      rw [hat g] at hg
      cases hg) h.logik, h.start⟩

/-! ## 5. The embedding: the statement of before follows -/

section Einbettung

variable {P : Programm D} {S : SperrInv D} {O : Orakel D} {passes : Nat}
  {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **With no shared atomic, `ZielX` is `Ziel`.** -/
theorem ziel_of_X (hT : ∀ c, ¬ Tg c) {M0 M : RufMaschineG D}
    (h : ZielX P S O passes Tg M0 M) : Ziel P S O passes M0 M where
  speicherSicher := h.speicherSicher
  rennfrei := rennfreiBis_of_GA h.rennfrei
  schwach := fun ord W W' u hr hWg hs => by
    obtain ⟨σ, M'', wahl, neu, hs'⟩ := hs
    exact gx_leer_g hT (h.schwach ord W W' u σ M'' wahl neu hr hWg hs').1
  vertrag := h.vertrag
  sperrInv := h.sperrInv
  invRueck := h.invRueck
  invGrund := h.invGrund
  invRuhe := h.invRuhe
  invSicht := h.invSicht
  sperrWechsel := fun u M' L hs => h.sperrWechsel u M' L (gx_aus_g hs)
  sperrSicht := fun u M' hs => h.sperrSicht u M' (gx_aus_g hs)
  startEnde := h.startEnde
  keinStartGrund := h.keinStartGrund
  keinLogikHalt := h.keinLogikHalt
  keineVerklemmung := h.keineVerklemmung
  keinZyklus := h.keinZyklus
  keinKernHalt := kernHaltG_of_GA h.keinKernHalt
  fortschritt := h.fortschritt
  zeit := fun f g n rho s0 k hadm hE M2 run hA => by
    have h1 := h.zeit f g n rho s0 k hadm hE M2 (SegLauf.alsX (Tg := Tg) run)
      (aktivVor_alsX f k run hA)
    rw [segZaehle_alsX] at h1
    exact h1
  folge := h.folge

/-- **With no shared atomic, `ZielFX` is `ZielF`.** -/
theorem zielF_of_X (hT : ∀ c, ¬ Tg c) {M0 : RufMaschineG D} {K : FadenMaschine D}
    (h : ZielFX P S O passes Tg M0 K) : ZielF P S O passes M0 K where
  g := ziel_of_X hT h.g
  schlafendUnberuehrt := h.schlafendUnberuehrt
  schlafendFrei := h.schlafendFrei
  joinFrei := h.joinFrei
  keineVerklemmung := h.keineVerklemmung
  keinZyklus := h.keinZyklus
  fortschritt := fortschrittF_aus h.g.fortschritt
  spawnSicht := fun K' t hs => h.spawnSicht K' t (fadenSchrittX_of hs)

variable [DecidableEq D.Fn]

/-- **A unit the checker of before accepts has no shared atomic at all**: every footprint
    carrier is signature-guarded, lock-protected or thread-local (`FussS`), so no carrier is read
    by one start while another writes it without a guard. -/
theorem geteiltA_leer {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA : AkzeptiertSpec P S fs ws) (c : D.Tab ⊕ D.Glob) : ¬ GeteiltA P ws c := by
  rintro ⟨_, hB, hR⟩
  apply hR
  intro w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
  have lokal : (sigB f c || lokW P fs ws c) = true → TraegerSchreibt g c = false := by
    intro h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨L, hL, _⟩ := sigB_ok h
      exact absurd hL (hB L)
    · have hG : Getrennt P fs ws c := @of_decide_eq_true _ (Classical.propDecidable _) h
      exact (getrenntR_iff hvoll hA.abg c).mpr hG w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
  rcases List.mem_append.mp hcf with hc | hc
  · rcases (hA.fuss f).1 c hc with h | ⟨L, hL, _⟩
    · exact lokal h
    · exact absurd hL (hB L)
  · exact lokal ((hA.fuss f).2 c hc)

theorem geteiltV_leer {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA : AkzeptiertSpec P S fs ws) (c : D.Tab ⊕ D.Glob) : ¬ GeteiltV P ws c :=
  fun h => geteiltA_leer hvoll hA c h.1

end Einbettung

/-- **THE STATEMENT OF BEFORE, DERIVED.** Every checker of before is a checker for the rely
    (`Pruefer.alsX`), on every unit it accepts (b) and (b) with the rely coincide
    (`nutzerPflichtA_of_akzeptiert`), every thread-machine run over G is one over GX
    (`fadenErreichbarX_of`), and such a unit has no admitted shared atomic (`geteiltV_leer`), so
    `ZielFX` there is `ZielF` (`zielF_of_X`). -/
theorem gabbro_ziel_sc_aus (h : GabbroZiel) : GabbroZielSC := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL lebt0 K hK
  have hA0 := C.korrekt E fs ls cs hC
  have hZ := h C.alsX D E fs ls cs hC (nutzerPflichtA_of_akzeptiert fs.2 hA0 hN) O hH passes sp
    init hL lebt0 K (fadenErreichbarX_of hK)
  refine zielF_of_X ?_ hZ
  exact fun c => geteiltV_leer fs.2 hA0 c

/-! ## 6. Linked units -/

section Verbund

variable [DecidableEq D.Fn] {E₁ E₂ : Einheit D} {e : D.Fn → Bool}

/-- **The linked unit is accepted by the checker of before**, from two units each accepted WITH
    the rely: the link check's `lok` makes every carrier a function relies on without a lock
    thread-local over the composed hulls -- shared atomics included -- so the linked footprints
    need no rely. The per-body components are each unit's own. -/
theorem akzeptiertSpec_verbindeX {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hA₁ : AkzeptiertSpecX E₁.P E₁.S fs E₁.ws) (hA₂ : AkzeptiertSpecX E₂.P E₂.S fs E₂.ws)
    (hV : Verbindbar E₁ E₂) (hS : SchnittstelleSpec fs e E₁ E₂) :
    AkzeptiertSpec (verbinde e E₁ E₂).P (verbinde e E₁ E₂).S fs (verbinde e E₁ E₂).ws := by
  have hH := huelle_of_reach (e := e) (E₁ := E₁) (E₂ := E₂) hvoll hS.keinRueckruf
  have hfrag : ∀ f, ((teilP e E₁ E₂ f).rumpf f).gOk
      (kandB (teilP e E₁ E₂ f) fs (fussOrteG (teilP e E₁ E₂ f) f)) (fun _ => true) = true := by
    intro f
    unfold teilP
    cases e f
    · exact List.all_eq_true.mp hA₂.frag f (hvoll f)
    · exact List.all_eq_true.mp hA₁.frag f (hvoll f)
  have hGetrennt : ∀ c, LokBedarf e E₁ E₂ c →
      Getrennt (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c := by
    intro c hc w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
    refine hS.lok c hc w₁ hw₁ w₂ hw₂ hne f g (hH w₁ f hf) ?_ (hH w₂ g hg)
    rw [← fussOrteG_teil hV]
    exact hcf
  refine ⟨?_, abg_verbinde hvoll hA₁.abg hA₂.abg hS.blatt₁ hS.blatt₂, ?_, ?_, hA₁.sperrOrte,
    ?_, ?_, ?_, ?_⟩
  · refine List.all_eq_true.mpr fun f _ => ?_
    show ((verbindeP e E₁ E₂).rumpf f).gOk
      (kandB (verbindeP e E₁ E₂) fs (fussOrteG (verbindeP e E₁ E₂) f)) (fun _ => true) = true
    rw [verbindeP_rumpf, kandB_teil hV fs f, fussOrteG_teil hV]
    exact hfrag f
  · intro f
    have hlok : ∀ c, LokBedarf e E₁ E₂ c → lokW (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c = true :=
      fun c hc => @decide_eq_true _ (Classical.propDecidable _) (hGetrennt c hc)
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have hc' : c ∈ fussOrte (teilP e E₁ E₂ f) f := by
        rw [← fussOrte_teil hV]
        exact hc
      by_cases hs : sigB f c = true
      · exact Or.inl (by rw [hs, Bool.true_or])
      · by_cases hg : ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L
        · exact Or.inr hg
        · refine Or.inl ?_
          rw [hlok c ⟨f, Or.inl ⟨hc', by simpa using hs, hg⟩⟩, Bool.or_true]
    · have hc' : c ∈ ((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger := by
        rw [← verbindeP_rumpf]
        exact hc
      by_cases hs : sigB f c = true
      · rw [hs, Bool.true_or]
      · rw [hlok c ⟨f, Or.inr ⟨hc', by simpa using hs⟩⟩, Bool.or_true]
  · intro f
    show Grammatik.mE (bodenM f) ((verbindeP e E₁ E₂).rumpf f) = true
    rw [verbindeP_rumpf]
    unfold teilP
    cases e f
    · exact hA₂.stufen f
    · exact hA₁.stufen f
  · intro w hw
    rcases mem_ws_verbinde hw with h | h
    · exact hA₁.wurzeln w h
    · exact hA₂.wurzeln w h
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := hS.einzeln w hw
    exact ⟨h1, h2, fun f hf c hc => h3 f (hH w f hf) c hc⟩
  · intro c hB hAt w₁ hw₁ w₂ hw₂ hne g hg hgc h hh
    have := hS.renn c hB hAt w₁ hw₁ w₂ hw₂ hne g (hH w₁ g hg) hgc h (hH w₂ h hh)
    have e' : fussOrteG (verbinde e E₁ E₂).P h = fussOrteG (teilP e E₁ E₂ h) h := fussOrteG_teil hV h
    rw [e']
    exact this
  · intro f x hx
    change x ∈ ((verbindeP e E₁ E₂).rumpf f).ants at hx
    rw [verbindeP_rumpf] at hx
    unfold teilP at hx
    cases hf : e f
    · rw [hf] at hx
      exact hA₂.antworten f x hx
    · rw [hf] at hx
      exact hA₁.antworten f x hx

/-- The rely duty of a unit implies its duty of before. -/
theorem nutzerTeil_of_A {eigen : D.Fn → Bool} {E : Einheit D} (h : NutzerTeilA eigen E) :
    NutzerTeil eigen E :=
  ⟨⟨fun pa f hf => ⟨koerperGutS_of_A (h.logik.1 pa f hf).1, invGutS_of_A (h.logik.1 pa f hf).2.1,
    invGutGrund_of_A (h.logik.1 pa f hf).2.2⟩, h.logik.2.1, h.logik.2.2⟩, h.start⟩

/-- On a unit the checker of before accepts, its duty of before is its rely duty. -/
theorem nutzerTeilA_of {eigen : D.Fn → Bool} {E : Einheit D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec E.P E.S fs E.ws) (h : NutzerTeil eigen E) :
    NutzerTeilA eigen E :=
  ⟨⟨fun pa f hf => ⟨koerperGutSA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA f)
      (h.logik.1 pa f hf).1,
    invGutSA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA f) (h.logik.1 pa f hf).2.1,
    invGutGrundA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA f) (h.logik.1 pa f hf).2.2⟩,
    h.logik.2.1, h.logik.2.2⟩, h.start⟩

end Verbund

/-- **LINKING WITH THE ATOMIC RELY, PROVED.** -/
theorem gabbro_ziel_verbund : GabbroZielVerbund := by
  intro C D _ E₁ E₂ e fs ls cs h₁ h₂ hV hS hN₁ hN₂ hQ O hH passes sp init hL lebt0 K hK
  have hA := akzeptiertSpec_verbindeX fs.2 (C.korrekt E₁ fs ls cs h₁) (C.korrekt E₂ fs ls cs h₂)
    hV hS
  have hB : akzeptiertX_pruefer.akzeptiert (verbinde e E₁ E₂) fs.1 ls.1 cs.1 = true :=
    akzeptiertX_of_akzeptiert ((akzeptiert_iff fs.2 ls.2 cs.2).mpr hA)
  exact gabbro_ziel akzeptiertX_pruefer D (verbinde e E₁ E₂) fs ls cs hB
    (nutzerPflichtA_of_akzeptiert fs.2 hA
      (nutzerPflicht_verbinde hV hQ (nutzerTeil_of_A hN₁) (nutzerTeil_of_A hN₂)))
    O hH passes sp init hL lebt0 K hK

/-- **THE LINKED STATEMENT OF BEFORE, DERIVED.** -/
theorem gabbro_ziel_verbund_sc_aus (h : GabbroZielVerbund) : GabbroZielVerbundSC := by
  intro C D _ E₁ E₂ e fs ls cs h₁ h₂ hV hS hN₁ hN₂ hQ O hH passes sp init hL lebt0 K hK
  have hA₁ := C.korrekt E₁ fs ls cs h₁
  have hA₂ := C.korrekt E₂ fs ls cs h₂
  have hZ := h C.alsX D E₁ E₂ e fs ls cs h₁ h₂ hV hS (nutzerTeilA_of fs.2 hA₁ hN₁)
    (nutzerTeilA_of fs.2 hA₂ hN₂) hQ O hH passes sp init hL lebt0 K (fadenErreichbarX_of hK)
  refine zielF_of_X ?_ hZ
  exact fun c => geteiltV_leer fs.2 (akzeptiertSpec_verbinde fs.2 hA₁ hA₂ hV hS) c

#print axioms Gabbro.Grammatik.Zielsatz.zielX_aus
#print axioms Gabbro.Grammatik.Zielsatz.zielFX_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_gx
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund_sc_aus

end Gabbro.Grammatik.Zielsatz
