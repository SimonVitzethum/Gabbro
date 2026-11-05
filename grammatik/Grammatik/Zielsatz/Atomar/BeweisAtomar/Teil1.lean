module

public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Speichermodell.Maschine.GXMaschine
public import Grammatik.Logik.Fortschritt.Hungerfrei
public import Grammatik.Bausteine.Arena.Ownership.Ruhe.Start
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



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
          simp only [↓reduceIte]

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

/-- **The same-core leg with the program's own handlers, on GA runs** (`kernHaltE_aus` of Opus
    agent H over GA: the argument reads the threads' own states only). -/
theorem kernHaltEA_aus [DecidableEq D.Fn] {P : Programm D} {O : Orakel D} {passes : Nat}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (hMask : MaskenDisziplin P fs) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D) :
    KernHaltEA P O passes (RufStartG P sp init) M := by
  intro kern ms fs' n hl hMn hKP g f L hHg hfg hkern hA
  have hH : ∀ t, HandlerVon P (RufStartG P sp init) t → P.unterbricht (init t).1 = true :=
    fun t ht => by unfold HandlerVon at ht; rw [rufStartG_kopf_f] at ht; exact ht
  exact kernHaltGA_gilt P O passes (RufStartG P sp init) M kern (HandlerVon P (RufStartG P sp init))
    (fun t => fun f => reachB P fs (init t).1 f = true)
    (fun t => fun _ => maskM fs (reachB P fs (init t).1))
    (fun t ht => merkAbg_maskM hvoll (hAbg _) (hMask _ (hH t ht)))
    (fun t ht => merkInvG_start sp init t
      (merkAbg_maskM hvoll (hAbg _) (hMask _ (hH t ht))) (reachB_wurzel P fs _))
    (fun t _ f' L' _ h => maskM_sperre f' L' h)
    (fun t L' => anSperre_start_falsch P sp init t L')
    ms fs' n hl hMn hKP g f L hHg hfg hkern hA

/-- Every G run is a GA run: `KernHaltEA` contains `KernHaltE`. -/
theorem kernHaltE_of_EA {P : Programm D} {O : Orakel D} {passes : Nat} {M0 M : RufMaschineG D}
    (h : KernHaltEA P O passes M0 M) : KernHaltE P O passes M0 M :=
  fun kern ms fs n hl hn hKP => h kern ms fs n ⟨hl.1, fun k hk => schrittGA_of_g (hl.2 k hk)⟩ hn hKP

/-! ## 2. Every leg, for any program meeting the premise groups with the rely -/

section Aus

variable [DecidableEq D.Fn]

/-- **Every leg of `ZielX` at every machine GX reaches**, from (a) `AkzeptiertSpecX`, (b) the
    user's logic with the rely, (c) the hardware assumptions and an admissible start. -/
theorem zielX_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {ls : List D.Lock} (hls : ∀ L : D.Lock, L ∈ ls) (ws : List D.Fn)
    {B : List (ArenaOwnership.Body.ArenaIface D)} {A : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpecX P S fs ws B A) (hN : LogikPflichtA P S Q (GeteiltA P ws))
    (O : Orakel D) (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
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
    sp init hH.1 hH.2.1 hH.2.2.1 hN.2.2.1 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) M hX
  have hInv := invarianten_atomar P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2.1 hN.2.2.1 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK hI hIG hZ.req hZ.sperren hex (fun t => (hW t).2) M hX
  have hZI := zielInvSA_erreichbarGX P O passes Q S (kVon P fs init) (GeteiltV P ws) (lokW P fs ws)
    sp init hH.1 hH.2.1 hH.2.2.1 hN.2.2.1 hS hvoll (fun t => hA.abg _)
    (fun t => reachB_wurzel P fs _) hTA hTV hTS hTO (fragX_ok hvoll hA.frag hA.fuss) hA.fuss
    hlokK hK (fun f => massPflicht_aus P passes Q S (GeteiltV P ws) Mass.leer f) hZ.req hZ.sperren hex M hX
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
      keinKernHalt := kernHaltEA_aus hvoll hA.abg hA.masken sp init M
      fortschritt := fortschrittG_GA hH.1 hA.stufen sp init (startSpur_nodup_leer init hLeer) hGA
        hV.2.2.1 (fun t => fadenSA_bereich hH.1 hH.2.1 hH.2.2.1 hS hZ.sperren hK hA.fuss t
          (hZI.1.1 t)) hA.antworten
      zeit := fun f g n _ _ _ hadm hE _ run hA' =>
        frame_schritte_beschraenktX f g n hadm hE run hA'
      folge := folgeG_erreichbarX hTA sp init hX
      speicherAdressen := fun hI lay hLay t k f hne =>
        geaendert_im_bereich (rufErreichbarGX_aussen
          (fun t ht => by obtain ⟨g, e, -⟩ := hTA _ ht; cases e) hI hX) hLay hne }

/-- A residue at a named stop is no `forever` loop with budget left. -/
theorem restHalt_nicht_ewigPos {O : Orakel D} {passes : Nat} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {σ : World D} {ρ : Env D Γ} {k : HaltArt} {r : GRest D V l Γ Λ}
    (h : RestHalt O passes σ ρ k r) : r.istEwigPos = false := by
  cases k <;> cases r <;> simp_all [RestHalt, GRest.istEwigPos] <;> rename_i n _ _ _ <;> cases n <;> simp_all [RestHalt]

/-- A residue at a spent budget is a `forever` loop. -/
theorem restHalt_budget_ewig {O : Orakel D} {passes : Nat} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {σ : World D} {ρ : Env D Γ} {r : GRest D V l Γ Λ}
    (h : RestHalt O passes σ ρ .budget r) : r.istEwig = true := by
  cases r <;> simp_all [RestHalt, GRest.istEwig, KopfHalt]
  all_goals (rename_i b _; cases b <;> simp_all [KopfHalt])

/-- A head with budget left is no head with another reading. -/
theorem kopf_ewigPos {r : RufRahmenG D} (hP : r.rest.2.2.2.2.istEwigPos = true) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {g : GRest D (vertragVon D r.f) l Γ Λ} (h : r.rest = ⟨l, Γ, Λ, ρ, g⟩)
    (hg : g.istEwigPos = false) : False := by
  have := (sigmaRest_lies (fun g => g.istEwigPos) h).symm.trans hP
  rw [hg] at this
  exact Bool.false_ne_true this

/-- **A stop on budget is no stop of the program**: on the machine one budget higher, the thread steps.
    The step comes from the progress leg at the higher budget: a `forever` loop with budget left is no
    finished thread, no lock wait and no named stop. -/
theorem budget_unecht {M : RufMaschineG D} {t : Faden} (hF : FortschrittG P O (passes + 1) (M.plus 1))
    (hB : HaltBenannt O passes M .budget t) : ∃ M', RufSchrittG P O (passes + 1) (M.plus 1) t M' := by
  obtain ⟨l, Γ, Λ, ρ, r, hr, hh⟩ := hB
  have hP : ((M.plus 1).faeden t).kopf.rest.2.2.2.2.istEwigPos = true :=
    (sigmaRest_lies (fun g => (g.plus 1).istEwigPos) hr).trans
      (GRest.plus_istEwigPos 0 r (restHalt_budget_ewig hh))
  have halt : ∀ k, ¬ HaltBenannt O (passes + 1) (M.plus 1) k t := by
    rintro k ⟨l', Γ', Λ', ρ', r', hr', hh'⟩
    exact kopf_ewigPos hP hr' (restHalt_nicht_ewigPos hh')
  rcases hF t with hf | hw | hh' | hh' | hh' | hh' | hs
  · exfalso
    have h1 := hf.2
    have hn : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
        g.istEwigPos = true → g.anRueck = false := by
      intro _ _ _ g hg; cases g <;> simp_all [GRest.istEwigPos, GRest.anRueck]
    exact Bool.false_ne_true ((hn _ hP).symm.trans h1)
  · exfalso
    obtain ⟨⟨L, l', Γ', Λ', Λ'', ρ', hr', body, rest, k, he⟩, _⟩ := hw
    exact kopf_ewigPos hP he rfl
  · exact absurd hh' (halt _)
  · exact absurd hh' (halt _)
  · exact absurd hh' (halt _)
  · exact absurd hh' (halt _)
  · exact hs

/-- **Every leg of `ZielFX` on every thread machine over GX.** -/
theorem zielFX_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {ls : List D.Lock} (hls : ∀ L : D.Lock, L ∈ ls) (ws : List D.Fn)
    {B : List (ArenaOwnership.Body.ArenaIface D)} {A : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpecX P S fs ws B A) (hN : LogikPflichtA P S Q (GeteiltA P ws))
    (O : Orakel D) (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs ws sp init)
    (hS : ∀ a ∈ B, ArenaOwnership.Machine.StartOwn a.A a.I sp init)
    (lebt0 : Faden → Bool) (K : FadenMaschine D)
    (hK : FadenErreichbarX P O passes (GeteiltV P ws) (FadenStart P sp init lebt0) K) :
    ZielFX P S O passes (GeteiltV P ws) (RufStartG P sp init) B K := by
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
      exact List.not_mem_nil hL
    budgetUnecht := fun t hB => by
      have hK1 := fadenInvX_erreichbar (fadenErreichbarX_budget 1 hK)
      exact budget_unecht (zielX_aus P S Q hvoll hls ws hA hN O hH (passes + 1) sp init hZ _
        hK1.lauf).fortschritt hB
    besitz := fun a ha => ArenaOwnership.Machine.ownInv_reachGX hH.1 (hA.besitz a ha) hvoll
      (ArenaOwnership.Ruhe.threadFacts_of (P := P) (S := S) (A := a.A)
        (fs := fs) (ws := ws) (B := B) (Ak := A) hA hZ (hA.worte a ha))
      (hS a ha) (hA.worte a ha)
      (fun c hc => hc.1.1) (fadenErreichbarX_GX hK) }

end Aus

/-! ## 3. The idle root: the admitted shared atomics of `P.mitRuhe` are those of `P` -/

section Ruhe

variable [DecidableEq D.Fn] (P : Programm D) {fs ws : List D.Fn}

omit [DecidableEq D.Fn] in
theorem vertragsFrei_mitRuhe_rueck {c : D.Tab ⊕ D.Glob} (h : VertragsFrei P.mitRuhe c) :
    VertragsFrei P c :=
  ⟨fun f => by
    obtain ⟨h1, h2, h3⟩ := h.1 (some f)
    rw [requires_mitRuhe_orte] at h1
    rw [ensures_mitRuhe_orte] at h2
    rw [invOrteP_mitRuhe] at h3
    exact ⟨h1, h2, h3⟩,
   fun i hi => by
    have h4 := h.2 i hi
    rw [invariante_mitRuhe_orte] at h4
    exact h4⟩

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
  obtain ⟨hA0, hBS, _⟩ := C.korrekt E fs ls cs hC
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
    (startZulaessig_aus E fs.1 hN.start hL) (ArenaOwnership.Ruhe.startOwn_arenen hL hBS) lebt0 K (heq ▸ hK)
  exact heq ▸ h

/-- **GABBRO_ZIEL_LEBEN, PROVED.** The reduction to `P.mitRuhe` as for `gabbro_ziel`; every machine of the run is
    reached, so the goal theorem's facts hold at each of them (progress, lock exclusivity, the rank invariant), and
    `hungerfrei` applies. -/
theorem gabbro_ziel_leben : GabbroZielLeben := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL R hR0 hFair n t L hSp
  have hA0 := (C.korrekt E fs ls cs hC).1
  have hA := akzeptiertSpecX_mitRuhe E.P fs.2 hA0
  have hN' : LogikPflichtA E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q)
      (GeteiltA E.P.mitRuhe (wsRuhe E.ws)) := by
    have h := logikPflichtA_mitRuhe hN.logik
    exact ⟨fun passes f => ⟨koerperGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc)
        (h.1 passes f).1,
      invGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.1,
      invGutGrundA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA0.abg hc) (h.1 passes f).2.2⟩,
      h.2⟩
  have hH' := hardware_mitRuhe hH
  have hZ := startZulaessig_aus E fs.1 hN.start hL
  have hLeer : ∀ t, D.mitRuhe.haelt (init t).1 = [] := fun t => by
    rcases hZ.wurzel t with h | h
    · exact (hA.wurzeln _ h).1
    · exact h.1
  have hND := startSpur_nodup_leer init hLeer
  have hr : ∀ n, RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) (R.M n) :=
    R.toPlanLauf.erreichbar (hR0 ▸ RufErreichbarG.start)
  exact hungerfrei R hH'.1
    (fun n t => ⟨_, rangInvG_erreichbar hH'.1 hA.stufen sp init hND (hr n) t⟩)
    (fun n => exklusivG hH'.1 sp init (startExklusiv_ohne_haelt init hLeer) (hr n))
    (fun n => (zielX_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2 (wsRuhe E.ws) hA hN'
      O.mitRuhe hH' passes sp init hZ (R.M n) (gx_aus_g_lauf (hr n))).fortschritt)
    hFair hSp

end Gabbro.Grammatik.Zielsatz
