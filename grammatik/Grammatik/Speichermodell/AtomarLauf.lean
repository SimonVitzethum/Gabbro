/-
  File:      Grammatik/Speichermodell/AtomarLauf.lean
  Subject:   THE REPLAY WITH THE ATOMIC RELY, part 4: the replay invariant on every run of the
             machine whose SHARED atomics the weak memory answers (machine GX), and the contract
             legs there. Opus lane O25b, 2026-09-26, OFFEN O25. Standalone.

  MACHINE GX (`RufSchrittGX`): a step of G on a PRESENTED memory that agrees with G's at every
  carrier outside the shared atomics `Tg`, the successor taking the written carriers from the
  step and keeping the rest -- machine GA of Atomar.lean with `Tg` in place of "atomic". For
  `Tg` inside the atomics every GX step is a GA step (`gx_ga`), so every thread invariant of GA
  holds on GX. What GX adds over GA is exactly what W gives on a checked program: a THREAD-LOCAL
  atomic is read at its newest message (`SichtInvX`, AtomarW.lean), so only the shared ones are
  free.

  THE INVARIANT ON EVERY GX RUN (`zielInvSA_erreichbarGX`): the replay `ZielInvSA` with the
  record of atomic reads, the frame invariant `RahmenInvS` and the machine lock invariant
  `SperrInvG`. A step of thread `u` is taken apart into (1) the presented memory -- a change at
  shared atomics only, which no stable carrier, no protected carrier and no suspended frame's
  record sees; (2) a G step from there -- `akteurSA` for `u`, the rely for every other thread;
  (3) the successor's memory -- again a change at shared atomics only.
-/
import Grammatik.Speichermodell.AtomarAkteur
import Grammatik.Speichermodell.Atomar

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The machine -/

/-- **One step of GX**: G on a memory that agrees with G's outside the shared atomics `Tg`; the
    written carriers from the step, the rest kept. -/
def RufSchrittGX (P : Programm D) (O : Orakel D) (passes : Nat) (Tg : D.Tab ⊕ D.Glob → Prop)
    (M : RufMaschineG D) (u : Faden) (M' : RufMaschineG D) : Prop :=
  ∃ (σ : Speicher D) (M'' : RufMaschineG D),
    RufSchrittG P O passes (mitSpeicher M σ) u M'' ∧
    (∀ c, ¬ Tg c → TraegerGleich σ M.speicher c) ∧
    (∀ c, SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M''.speicher c) ∧
    (∀ c, ¬ SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M.speicher c) ∧
    M'.faeden = M''.faeden ∧ M'.lauf = M''.lauf ∧ M'.start = M''.start

/-- The machines GX reaches from `M0`. -/
inductive RufErreichbarGX (P : Programm D) (O : Orakel D) (passes : Nat)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) : RufMaschineG D → Prop where
  | start : RufErreichbarGX P O passes Tg M0 M0
  | schritt (M M' : RufMaschineG D) (u : Faden) :
      RufErreichbarGX P O passes Tg M0 M → RufSchrittGX P O passes Tg M u M' →
        RufErreichbarGX P O passes Tg M0 M'

section GX

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **With the shared atomics inside the atomics, every GX step is a GA step.** -/
theorem gx_ga (hTA : ∀ c, Tg c → AtomarAusgenommen c) {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGX P O passes Tg M u M') : RufSchrittGA P O passes M u M' := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨σ, M'', hs, fun c hc => hσ c fun ht => hc (hTA c ht), h1, h2, h3, h4, h5⟩

theorem gx_ga_lauf (hTA : ∀ c, Tg c → AtomarAusgenommen c) {M0 M : RufMaschineG D}
    (h : RufErreichbarGX P O passes Tg M0 M) : RufErreichbarGA P O passes M0 M := by
  induction h with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ _ ih (gx_ga hTA hs)

/-- **Every G step is a GX step** (present G's own memory). -/
theorem gx_aus_g {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O passes M u M') :
    RufSchrittGX P O passes Tg M u M' := by
  refine ⟨M.speicher, M', by rw [mitSpeicher_selbst]; exact hs, fun c _ => traegerGleich_refl _ c,
    fun c _ => traegerGleich_refl _ c, fun c hw => ?_, rfl, rfl, rfl⟩
  have h := traegerGleich_of_nicht_schreib hw
  rw [mitSpeicher_selbst] at h
  exact h

theorem gx_aus_g_lauf {M0 M : RufMaschineG D} (h : RufErreichbarG P O passes M0 M) :
    RufErreichbarGX P O passes Tg M0 M := by
  induction h with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ _ ih (gx_aus_g hs)

/-- **The successor agrees with the G step's result outside the shared atomics.** -/
theorem gx_aussen {M M' M'' : RufMaschineG D} {σ : Speicher D} {u : Faden}
    (hσ : ∀ c, ¬ Tg c → TraegerGleich σ M.speicher c)
    (h1 : ∀ c, SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M''.speicher c)
    (h2 : ∀ c, ¬ SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M.speicher c)
    (c : D.Tab ⊕ D.Glob) (hc : ¬ Tg c) : TraegerGleich M'.speicher M''.speicher c := by
  by_cases hw : SchreibG (mitSpeicher M σ) M'' u c
  · exact h1 c hw
  · refine traegerGleich_trans (h2 c hw) ?_
    refine traegerGleich_symm (traegerGleich_trans (traegerGleich_of_nicht_schreib hw) ?_)
    exact hσ c hc

end GX

/-! ## 2. The rely over GX -/

section Rely

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

/-- **Another thread's G step leaves the stable carriers of every frame of `t` alone**, from the
    thread invariants alone (as `stabilS_rely` with `lokOk_mehr`, without reachability). -/
theorem stabilS_relyX (hO : GutO O) (hS : SperrInvOk S) {K : Faden → D.Fn → Bool}
    {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O passes M u M')
    (hH : ∀ t, HaeltInvG (M.faeden t)) (hex : Exklusiv M)
    (hMk : ∀ t, ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, K t F.f = true)
    (t : Faden) (htu : t ≠ u) (F : RufRahmenG D) (hF : F ∈ (M.faeden t).kopf :: (M.faeden t).stapel)
    (c : D.Tab ⊕ D.Glob) (hc : c ∈ stabilS P S (lokK P K) F.f F.rest.2.2.1) :
    TraegerGleich M'.speicher M.speicher c := by
  rcases stabilS_mem.mp hc with hc | ⟨L, hL, hcL⟩
  · have hsf := (sicher_mem.mp hc).2
    simp only [Bool.or_eq_true] at hsf
    rcases hsf with hsig | hfrei
    · obtain ⟨L, hB, hLh⟩ := sigB_ok hsig
      have hLt := (hH t).signatur F hF L hLh
      exact schritt_traeger hO hs c (Or.inl ⟨L, hB, hex t u htu L hLt⟩)
    · exact schritt_traeger hO hs c (Or.inr (lokK_ok hfrei t u htu F.f (hMk t F hF)
        (sicher_mem.mp hc).1 _ (hMk u _ List.mem_cons_self)))
  · have hLt := (hH t).alle F hF L hL
    exact schritt_traeger hO hs c (Or.inl ⟨L, hS.1 L c hcL, hex t u htu L hLt⟩)

end Rely

/-! ## 3. The invariant on every GX run -/

section Lauf

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {K : Faden → D.Fn → Bool} {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **The start machine is replayed** (as `zielInvS_start`). -/
theorem zielInvSA_start
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P (lokK P K) f)) = true)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hStart : StartGut P sp init) :
    ZielInvSA P O passes Q S (lokK P K) Tg (RufStartG P sp init) := by
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
    exact ⟨⟨[], [], [], [], sp.welt [], hStart t, funkV_nil, vertraegeOkR_nil P, kurzVBA_nil _,
      funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
      ⟨funkX_nil, kurzX_nil _⟩, GleichAuf.vonSpeicher rfl, ⟨hFragS _, fuss_rumpfG P _⟩,
      fun R O' U A _ _ _ _ _ _ => ZErgG.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- What a GX-reached machine satisfies besides the replay: the thread invariants the steps
    need. -/
structure FadenFakten (P : Programm D) (K : Faden → D.Fn → Bool) (M : RufMaschineG D) : Prop where
  halt : ∀ t, HaeltInvG (M.faeden t)
  exkl : Exklusiv M
  graph : ∀ t, ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, K t F.f = true

/-- **One GX step keeps the replay, the frame invariant and the machine lock invariant.** -/
theorem zielInvSA_schrittGX (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S (lokK P K) f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P (lokK P K) f)) = true)
    (hFS : ∀ f, FussSX P S (lokK P K) Tg f)
    {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittGX P O passes Tg M u M')
    (hFF : FadenFakten P K M)
    (hI : ZielInvSA P O passes Q S (lokK P K) Tg M) (hRS : RahmenInvS P S (lokK P K) M)
    (hSG : SperrInvG S M) :
    ZielInvSA P O passes Q S (lokK P K) Tg M' ∧ RahmenInvS P S (lokK P K) M' ∧ SperrInvG S M' := by
  obtain ⟨σ, M'', hs1, hσ, h1, h2, hfa, _, _⟩ := hs
  let M1 := mitSpeicher M σ
  have hM1f : M1.faeden = M.faeden := rfl
  -- memory moves between M, M1, M'', M' only at shared atomics (or where the step wrote)
  have hj : ∀ c, ¬ Tg c → TraegerGleich M1.speicher M.speicher c := hσ
  have ha : ∀ c, ¬ Tg c → TraegerGleich M'.speicher M''.speicher c := gx_aussen hσ h1 h2
  have hfe : ∀ t, M'.faeden t = M''.faeden t := fun t => by rw [hfa]
  -- the machine lock invariant at M1
  have hSG1 : SperrInvG S M1 := by
    intro L hL
    rw [← hSG L hL]
    exact hS.2 L _ _ fun c hc => hj c fun ht => hTO c ht L hc
  -- the replay of u at M1
  have hFu1 : FadenSA P O passes Q S (lokK P K) Tg (M1.faeden u) (M1.weltVon u) :=
    fadenSA_speicher (hI.1 u) fun c hc => hj c fun ht => hTS c ht _ _ hc
  have hRSu1 : RahmenStapelS P S (lokK P K) M1.speicher (RufSchluesselG (M1.faeden u).kopf)
      (M1.faeden u).stapel :=
    rahmenStapelS_fremd (hRS u) fun F _ c hc => hj c fun ht => hTS c ht _ _ hc
  have hA := akteurSA hO hRL hQ hlok hS hsp hK hTV hFragS hFS hs1 hFu1 (hI.2 u) hRSu1 hSG1
  -- the rely for the other threads, from the thread invariants at M1 (= M's threads)
  have hFF1 : FadenFakten P K M1 := ⟨hFF.halt, hFF.exkl, hFF.graph⟩
  have hrely : ∀ t, t ≠ u → ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel,
      ∀ c ∈ stabilS P S (lokK P K) F.f F.rest.2.2.1, TraegerGleich M'.speicher M.speicher c := by
    intro t htu F hF c hc
    have hnt : ¬ Tg c := fun ht => hTS c ht _ _ hc
    exact traegerGleich_trans (ha c hnt) (traegerGleich_trans
      (stabilS_relyX hO hS hs1 hFF1.halt hFF1.exkl hFF1.graph t htu F hF c hc) (hj c hnt))
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_⟩
  · by_cases htu : t = u
    · subst htu
      have e : M'.weltVon t = M'.speicher.welt (M''.faeden t).spur := by
        unfold RufMaschineG.weltVon; rw [hfe]
      rw [e, hfe]
      exact fadenSA_speicher hA.1 fun c hc => ha c fun ht => hTS c ht _ _ hc
    · have e0 : M''.faeden t = M.faeden t := rufSchrittG_fremd hs1 t htu
      have e : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
        unfold RufMaschineG.weltVon; rw [hfe, e0]
      rw [e, hfe, e0]
      exact fadenSA_speicher (hI.1 t) fun c hc => hrely t htu _ List.mem_cons_self c hc
  · by_cases htu : t = u
    · subst htu
      rw [hfe]
      exact hA.2
    · rw [hfe, rufSchrittG_fremd hs1 t htu]
      exact hI.2 t
  · by_cases htu : t = u
    · subst htu
      have h3 := rahmenStapelS_akteur hO hs1 hRSu1
      show RahmenStapelS P S (lokK P K) M'.speicher (RufSchluesselG (M'.faeden t).kopf)
        (M'.faeden t).stapel
      rw [hfe]
      exact rahmenStapelS_fremd h3 fun F _ c hc => ha c fun ht => hTS c ht _ _ hc
    · show RahmenStapelS P S (lokK P K) M'.speicher (RufSchluesselG (M'.faeden t).kopf)
        (M'.faeden t).stapel
      rw [hfe, rufSchrittG_fremd hs1 t htu]
      exact rahmenStapelS_fremd (hRS t) fun F hF c hc =>
        hrely t htu F (List.mem_cons_of_mem _ hF) c hc
  · -- the machine lock invariant: at M'' by the release check, then at M'
    have hSG'' : SperrInvG S M'' := by
      refine sperrInvG_schritt hO hS hs1 hSG1 (fun L hL hL' => ?_)
      rcases freigabe_schrittG hO hs1 with hgr | ⟨l, Γ, Λ, L', k, ρ, hhead, hsp', hoff⟩ |
          ⟨Γ, Λ, Λ1, L', rest, k, ρ, h, x, hhead, hsp', hoff⟩
      · exact absurd (hgr L hL) hL'
      · have hLL : L = L' := by
          refine Classical.byContradiction fun hne => hL' ?_
          rw [hoff]
          exact (List.mem_erase_of_ne hne).mpr hL
        subst hLL
        rw [hsp']
        exact kopfSA_frei_inv hO hRL hQ hS hsp hK hFu1.1 L List.mem_cons_self hhead
          (fun O' U A R σ hi => semHA_frei_falsch S O' U A passes R L k σ ρ hi)
      · have hLL : L = L' := by
          refine Classical.byContradiction fun hne => hL' ?_
          rw [hoff]
          exact (List.mem_erase_of_ne hne).mpr hL
        subst hLL
        rw [hsp']
        exact kopfSA_frei_inv hO hRL hQ hS hsp hK hFu1.1 L
          ((Block.held_iff rest L).mp List.mem_cons_self) hhead
          (fun O' U A R σ hi => semHA_peelFrei_falsch S O' U A passes R L rest k σ ρ h x hi)
    intro L hL
    have hL'' : ∀ t, L ∉ offen (M''.faeden t).spur := fun t => by rw [← hfe]; exact hL t
    rw [← hSG'' L hL'']
    exact hS.2 L _ _ fun c hc => ha c fun ht => hTO c ht L hc

/-- **The thread facts on every GX run** (shared atomics inside the atomics: GX runs are GA runs,
    and the thread invariants of GA hold). -/
theorem fadenFakten_GX {fs : List D.Fn} (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    {M : RufMaschineG D} (hr : RufErreichbarGX P O passes Tg (RufStartG P sp init) M) :
    FadenFakten P K M := by
  have hrA := gx_ga_lauf hTA hr
  refine ⟨?_, gaInv_exklusiv hO sp init hex hrA, fun t F hF => ?_⟩
  · refine gaInv (I := fun M => ∀ t, HaeltInvG (M.faeden t))
      (fun M M' e h t => by rw [← e]; exact h t) (haeltInvG_start P sp init) ?_ hrA
    intro M M' u h hs t
    by_cases htu : t = u
    · subst htu; exact rufSchrittG_haeltInv hO hs (h t)
    · rw [rufSchrittG_fremd hs t htu]; exact h t
  · exact (gaInv_merk (P := P) (O := O) (passes := passes) sp init (fun t f => K t f = true)
      (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hrA t F hF).1

/-- **THE REPLAY WITH THE ATOMIC RELY ON EVERY GX RUN** (as `zielInvS_erreichbarL` over GX): the
    replay, the frame invariant and the machine lock invariant hold at every machine GX reaches,
    for thread-local carriers over closed per-thread call graphs. -/
theorem zielInvSA_erreichbarGX (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) {fs : List D.Fn} (K : Faden → D.Fn → Bool) (Tg : D.Tab ⊕ D.Glob → Prop)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S (lokK P K) f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P (lokK P K) f)) = true)
    (hFS : ∀ f, FussSX P S (lokK P K) Tg f)
    (hK : ∀ f : D.Fn, KoerperGutSA P passes Q S Tg f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      ZielInvSA P O passes Q S (lokK P K) Tg M ∧ RahmenInvS P S (lokK P K) M ∧ SperrInvG S M := by
  intro M hr
  induction hr with
  | start =>
      refine ⟨zielInvSA_start hFragS sp init hStart, fun t => ?_, sperrInvG_start P S sp init hsp⟩
      show RahmenStapelS P S (lokK P K) sp _ ((RufStartG P sp init).faeden t).stapel
      have e : ((RufStartG P sp init).faeden t).stapel = [] := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).stapel = []
        cases init t
        rfl
      rw [e]
      trivial
  | schritt M M' u hr' hs ih =>
      exact zielInvSA_schrittGX hO hRL hQ hlok hS hsp hK hTV hTS hTO hFragS hFS hs
        (fadenFakten_GX hO hvoll hTA sp init hex hAbg hWurzel hr') ih.1 ih.2.1 ih.2.2

/-- **A replayed thread is stopped at no `logik` check of G** (as `fadenS_prueft`): the check
    reads the MACHINE's memory; the rely lets the sequential run read the same values at the
    shared atomics (a record made here), so a failing check would be a `logik` outcome of the
    obligation. -/
theorem fadenSA_prueft (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hFS : ∀ f, FussSX P S (lokK P K) Tg f)
    {M : RufMaschineG D} (t : Faden)
    (hF : FadenSA P O passes Q S (lokK P K) Tg (M.faeden t) (M.weltVon t)) :
    PrueftG O passes M t := by
  have hK' := hF.1
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s Kr hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ inv.orte (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    refine wahr_of_nicht_falsch fun hw => hno _ (passtX_teil hsub hPX) hHA .schleife ?_
    apply semHA_trav_falsch
    rw [hrec _ hPX hHA, eval_gleichAuf inv (fun _ h => List.mem_append_right _ h)
      (mischT_gleichAuf hg (expr_stabilX (hFS _) inv hok.1) Λ Λ) ρ]
    exact hw
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ inv.orte (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    refine wahr_of_nicht_falsch fun hw => hno _ (passtX_teil hsub hPX) hHA .schleife ?_
    apply semHA_ewig_falsch
    rw [hrec _ hPX hHA, eval_gleichAuf inv (fun _ h => List.mem_append_right _ h)
      (mischT_gleichAuf hg (expr_stabilX (hFS _) inv hok.1) Λ Λ) ρ]
    exact hw
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hK' hr
    have hg' := gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg
    obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ inv.orte (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    refine wahr_of_nicht_falsch fun hw => hno _ (passtX_teil hsub hPX) hHA .schleife ?_
    apply semHA_leaveTrav_falsch
    rw [hrec _ hPX hHA, eval_gleichAuf inv (fun _ h => List.mem_append_right _ h)
      (mischT_gleichAuf hg' (expr_stabilX (hFS _) inv hok.2.2.1) Λ Λ) ρ]
    exact hw
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨_, hss, _⟩ := okS_ende_cons hok
    have hXs := orte_stabilX (hFS _) (s.blatt_darf P hb) hss
    obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ (stmtOrteP P s) (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    have hĝ : GleichAuf (stabilS P S (lokK P K) (M.faeden t).kopf.f Λ ++ stmtOrteP P s)
        (vorA (umweltAusA Tg HX') σ Λ (stmtOrteP P s)) (M.weltVon t) := by
      rw [vorA_eq (hrec _ hPX hHA)]
      exact mischT_gleichAuf hg hXs Λ Λ
    have h' := blatt_logik P s hb (fun _ h => List.mem_append_right _ h) hĝ O (orakelAus O HA)
      passes keinRuf (rufAusL H) ρ e he
    refine hno _ (passtX_teil hsub hPX) hHA e ?_
    show zErgG (execEndHA S (orakelAus O HA) (umweltAus S sp HU) (umweltAusA Tg HX') passes
      (rufAusL H) (.cons s Kr) σ ρ) = _
    simp only [execEndHA, execStmtHA_blatt P S (orakelAus O HA) (umweltAus S sp HU) hHA passes
      (rufAusL H) s hb, h', zErgG]
  · obtain ⟨H, HA, HU, HX, σ, hfx, hkx, hg, hok, hno⟩ :=
      kopfSA_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨_, hss, _⟩ := okS_dann_cons hok
    have hXs := orte_stabilX (hFS _) (s.blatt_darf P hb) hss
    obtain ⟨HX', hfx', _, hsub, hrec⟩ := lese_schritt Tg hfx hkx Λ (stmtOrteP P s) (M.weltVon t).speicher
    have hPX := umweltAusA_passt Tg hfx'
    have hHA := umweltAusA_ok Tg HX'
    have hĝ : GleichAuf (stabilS P S (lokK P K) (M.faeden t).kopf.f Λ ++ stmtOrteP P s)
        (vorA (umweltAusA Tg HX') σ Λ (stmtOrteP P s)) (M.weltVon t) := by
      rw [vorA_eq (hrec _ hPX hHA)]
      exact mischT_gleichAuf hg hXs Λ Λ
    have h' := blatt_logik P s hb (fun _ h => List.mem_append_right _ h) hĝ O (orakelAus O HA)
      passes keinRuf (rufAusL H) ρ e he
    refine hno _ (passtX_teil hsub hPX) hHA e ?_
    rw [semHA_dann_cons, execStmtHA_blatt P S (orakelAus O HA) (umweltAus S sp HU) hHA passes
      (rufAusL H) s hb, h']
    exact weiterHA_logik _ _ _ _ _ _ _ e

/-- **THE CONTRACT LEGS OVER GX** (as `ziel_ort_sperre` over G): on every machine GX reaches --
    G with the shared atomics answered by the weak memory -- the contracts hold at every logged
    entry and return, every free lock has its invariant, and no thread stands at a failing
    check. The user's obligation is `KoerperGutSA`: the rely at every shared atomic read. -/
theorem ziel_ort_atomar (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) {fs : List D.Fn} (K : Faden → D.Fn → Bool) (Tg : D.Tab ⊕ D.Glob → Prop)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hTS : ∀ c, Tg c → ∀ f Λ, c ∉ stabilS P S (lokK P K) f Λ)
    (hTO : ∀ c, Tg c → ∀ L, c ∉ S.orte L)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P (lokK P K) f)) = true)
    (hFS : ∀ f, FussSX P S (lokK P K) Tg f)
    (hK : ∀ f : D.Fn, KoerperGutSA P passes Q S Tg f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarGX P O passes Tg (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M := by
  intro M hr
  have hI := zielInvSA_erreichbarGX P O passes Q S K Tg sp init hO hRL hQ hlok hS hvoll hAbg
    hWurzel hTA hTV hTS hTO hFragS hFS hK hStart hsp hex M hr
  exact ⟨fun t ev hev => hI.1.2 t ev hev, hI.2.2,
    fun t => fadenSA_prueft hO hRL hQ hS hsp hK hFS t (hI.1.1 t)⟩

#print axioms Gabbro.Grammatik.zielInvSA_schrittGX
#print axioms Gabbro.Grammatik.zielInvSA_erreichbarGX
#print axioms Gabbro.Grammatik.ziel_ort_atomar

end Lauf

end Gabbro.Grammatik
