/-
  File:      Grammatik/Speichermodell/AtomarW.lean
  Subject:   THE DRF THEOREM WITH SHARED ATOMICS: machine W on a program whose footprints
             satisfy `FussSX` takes only steps of GX -- the memory a step is presented agrees
             with G's at every carrier outside the shared atomics `Tg` (thread-local atomics
             included, which Atomar.lean's GA left free). A copy of Atomar.lean §3 with the free
             class "not in `Tg`" in place of "not atomic". Opus lane O25b, 2026-09-26.
-/
import Grammatik.Speichermodell.AtomarLauf

namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-- **An unguarded footprint carrier outside `Tg` is thread-local** (`getrennt_of_freiA` for
    `FussSX`). -/
theorem getrennt_of_freiX {P : Programm D} {S : SperrInv D} {K : Faden → D.Fn → Bool}
    {Tg : D.Tab ⊕ D.Glob → Prop} {f : D.Fn}
    (hF : FussSX P S (lokK P K) Tg f) {c : D.Tab ⊕ D.Glob} (hc : c ∈ fussOrteG P f)
    (hB : ∀ L, ¬ Bewacht c L) (hA : ¬ Tg c) : GetrenntK P K c := by
  have hsig : sigB f c = false := by
    cases h : sigB f c
    · rfl
    · obtain ⟨L, hL, _⟩ := List.any_eq_true.mp h
      exact absurd (waechterVon_mem.mp hL) (hB L)
  rcases List.mem_append.mp hc with hc | hc
  · rcases hF.1 c hc with h | ⟨L, hL, _⟩ | h
    · rw [hsig, Bool.false_or] at h
      exact lokK_ok h
    · exact absurd hL (hB L)
    · exact absurd h hA
  · have h := hF.2 c hc
    rw [hsig, Bool.false_or] at h
    exact lokK_ok h


section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} (sp : Speicher D)
  (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool) (Tg : D.Tab ⊕ D.Glob → Prop)

/-- **The view invariant of W with racing atomics.** As `SichtInv` (DRF.lean), with two
    changes: G's part is reached by GA (not by G), and the fields `frei` and `stimmt` speak
    about NON-atomic carriers only -- at an atomic carrier W's reads are free. -/
structure SichtInvX (W : RufMaschineW D) : Prop where
  erreicht : RufErreichbarGA P O passes (RufStartG P sp init) W.g
  frei : ∀ c t, (∀ L, ¬ Bewacht c L) → ¬ Tg c → LesbarK P K t c →
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  halter : ∀ c L, Bewacht c L → ∀ t, L ∈ offen (W.g.faeden t).spur →
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  sperre : ∀ c L, Bewacht c L → (∀ t, L ∉ offen (W.g.faeden t).spur) →
    ∀ m ∈ W.hist c, m.ts ≤ W.lsicht L c
  stimmt : ∀ c, ¬ Tg c → (∃ t, LesbarK P K t c) → ∀ m ∈ W.hist c,
    (∀ m' ∈ W.hist c, m'.ts ≤ m.ts) → TraegerGleich W.g.speicher m.wert c

theorem sichtInvX_start :
    SichtInvX (P := P) (O := O) (passes := passes) sp init K Tg (RufStartW (RufStartG P sp init)) where
  erreicht := .start
  frei _ _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  halter _ _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  sperre _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  stimmt c _ _ m hm _ := by rw [List.mem_singleton.mp hm]; exact traegerGleich_refl _ c

end Inv

section Schritt

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} {sp : Speicher D}
  {init : Faden → Σ f : D.Fn, Env D (D.params f)} {K : Faden → D.Fn → Bool}
  {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **A read of a NON-atomic carrier is the newest message, and it carries G's value.** -/
theorem liest_neuesteX (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W W' : RufMaschineW D}
    (hI : SichtInvX (P := P) (O := O) (passes := passes) sp init K Tg W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hA : ¬ Tg c) (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
    (∀ m ∈ W.hist c, m.ts ≤ (wahl c).ts) ∧ TraegerGleich W.g.speicher (wahl c).wert c := by
  obtain ⟨hK, hL⟩ := lies_faktenA hO hvoll hAbg hWurzel hI.erreicht h.schritt hl
  obtain ⟨⟨hmem, hv⟩, _⟩ := h.lies c hl
  have hoben : ∀ m ∈ W.hist c, m.ts ≤ (wahl c).ts := by
    by_cases hB : ∃ L, Bewacht c L
    · obtain ⟨L, hB⟩ := hB
      exact fun m hm => Nat.le_trans (hI.halter c L hB u (hL L hB) m hm) hv
    · exact fun m hm => Nat.le_trans (hI.frei c u (fun L h => hB ⟨L, h⟩) hA hK m hm) hv
  exact ⟨hoben, hI.stimmt c hA ⟨u, hK⟩ (wahl c) hmem hoben⟩

/-- **The presented memory is G's at every NON-atomic carrier.** -/
theorem praesentiert_gX (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W W' : RufMaschineW D}
    (hI : SichtInvX (P := P) (O := O) (passes := passes) sp init K Tg W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (c : D.Tab ⊕ D.Glob) (hA : ¬ Tg c) : TraegerGleich σ W.g.speicher c := by
  by_cases hl : LiestG (mitSpeicher W.g σ) M'' u c
  · have h1 := (h.lies c hl).2
    have h2 := (liest_neuesteX hO hvoll hAbg hWurzel hI h hA hl).2
    exact traegerGleich_trans h1 (traegerGleich_symm h2)
  · exact h.ungelesen c hl

/-- A write of thread `u` to an unguarded NON-atomic carrier some thread `t` reads: `t` is
    `u` (over a GA-reached machine). -/
theorem frei_schreiberX (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) (hFuss : ∀ f, FussSX P S (lokK P K) Tg f)
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M)
    {σ : Speicher D} {M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes (mitSpeicher M σ) u M') {c : D.Tab ⊕ D.Glob}
    (hB : ∀ L, ¬ Bewacht c L) (hA : ¬ Tg c)
    (hw : SchreibG (mitSpeicher M σ) M' u c) {t : Faden} (ht : LesbarK P K t c) : t = u := by
  apply Classical.byContradiction
  intro htu
  obtain ⟨f, hf, hc⟩ := ht
  have hOrte : OrteInvG P ((mitSpeicher M σ).faeden u) := gaInv_orte sp init hr u
  have hInv := gaInv_merk (P := P) (O := O) (passes := passes) sp init (fun t f => K t f = true)
    (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
  have hK : K u ((mitSpeicher M σ).faeden u).kopf.f = true := (hInv u _ List.mem_cons_self).1
  have hgw := (schritt_zugriffeA hO hOrte hs c).2 hw
  have := getrennt_of_freiX (hFuss f) hc hB hA t u htu f hf hc _ hK
  rw [this] at hgw
  cases hgw

/-- **ONE STEP OF W ON A PROGRAM WITH RACING ATOMICS IS A STEP OF GA, and keeps the
    invariant.** -/
theorem schritt_sichtInvX (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S (lokK P K) Tg f) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hI : SichtInvX (P := P) (O := O) (passes := passes) sp init K Tg W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    RufSchrittGX P O passes Tg W.g u W'.g ∧
      SichtInvX (P := P) (O := O) (passes := passes) sp init K Tg W' := by
  have hσ := praesentiert_gX hO hvoll hAbg hWurzel hI h
  have hs := h.schritt
  have hr := hI.erreicht
  have hGX : RufSchrittGX P O passes Tg W.g u W'.g :=
    ⟨σ, M'', hs, hσ, h.speicherS, h.speicherU, h.faeden, h.lauf, h.start⟩
  have hGA : RufSchrittGA P O passes W.g u W'.g := gx_ga hTA hGX
  have hr' : RufErreichbarGA P O passes (RufStartG P sp init) W'.g := .schritt _ _ _ hr hGA
  -- the thread-local invariants, before (on the presented machine) and after the step
  have hSp' : SpurInv M'' := by
    have := gaInv_spur hO sp init hr'
    intro t; have e := h.faeden; rw [← e]; exact this t
  have hEx : Exklusiv W.g := gaInv_exklusiv hO sp init hex hr
  have hEx' : Exklusiv W'.g := gaInv_exklusiv hO sp init hex hr'
  have hfaeden : W'.g.faeden = M''.faeden := h.faeden
  have hge : ∀ x, W.sicht u x ≤ vorSicht ord W u σ M'' wahl x :=
    fun x => vorSicht_ge W u _ M'' wahl x
  -- a written carrier: new message; the writer's view before the write bounds the old ones
  have hneu : ∀ c, SchreibG (mitSpeicher W.g σ) M'' u c →
      (∀ m ∈ W.hist c, m.ts ≤ W.sicht u c) → ∀ m ∈ W.hist c, m.ts < neu c := by
    intro c hw hb m hm
    exact Nat.lt_of_le_of_lt (Nat.le_trans (hb m hm) (hge c)) (h.frisch c hw).1
  -- the guard of an access is held before and after, on the presented machine
  have haelt : ∀ c L, Bewacht c L → ZugriffG (mitSpeicher W.g σ) M'' u c →
      L ∈ offen (W.g.faeden u).spur ∧ L ∈ offen (W'.g.faeden u).spur := by
    intro c L hB hz
    have := zugriff_haeltA hO hs hSp' hB hz
    exact ⟨this.1, by rw [hfaeden]; exact this.2⟩
  have hfremd : ∀ t, t ≠ u → W'.g.faeden t = W.g.faeden t := by
    intro t ht; rw [hfaeden]; exact rufSchrittG_fremd hs t ht
  refine ⟨hGX, hr', ?_, ?_, ?_, ?_⟩
  · -- `frei`
    intro c t hB hA ht m hm
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u c
    · have htu := frei_schreiberX hO hvoll hAbg hWurzel hFuss hr hs hB hA hw ht
      subst htu
      rw [h.histS c hw] at hm
      rw [h.sichtS c hw]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (hneu c hw (hI.frei c t hB hA ht) m hm)
    · rw [h.histU c hw] at hm
      exact Nat.le_trans (hI.frei c t hB hA ht m hm) (sicht_waechst h t c)
  · -- `halter`
    intro c L hB t ht m hm
    by_cases htu : t = u
    · subst htu
      by_cases hw : SchreibG (mitSpeicher W.g σ) M'' t c
      · have hvor := (haelt c L hB (zugriff_of_schreib hw)).1
        rw [h.histS c hw] at hm
        rw [h.sichtS c hw]
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Nat.le_refl _
        · exact Nat.le_of_lt (hneu c hw (hI.halter c L hB t hvor) m hm)
      · rw [h.histU c hw] at hm
        by_cases hvor : L ∈ offen (W.g.faeden t).spur
        · exact Nat.le_trans (hI.halter c L hB t hvor m hm) (sicht_waechst h t c)
        · -- the step takes `L`: nobody held it before
          have ht' : L ∈ offen (M''.faeden t).spur := by rw [← hfaeden]; exact ht
          have hnimm := genommen_von hO hs hvor ht'
          have hkein : ∀ t', L ∉ offen (W.g.faeden t').spur := by
            intro t' ht''
            by_cases e : t' = t
            · subst e; exact hvor ht''
            · have := hEx' t t' (Ne.symm e) L ht
              rw [hfremd t' e] at this
              exact this ht''
          have h1 := hI.sperre c L hB hkein m hm
          have h2 : W.lsicht L c ≤ vorSicht ord W t σ M'' wahl c :=
            locksicht_mem _ _ _ L hnimm c
          rw [h.sichtU c hw]
          exact Nat.le_trans h1 h2
    · have ht0 : L ∈ offen (W.g.faeden t).spur := by rw [← hfremd t htu]; exact ht
      by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u c
      · have hu := (haelt c L hB (zugriff_of_schreib hw)).1
        exact absurd ht0 (hEx u t (Ne.symm htu) L hu)
      · rw [h.histU c hw] at hm
        rw [h.sichtF t htu]
        exact hI.halter c L hB t ht0 m hm
  · -- `sperre`
    intro c L hB hkein m hm
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u c
    · exact absurd (haelt c L hB (zugriff_of_schreib hw)).2 (hkein u)
    · rw [h.histU c hw] at hm
      by_cases hvor : ∀ t, L ∉ offen (W.g.faeden t).spur
      · exact Nat.le_trans (hI.sperre c L hB hvor m hm) (lsicht_waechst h L c)
      · -- someone held `L` before: only `u` can have let go of it
        have hu : L ∈ offen (W.g.faeden u).spur := by
          apply Classical.byContradiction
          intro hu
          apply hvor
          intro t ht
          by_cases e : t = u
          · subst e; exact hu ht
          · have := hkein t
            rw [hfremd t e] at this
            exact this ht
        have hk' : L ∉ offen (M''.faeden u).spur := by rw [← hfaeden]; exact hkein u
        have hgib := gegeben_von hO hs hu hk'
        have h1 := hI.halter c L hB u hu m hm
        rw [h.lsicht L, if_pos hgib]
        exact Nat.le_trans h1 (Nat.le_trans (sicht_waechst h u c) (Sicht.verein_rechts _ _ c))
  · -- `stimmt`
    intro c hA ⟨t, ht⟩ m hm hmax
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u c
    · rw [h.histS c hw] at hm hmax
      -- the writer's view reached every old message
      have hb : ∀ m ∈ W.hist c, m.ts ≤ W.sicht u c := by
        by_cases hB : ∃ L, Bewacht c L
        · obtain ⟨L, hB⟩ := hB
          exact hI.halter c L hB u (haelt c L hB (zugriff_of_schreib hw)).1
        · have hB' : ∀ L, ¬ Bewacht c L := fun L h' => hB ⟨L, h'⟩
          have htu := frei_schreiberX hO hvoll hAbg hWurzel hFuss hr hs hB' hA hw ht
          subst htu
          exact hI.frei c t hB' hA ht
      rcases List.mem_cons.mp hm with rfl | hm
      · exact traegerGleich_refl _ c
      · have h1 := hneu c hw hb m hm
        have h2 := hmax _ List.mem_cons_self
        simp only [nachricht] at h2
        omega
    · rw [h.histU c hw] at hm hmax
      exact traegerGleich_trans (h.speicherU c hw) (hI.stimmt c hA ⟨t, ht⟩ m hm hmax)

/-- **The invariant on every machine W reaches**, racing atomics included. -/
theorem sichtInvX_erreichbar (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S (lokK P K) Tg f) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    SichtInvX (P := P) (O := O) (passes := passes) sp init K Tg W := by
  induction hr with
  | start => exact sichtInvX_start sp init K Tg
  | schritt W W' u _ hs ih =>
      obtain ⟨σ, M'', wahl, neu, h⟩ := hs
      exact (schritt_sichtInvX hO hvoll hAbg hWurzel hFuss hTA hex ih h).2

/-- **THE DRF THEOREM WITH SHARED ATOMICS, one step.** On a program whose footprints satisfy
    `FussSX` (every carrier local or guarded, or a shared atomic of `Tg`), from every state W reaches:
    every step of W is a step of GX from W's G-part to the successor's G-part, and the memory
    it is presented agrees with G's at EVERY carrier outside `Tg` -- plain carriers and
    thread-local atomics are sequentially consistent, whatever the shared atomics do. -/
theorem schwach_ist_gX (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S (lokK P K) Tg f) (hTA : ∀ c, Tg c → AtomarAusgenommen c)
    (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    RufSchrittGX P O passes Tg W.g u W'.g ∧
      ∀ c, ¬ Tg c → TraegerGleich σ W.g.speicher c := by
  have hI := sichtInvX_erreichbar hO hvoll hAbg hWurzel hFuss hTA hex hr
  exact ⟨(schritt_sichtInvX hO hvoll hAbg hWurzel hFuss hTA hex hI h).1,
    praesentiert_gX hO hvoll hAbg hWurzel hI h⟩


end Schritt

#print axioms Gabbro.Grammatik.schritt_sichtInvX
#print axioms Gabbro.Grammatik.schwach_ist_gX

end Gabbro.Grammatik
