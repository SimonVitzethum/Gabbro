module

public import Grammatik.Speichermodell.Maschine.DRF
public import Grammatik.Speichermodell.Atomar.Atomar.Teil1

@[expose] public section

namespace Gabbro.Grammatik
open Speichermodell
variable {D : Deklaration}
section Schritt
variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} {sp : Speicher D}
  {init : Faden → Σ f : D.Fn, Env D (D.params f)} {K : Faden → D.Fn → Bool}

/-- **ONE STEP OF W ON A PROGRAM WITH RACING ATOMICS IS A STEP OF GA, and keeps the
    invariant.** -/
theorem schritt_sichtInvA (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSA P S (lokK P K) f) (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hI : SichtInvA (P := P) (O := O) (passes := passes) sp init K W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    RufSchrittGA P O passes W.g u W'.g ∧
      SichtInvA (P := P) (O := O) (passes := passes) sp init K W' := by
  have hσ := praesentiert_gA hO hvoll hAbg hWurzel hI h
  have hs := h.schritt
  have hr := hI.erreicht
  have hGA : RufSchrittGA P O passes W.g u W'.g :=
    ⟨σ, M'', hs, hσ, h.speicherS, h.speicherU, h.faeden, h.lauf, h.start⟩
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
  refine ⟨hGA, hr', ?_, ?_, ?_, ?_⟩
  · -- `frei`
    intro c t hB hA ht m hm
    by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u c
    · have htu := frei_schreiberA hO hvoll hAbg hWurzel hFuss hr hs hB hA hw ht
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
          have htu := frei_schreiberA hO hvoll hAbg hWurzel hFuss hr hs hB' hA hw ht
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
theorem sichtInvA_erreichbar (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSA P S (lokK P K) f) (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    SichtInvA (P := P) (O := O) (passes := passes) sp init K W := by
  induction hr with
  | start => exact sichtInvA_start sp init K
  | schritt W W' u _ hs ih =>
      obtain ⟨σ, M'', wahl, neu, h⟩ := hs
      exact (schritt_sichtInvA hO hvoll hAbg hWurzel hFuss hex ih h).2

/-- **THE DRF THEOREM WITH RACING ATOMICS, one step.** On a program whose footprints satisfy
    `FussSA` (plain carriers local or guarded, atomics free), from every state W reaches:
    every step of W is a step of GA from W's G-part to the successor's G-part, and the memory
    it is presented agrees with G's at EVERY non-atomic carrier -- plain carriers are
    sequentially consistent, whatever the atomics do. -/
theorem schwach_ist_gA (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSA P S (lokK P K) f) (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    RufSchrittGA P O passes W.g u W'.g ∧
      ∀ c, ¬ AtomarAusgenommen c → TraegerGleich σ W.g.speicher c := by
  have hI := sichtInvA_erreichbar hO hvoll hAbg hWurzel hFuss hex hr
  exact ⟨(schritt_sichtInvA hO hvoll hAbg hWurzel hFuss hex hI h).1,
    praesentiert_gA hO hvoll hAbg hWurzel hI h⟩

/-- **A plain read on a program with racing atomics is the newest write.** -/
theorem plain_liest_neueste (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSA P S (lokK P K) f) (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hA : ¬ AtomarAusgenommen c) (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
    ∀ m ∈ W.hist c, m.ts ≤ (wahl c).ts :=
  (liest_neuesteA hO hvoll hAbg hWurzel (sichtInvA_erreichbar hO hvoll hAbg hWurzel hFuss hex hr)
    h hA hl).1

/-- **THE DRF THEOREM WITH RACING ATOMICS, runs**: every machine W reaches has a G-part that GA
    reaches -- and so the trace invariant (`SpurInv`, memory safety of the trace) and lock
    exclusivity hold there (`gaInv_spur`, `gaInv_exklusiv`). -/
theorem ga_aus_w (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSA P S (lokK P K) f) (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    RufErreichbarGA P O passes (RufStartG P sp init) W.g :=
  (sichtInvA_erreichbar hO hvoll hAbg hWurzel hFuss hex hr).erreicht

/-- Memory safety of the trace and lock exclusivity at every machine W reaches, racing atomics
    included. -/
theorem w_spur_exklusiv (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSA P S (lokK P K) f) (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    SpurInv W.g ∧ Exklusiv W.g :=
  have h := ga_aus_w hO hvoll hAbg hWurzel hFuss hex hr
  ⟨gaInv_spur hO sp init h, gaInv_exklusiv hO sp init hex h⟩

/-- **The old theorem is the special case**: with the old footprint property every W step
    presents G's memory everywhere (`schwach_ist_g`), and the new theorem applies too, with the
    weaker conclusion at atomic carriers. -/
theorem schwach_ist_gA_vor (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f) (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) {u : Faden}
    (hs : RufSchrittW P O passes ord W u W') :
    RufSchrittG P O passes W.g u W'.g ∧ RufSchrittGA P O passes W.g u W'.g :=
  have h := schwach_ist_g hO hvoll hAbg hWurzel hFuss hex hr hs
  ⟨h, schrittGA_of_g h⟩

end Schritt

end Gabbro.Grammatik
