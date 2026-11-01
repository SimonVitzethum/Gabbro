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

/-! ## 4. Atomics per W: the release/acquire hand-off (happens-before), on every program -/

section Uebergabe

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}

/-- **A release write carries the writer's view**: the message a step of `u` writes at a carrier
    of order `freigabe` knows every OTHER carrier at least as new as `u` did before the step. -/
theorem schrittW_freigabe {W W' : RufMaschineW D} {u : Faden} {σ : Speicher D}
    {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' σ M'' wahl neu) {c : D.Tab ⊕ D.Glob}
    (hw : SchreibG (mitSpeicher W.g σ) M'' u c) (ho : ordVon ord c = .freigabe)
    {x : D.Tab ⊕ D.Glob} (hx : x ≠ c) :
    ∃ m ∈ W'.hist c, m.ts = neu c ∧ W.sicht u x ≤ m.sicht x := by
  rw [h.histS c hw]
  refine ⟨_, List.mem_cons_self, rfl, ?_⟩
  show W.sicht u x ≤ (match ordVon ord c with
    | .entspannt => Sicht.eins c (neu c)
    | .freigabe => (vorSicht ord W u σ M'' wahl).setze c (neu c)) x
  rw [ho]
  show W.sicht u x ≤ (if x = c then neu c else vorSicht ord W u σ M'' wahl x)
  rw [if_neg hx]
  exact vorSicht_ge W u σ M'' wahl x

/-- Messages are never removed: a W step keeps every message of every carrier. -/
theorem schrittW_hist {W W' : RufMaschineW D} {u : Faden} (hs : RufSchrittW P O passes ord W u W')
    (c : D.Tab ⊕ D.Glob) {m : NachrichtW D} (hm : m ∈ W.hist c) : m ∈ W'.hist c := by
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  by_cases hw : SchreibG (mitSpeicher W.g σ) M'' u c
  · rw [h.histS c hw]; exact List.mem_cons_of_mem _ hm
  · rw [h.histU c hw]; exact hm

/-- Views only grow along a W step, for every thread. -/
theorem schrittW_sicht {W W' : RufMaschineW D} {u : Faden}
    (hs : RufSchrittW P O passes ord W u W') (t : Faden) (x : D.Tab ⊕ D.Glob) :
    W.sicht t x ≤ W'.sicht t x := by
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  exact sicht_waechst h t x

/-- Along a W run from `W1`: messages stay, views grow. -/
theorem laufW_waechst {W1 W2 : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord W1 W2) :
    (∀ c m, m ∈ W1.hist c → m ∈ W2.hist c) ∧ (∀ t x, W1.sicht t x ≤ W2.sicht t x) := by
  induction hr with
  | start => exact ⟨fun _ _ h => h, fun _ _ => Nat.le_refl _⟩
  | schritt W W' u _ hs ih =>
      exact ⟨fun c m h => schrittW_hist hs c (ih.1 c m h),
        fun t x => Nat.le_trans (ih.2 t x) (schrittW_sicht hs t x)⟩

/-- **A read is at or above the reader's view** (every program, by `Lesbar`). -/
theorem schrittW_lies_ab {W W' : RufMaschineW D} {u : Faden} {σ : Speicher D}
    {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D} {neu : D.Tab ⊕ D.Glob → Nat}
    (h : SchrittW P O passes ord W u W' σ M'' wahl neu) {x : D.Tab ⊕ D.Glob}
    (hl : LiestG (mitSpeicher W.g σ) M'' u x) : W.sicht u x ≤ (wahl x).ts :=
  (h.lies x hl).1.2

/-- **THE HAPPENS-BEFORE HAND-OFF (message passing), on every program.** Thread `t` writes a
    carrier `c` of order `freigabe` (the flag, `publishes`) in the step `W1 → W2`; in a
    step `W3 → W4` thread `u` reads, with acquire, a message at `c` that is in `W2`'s history
    and not in `W1`'s -- exactly the one `t` wrote (`awaits`). Then for every OTHER carrier `x` -- the payload -- `u`'s
    view after the read is at least `t`'s view before the write, and every read of `x` by
    `u` from then on returns a message at or above it: whatever `t` had written or seen at
    `x` before its release, `u` never reads anything older. -/
theorem hb_uebergabe {W1 W2 W3 W4 : RufMaschineW D} {t u : Faden}
    {σ1 : Speicher D} {N1 : RufMaschineG D} {wahl1 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu1 : D.Tab ⊕ D.Glob → Nat}
    (h1 : SchrittW P O passes ord W1 t W2 σ1 N1 wahl1 neu1) {c : D.Tab ⊕ D.Glob}
    (hw : SchreibG (mitSpeicher W1.g σ1) N1 t c) (ho : ordVon ord c = .freigabe)
    {σ3 : Speicher D} {N3 : RufMaschineG D} {wahl3 : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu3 : D.Tab ⊕ D.Glob → Nat}
    (h3 : SchrittW P O passes ord W3 u W4 σ3 N3 wahl3 neu3)
    (hl : LiestG (mitSpeicher W3.g σ3) N3 u c)
    (hm2 : wahl3 c ∈ W2.hist c) (hm1 : wahl3 c ∉ W1.hist c)
    {x : D.Tab ⊕ D.Glob} (hx : x ≠ c) :
    W1.sicht t x ≤ W4.sicht u x ∧
      ∀ W5 W6 : RufMaschineW D, RufErreichbarW P O passes ord W4 W5 →
        ∀ (σ5 : Speicher D) (N5 : RufMaschineG D) (wahl5 : D.Tab ⊕ D.Glob → NachrichtW D)
          (neu5 : D.Tab ⊕ D.Glob → Nat), SchrittW P O passes ord W5 u W6 σ5 N5 wahl5 neu5 →
          LiestG (mitSpeicher W5.g σ5) N5 u x → W1.sicht t x ≤ (wahl5 x).ts := by
  have hm : wahl3 c = nachricht (ordVon ord c) (vorSicht ord W1 t σ1 N1 wahl1) c (neu1 c)
      W2.g.speicher := by
    rw [h1.histS c hw] at hm2
    rcases List.mem_cons.mp hm2 with e | e
    · exact e
    · exact absurd e hm1
  have e1 : W1.sicht t x ≤ (wahl3 c).sicht x := by
    rw [hm]
    show W1.sicht t x ≤ (match ordVon ord c with
      | .entspannt => Sicht.eins c (neu1 c)
      | .freigabe => (vorSicht ord W1 t σ1 N1 wahl1).setze c (neu1 c)) x
    rw [ho]
    show W1.sicht t x ≤ (if x = c then neu1 c else vorSicht ord W1 t σ1 N1 wahl1 x)
    rw [if_neg hx]
    exact vorSicht_ge W1 t σ1 N1 wahl1 x
  have e2 := schrittW_erwerb h3 hl ho x
  have hv : W1.sicht t x ≤ W4.sicht u x := Nat.le_trans e1 e2
  refine ⟨hv, fun W5 W6 h45 σ5 N5 wahl5 neu5 h5 hl5 => ?_⟩
  exact Nat.le_trans hv (Nat.le_trans ((laufW_waechst h45).2 u x) (schrittW_lies_ab h5 hl5))

end Uebergabe

/-! ## 5. Race freedom for plain carriers on every GA run -/

section Rennen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A GA step moves no other thread. -/
theorem ga_fremd {M M' : RufMaschineG D} {u : Faden} (h : RufSchrittGA P O passes M u M')
    (t : Faden) (ht : t ≠ u) : M'.faeden t = M.faeden t := by
  obtain ⟨σ, M'', hs, _, _, _, hfa, _, _⟩ := h
  rw [hfa]; exact rufSchrittG_fremd hs t ht

/-- **A GA step, taken apart**: its G step on the presented memory, and what an access, a write
    and the recorded events of the GA step are there. -/
theorem schrittGA_zerlegen {M M' : RufMaschineG D} {u : Faden}
    (h : RufSchrittGA P O passes M u M') :
    ∃ (σ : Speicher D) (M'' : RufMaschineG D), RufSchrittG P O passes (mitSpeicher M σ) u M'' ∧
      M'.faeden = M''.faeden ∧
      (∀ c, ZugriffG M M' u c → ZugriffG (mitSpeicher M σ) M'' u c) ∧
      (∀ c, SchreibG M M' u c → SchreibG (mitSpeicher M σ) M'' u c) ∧
      ereignisse M M' u = ereignisse (mitSpeicher M σ) M'' u := by
  obtain ⟨σ, M'', hs, _, _, hU, hfa, _, _⟩ := h
  have hz : zugriffe M M' u = zugriffe (mitSpeicher M σ) M'' u := by
    unfold zugriffe; rw [hfa]; rfl
  have he : ereignisse M M' u = ereignisse (mitSpeicher M σ) M'' u := by
    unfold ereignisse; rw [hfa]; rfl
  have hmem : ∀ c, ¬ TraegerGleich M'.speicher M.speicher c →
      SchreibG (mitSpeicher M σ) M'' u c := fun c hn =>
    Classical.byContradiction fun hw => hn (hU c hw)
  refine ⟨σ, M'', hs, hfa, fun c hc => ?_, fun c hc => ?_, he⟩
  · rcases hc with ⟨w, hw⟩ | hm
    · exact Or.inl ⟨w, by rw [← hz]; exact hw⟩
    · exact zugriff_of_schreib (hmem c hm)
  · rcases hc with hw | hm
    · exact Or.inl (by rw [← hz]; exact hw)
    · exact hmem c hm

/-- A run of GA of `n` steps from `M0`, by index. -/
def LaufGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D)
    (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat) : Prop :=
  ms 0 = M0 ∧ ∀ k, k < n → RufSchrittGA P O passes (ms k) (fs k) (ms (k + 1))

theorem laufGA_erreichbar {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} (hl : LaufGA P O passes M0 ms fs n) : ∀ k, k ≤ n → RufErreichbarGA P O passes M0 (ms k)
  | 0, _ => by rw [hl.1]; exact .start
  | k + 1, hk => .schritt _ _ _ (laufGA_erreichbar hl k (by omega)) (hl.2 k (by omega))

/-- **The ordering through a lock on a GA run** (`sperre_ordnet` over GA). -/
theorem sperre_ordnetGA (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hex : StartExklusiv init) {ms : Nat → RufMaschineG D} {fs : Nat → Faden}
    {n : Nat} (hl : LaufGA P O passes (RufStartG P sp init) ms fs n) (i j : Nat) (hij : i < j)
    (hjn : j < n) (hfg : fs i ≠ fs j) (L : D.Lock)
    (hi : L ∈ offen ((ms (i + 1)).faeden (fs i)).spur)
    (hj : L ∈ offen ((ms j).faeden (fs j)).spur) : GeordnetG ms fs L i j := by
  have hx : ∀ k, k ≤ n → ∀ u v : Faden, u ≠ v → L ∈ offen ((ms k).faeden u).spur →
      L ∉ offen ((ms k).faeden v).spur :=
    fun k hk u v huv hu => gaInv_exklusiv hO sp init hex (laufGA_erreichbar hl k hk) u v huv L hu
  obtain ⟨r, hr1, hr2, hQr, hQr1⟩ := erster_wechsel
    (fun k => L ∈ offen ((ms k).faeden (fs i)).spur) j (i + 1) (by omega) hi
    (hx j (by omega) (fs j) (fs i) (Ne.symm hfg) hj)
  have hsr := hl.2 r (by omega)
  have hfr : fs r = fs i := by
    apply Classical.byContradiction
    intro hne
    exact hQr1 (by rw [ga_fremd hsr (fs i) (Ne.symm hne)]; exact hQr)
  rw [hfr] at hsr
  have hgibt : Ereignis.gibt L ∈ ereignisse (ms r) (ms (r + 1)) (fs i) := by
    obtain ⟨σ, M'', hs, hfa, _, _, he⟩ := schrittGA_zerlegen hsr
    have hQr1' : L ∉ offen (M''.faeden (fs i)).spur := by rw [← hfa]; exact hQr1
    rw [he]
    rcases schritt_delta hO hs with ⟨_, _, _, _, _, hoff⟩ | ⟨⟨X, eX, _, _⟩, _⟩
    · have hoff' : offen (M''.faeden (fs i)).spur = offen ((ms r).faeden (fs i)).spur := hoff
      exact absurd (by rw [hoff']; exact hQr) hQr1'
    · have eX' : (M''.faeden (fs i)).spur = X ++ ((ms r).faeden (fs i)).spur := eX
      rw [ereignisse_eq eX]
      exact gibt_aus_offen L X _ hQr (by rw [← eX']; exact hQr1')
  have hn1 : L ∉ offen ((ms (r + 1)).faeden (fs j)).spur := by
    rw [ga_fremd hsr (fs j) (Ne.symm hfg)]
    exact hx r (by omega) (fs i) (fs j) hfg hQr
  obtain ⟨a, ha1, ha2, hQa, hQa1⟩ := erster_wechsel
    (fun k => L ∉ offen ((ms k).faeden (fs j)).spur) j (r + 1) (by omega) hn1
    (fun h => h hj)
  have hQa1' : L ∈ offen ((ms (a + 1)).faeden (fs j)).spur :=
    Classical.byContradiction hQa1
  have hsa := hl.2 a (by omega)
  have hfa : fs a = fs j := by
    apply Classical.byContradiction
    intro hne
    exact hQa (by rw [← ga_fremd hsa (fs j) (Ne.symm hne)]; exact hQa1')
  rw [hfa] at hsa
  have hnimmt : ∃ h, Ereignis.nimmt L h ∈ ereignisse (ms a) (ms (a + 1)) (fs j) := by
    obtain ⟨σ, M'', hs, hfa', _, _, he⟩ := schrittGA_zerlegen hsa
    have hQa1'' : L ∈ offen (M''.faeden (fs j)).spur := by rw [← hfa']; exact hQa1'
    rw [he]
    rcases schritt_delta hO hs with ⟨_, _, _, _, _, hoff⟩ | ⟨⟨X, eX, _, _⟩, _⟩
    · have hoff' : offen (M''.faeden (fs j)).spur = offen ((ms a).faeden (fs j)).spur := hoff
      exact absurd (by rw [← hoff']; exact hQa1'') hQa
    · have eX' : (M''.faeden (fs j)).spur = X ++ ((ms a).faeden (fs j)).spur := eX
      rw [ereignisse_eq eX]
      exact nimmt_aus_offen L X _ hQa (by rw [← eX']; exact hQa1'')
  have hfrei : RufFreiG (ms a) (fs j) L := by
    intro u hu
    rw [← ga_fremd hsa u hu]
    exact hx (a + 1) (by omega) (fs j) u (Ne.symm hu) hQa1'
  exact ⟨r, a, by omega, by omega, ha2, hfr, hfa, ⟨hQr, hQr1, hgibt⟩,
    ⟨hQa, hQa1', hfrei, hnimmt⟩⟩

/-- **Race freedom on every GA run from the start, for every non-atomic carrier**: two accesses
    by different threads, one a write, are ordered through a guard lock. Guarded carriers: the
    guard is held at both accesses (`zugriff_haeltA` on the presented steps), then
    `sperre_ordnetGA`. Unguarded non-atomic carriers are write-separated over the call graphs
    (`hsep`), so no such pair exists. -/
end Rennen
end Gabbro.Grammatik
