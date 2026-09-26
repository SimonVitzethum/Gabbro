/-
  File:      Grammatik/Speichermodell/DRF.lean
  Subject:   THE DRF THEOREM FOR GABBRO (Opus agent B, 2026-09-26): on a program whose
             footprints the checker bounded, machine W (weak memory) takes only steps of
             machine G (sequential consistency) -- for EVERY carrier, `atomic` ones included,
             and for every choice of memory orders.

  THE STATEMENT. `schwach_ist_g`: from every state W reaches, every step of W is a step of G
  on G's own memory, and W's G-part moves exactly as G. So every run of W is a run of G
  (`g_aus_w`), and with `w_aus_g` (MaschineW.lean) the two machines reach the same G-states.
  The weakness of W is real (`sb_erlaubt`, `mp_rlx_erlaubt` in Sicht.lean: on other programs W
  shows non-SC outcomes); on these programs it never shows, because every read reads the
  newest message (`liest_neueste`).

  THE PREMISES are the ones the race leg of G already uses, no more: a good oracle (`GutO`),
  closed call graphs `K` containing the starts (`AbgK`), footprints bounded by locality or a
  lock (`FussS … (lokK P K)`, the checker's `fuss` component) and an exclusive start
  (`StartExklusiv`). In particular NOTHING about `atomic` carriers beyond what `fuss` demands
  of every carrier: a carrier that a thread reads is either thread-local (no other thread's
  call graph writes it: `GetrenntK`) or guarded by a lock (`Bewacht`) -- `atomic` or not.

  WHY IT HOLDS (the invariant `SichtInv`, every field a lower bound on a view):
  * `frei` -- an unguarded carrier a thread's graph reads: that thread's view has reached
    every message of it. Only that thread writes it (`frei_schreiber`), and a write sets the
    writer's view to its own, fresh, larger timestamp.
  * `halter`/`sperre` -- a guarded carrier: the view of the thread holding its lock, or the
    lock's own view when nobody holds it, has reached every message. Every access holds the
    lock (`zugriff_haelt`), a take joins the lock's view (`genommenVon`), a release joins the
    thread's view into the lock (`gegebenVon`).
  * `stimmt` -- at a carrier some thread reads, the newest message carries G's value.
  So at a read the thread's view is at the newest message, `Lesbar` admits only that one, and
  it carries G's value: the presented memory IS G's memory.

  WHAT IS NOT CLAIMED HERE: that the view machine is exactly RC11 (it is the promise-free
  timestamp machine, which over-approximates RC11 for the orders the emitter uses; see
  Sicht.lean) and that the C compiler implements C11 atomics and `pthread_mutex` as specified
  -- both named in the header of `Spec.lean`.
-/
import Grammatik.RennfreiOrte
import Grammatik.SperreFuss
import Grammatik.Speichermodell.MaschineW

namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-- Thread `t`'s call graph reads carrier `c` (some function of `K t` has it in its
    footprint). A static fact: it does not move with the run. -/
def LesbarK (P : Programm D) (K : Faden → D.Fn → Bool) (t : Faden) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ f, K t f = true ∧ c ∈ fussOrteG P f

/-! ## 1. Static facts from the footprint check -/

/-- An unguarded footprint carrier is thread-local: `FussS` leaves no other disjunct. -/
theorem getrennt_of_frei {P : Programm D} {S : SperrInv D} {K : Faden → D.Fn → Bool} {f : D.Fn}
    (hF : FussS P S (lokK P K) f) {c : D.Tab ⊕ D.Glob} (hc : c ∈ fussOrteG P f)
    (hB : ∀ L, ¬ Bewacht c L) : GetrenntK P K c := by
  have hsig : sigB f c = false := by
    cases h : sigB f c
    · rfl
    · obtain ⟨L, hL, _⟩ := List.any_eq_true.mp h
      exact absurd (waechterVon_mem.mp hL) (hB L)
  rcases List.mem_append.mp hc with hc | hc
  · rcases hF.1 c hc with h | ⟨L, hL, _⟩
    · rw [hsig, Bool.false_or] at h
      exact lokK_ok h
    · exact absurd hL (hB L)
  · have h := hF.2 c hc
    rw [hsig, Bool.false_or] at h
    exact lokK_ok h

/-! ## 2. The invariant -/

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} (sp : Speicher D)
  (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool)

/-- **The view invariant of W** on a checked program. -/
structure SichtInv (W : RufMaschineW D) : Prop where
  erreicht : RufErreichbarG P O passes (RufStartG P sp init) W.g
  frei : ∀ c t, (∀ L, ¬ Bewacht c L) → LesbarK P K t c → ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  halter : ∀ c L, Bewacht c L → ∀ t, L ∈ offen (W.g.faeden t).spur →
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  sperre : ∀ c L, Bewacht c L → (∀ t, L ∉ offen (W.g.faeden t).spur) →
    ∀ m ∈ W.hist c, m.ts ≤ W.lsicht L c
  stimmt : ∀ c, (∃ t, LesbarK P K t c) → ∀ m ∈ W.hist c, (∀ m' ∈ W.hist c, m'.ts ≤ m.ts) →
    TraegerGleich W.g.speicher m.wert c

theorem sichtInv_start :
    SichtInv (P := P) (O := O) (passes := passes) sp init K (RufStartW (RufStartG P sp init)) where
  erreicht := .start
  frei _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  halter _ _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  sperre _ _ _ _ m hm := by rw [List.mem_singleton.mp hm]; exact Nat.zero_le _
  stimmt c _ m hm _ := by rw [List.mem_singleton.mp hm]; exact traegerGleich_refl _ c

end Inv

/-! ## 3. One step -/

section Schritt

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} {sp : Speicher D}
  {init : Faden → Σ f : D.Fn, Env D (D.params f)} {K : Faden → D.Fn → Bool}

/-- Every step prepends its events to the acting thread's trace. -/
theorem spur_delta (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') :
    ∃ X, (M'.faeden u).spur = X ++ (M.faeden u).spur := by
  rcases schritt_delta hO hs with ⟨X, e, _⟩ | ⟨⟨X, e, _⟩, _⟩
  · exact ⟨X, e⟩
  · exact ⟨X, e⟩

/-- **What a read of a step tells, before the memory is known to be G's**: the reading
    thread's graph reads the carrier, and it holds every guard lock of it. Only the threads
    of the state are used, and they are those of a reachable machine of G. -/
theorem lies_fakten (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W : RufMaschineW D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) W.g) {σ : Speicher D}
    {M'' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O passes (mitSpeicher W.g σ) u M'')
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
    LesbarK P K u c ∧ ∀ L, Bewacht c L → L ∈ offen (W.g.faeden u).spur := by
  refine ⟨?_, fun L hB => ?_⟩
  · have hI := orteInvG_erreichbar sp init hr u _ List.mem_cons_self
    obtain ⟨X, hX, hok⟩ := schritt_ev hO hs hI
    have h := (zugriffe_ev hX hok hl).1 rfl
    have hInv := merkInvG_erreichbar (O := O) (pa := passes) sp init (fun t f => K t f = true)
      (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
    exact ⟨_, (hInv u _ List.mem_cons_self).1, istIn_iff.mp h⟩
  · have hI0 : SpurInv W.g := spurInv_erreichbar hO sp init hr
    have hI : SpurInv (mitSpeicher W.g σ) := hI0
    exact (ereignis_haelt hO hs (spurInv_schritt hO hs hI) hl hB).1

/-- **The read is the newest message, and it carries G's value.** -/
theorem liest_neueste (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W W' : RufMaschineW D}
    (hI : SichtInv (P := P) (O := O) (passes := passes) sp init K W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
    (∀ m ∈ W.hist c, m.ts ≤ (wahl c).ts) ∧ TraegerGleich W.g.speicher (wahl c).wert c := by
  obtain ⟨hK, hL⟩ := lies_fakten hO hvoll hAbg hWurzel hI.erreicht h.schritt hl
  obtain ⟨⟨hmem, hv⟩, _⟩ := h.lies c hl
  have hoben : ∀ m ∈ W.hist c, m.ts ≤ (wahl c).ts := by
    by_cases hB : ∃ L, Bewacht c L
    · obtain ⟨L, hB⟩ := hB
      exact fun m hm => Nat.le_trans (hI.halter c L hB u (hL L hB) m hm) hv
    · exact fun m hm => Nat.le_trans (hI.frei c u (fun L h => hB ⟨L, h⟩) hK m hm) hv
  exact ⟨hoben, hI.stimmt c ⟨u, hK⟩ (wahl c) hmem hoben⟩

/-- **The presented memory is G's memory.** -/
theorem praesentiert_g (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W W' : RufMaschineW D}
    (hI : SichtInv (P := P) (O := O) (passes := passes) sp init K W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    σ = W.g.speicher := by
  apply speicher_ext
  intro c
  by_cases hl : LiestG (mitSpeicher W.g σ) M'' u c
  · have h1 := (h.lies c hl).2
    have h2 := (liest_neueste hO hvoll hAbg hWurzel hI h hl).2
    exact traegerGleich_trans h1 (traegerGleich_symm h2)
  · exact h.ungelesen c hl

/-- A write of thread `u` to an unguarded carrier some thread `t` reads: `t` is `u`. -/
theorem frei_schreiber (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) (hFuss : ∀ f, FussS P S (lokK P K) f)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) {u : Faden}
    (hs : RufSchrittG P O passes M u M') {c : D.Tab ⊕ D.Glob} (hB : ∀ L, ¬ Bewacht c L)
    (hw : SchreibG M M' u c) {t : Faden} (ht : LesbarK P K t c) : t = u := by
  apply Classical.byContradiction
  intro htu
  obtain ⟨f, hf, hc⟩ := ht
  obtain ⟨g, hg, hgw⟩ := (zugriff_im_graph hO hvoll sp init K hAbg hWurzel hr hs c).2 hw
  have := getrennt_of_frei (hFuss f) hc hB t u htu f hf hc g hg
  rw [this] at hgw
  cases hgw

/-- A lock the step takes is in `genommenVon`. -/
theorem genommen_von (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') {L : D.Lock} (h0 : L ∉ offen (M.faeden u).spur)
    (h1 : L ∈ offen (M'.faeden u).spur) : L ∈ genommenVon M M' u := by
  obtain ⟨X, eX⟩ := spur_delta hO hs
  rw [eX] at h1
  obtain ⟨hh, hm⟩ := nimmt_aus_offen L X _ h0 h1
  unfold genommenVon
  rw [ereignisse_eq eX]
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- A lock the step releases is in `gegebenVon`. -/
theorem gegeben_von (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') {L : D.Lock} (h0 : L ∈ offen (M.faeden u).spur)
    (h1 : L ∉ offen (M'.faeden u).spur) : L ∈ gegebenVon M M' u := by
  obtain ⟨X, eX⟩ := spur_delta hO hs
  rw [eX] at h1
  have hm := gibt_aus_offen L X _ h0 h1
  unfold gegebenVon
  rw [ereignisse_eq eX]
  exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-- A write is an access. -/
theorem zugriff_of_schreib {M M' : RufMaschineG D} {u : Faden} {c : D.Tab ⊕ D.Glob}
    (h : SchreibG M M' u c) : ZugriffG M M' u c := by
  rcases h with h | h
  · exact Or.inl ⟨true, h⟩
  · exact Or.inr h

/-- **ONE STEP OF W ON A CHECKED PROGRAM IS A STEP OF G, and keeps the invariant.** -/
theorem schritt_sichtInv (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f) (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hI : SichtInv (P := P) (O := O) (passes := passes) sp init K W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu) :
    RufSchrittG P O passes W.g u W'.g ∧
      SichtInv (P := P) (O := O) (passes := passes) sp init K W' := by
  have hσ := praesentiert_g hO hvoll hAbg hWurzel hI h
  subst hσ
  obtain ⟨hs, hg⟩ := schrittW_g h
  have hMσ : mitSpeicher W.g W.g.speicher = W.g := mitSpeicher_selbst W.g
  have hr := hI.erreicht
  have hr' : RufErreichbarG P O passes (RufStartG P sp init) M'' := .schritt _ _ _ hr hs
  -- the fields of `h`, over `W.g` instead of the presented machine
  have hSchreibG : ∀ c, SchreibG (mitSpeicher W.g W.g.speicher) M'' u c ↔ SchreibG W.g M'' u c :=
    fun c => by rw [hMσ]
  have vorDef : vorSicht ord W u W.g.speicher M'' wahl =
      locksicht W.lsicht (genommenVon W.g M'' u)
        (lesesicht ord wahl (lesenVon W.g M'' u) (W.sicht u)) := by
    unfold vorSicht; rw [hMσ]
  have hge : ∀ x, W.sicht u x ≤ vorSicht ord W u W.g.speicher M'' wahl x :=
    fun x => vorSicht_ge W u _ M'' wahl x
  have hfaeden : W'.g.faeden = M''.faeden := h.faeden
  -- a written carrier: new message; the writer's view before the write bounds the old ones
  have hneu : ∀ c, SchreibG W.g M'' u c →
      (∀ m ∈ W.hist c, m.ts ≤ W.sicht u c) → ∀ m ∈ W.hist c, m.ts < neu c := by
    intro c hw hb m hm
    have hf := (h.frisch c ((hSchreibG c).mpr hw)).1
    exact Nat.lt_of_le_of_lt (Nat.le_trans (hb m hm) (hge c)) hf
  refine ⟨by rw [hg]; exact hs, ?_⟩
  refine ⟨by rw [hg]; exact hr', ?_, ?_, ?_, ?_⟩
  · -- `frei`
    intro c t hB ht m hm
    by_cases hw : SchreibG W.g M'' u c
    · have htu := frei_schreiber hO hvoll hAbg hWurzel hFuss hr hs hB hw ht
      subst htu
      rw [h.histS c ((hSchreibG c).mpr hw)] at hm
      rw [h.sichtS c ((hSchreibG c).mpr hw)]
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (hneu c hw (hI.frei c t hB ht) m hm)
    · rw [h.histU c (fun h' => hw ((hSchreibG c).mp h'))] at hm
      exact Nat.le_trans (hI.frei c t hB ht m hm) (sicht_waechst h t c)
  · -- `halter`
    intro c L hB t ht m hm
    rw [hg] at ht
    by_cases htu : t = u
    · subst htu
      by_cases hw : SchreibG W.g M'' t c
      · have hvor := (zugriff_haelt sp init hO hex hr hs hB (zugriff_of_schreib hw)).1
        rw [h.histS c ((hSchreibG c).mpr hw)] at hm
        rw [h.sichtS c ((hSchreibG c).mpr hw)]
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Nat.le_refl _
        · exact Nat.le_of_lt (hneu c hw (hI.halter c L hB t hvor) m hm)
      · have hw' : ¬ SchreibG (mitSpeicher W.g W.g.speicher) M'' t c :=
          fun h' => hw ((hSchreibG c).mp h')
        rw [h.histU c hw'] at hm
        by_cases hvor : L ∈ offen (W.g.faeden t).spur
        · exact Nat.le_trans (hI.halter c L hB t hvor m hm) (sicht_waechst h t c)
        · -- the step takes `L`: nobody held it before
          have hnimm := genommen_von hO hs hvor ht
          have hkein : ∀ t', L ∉ offen (W.g.faeden t').spur := by
            intro t' ht'
            by_cases e : t' = t
            · subst e; exact hvor ht'
            · have := exklusivG hO sp init hex hr' t t' (Ne.symm e) L ht
              rw [rufSchrittG_fremd hs t' e] at this
              exact this ht'
          have h1 := hI.sperre c L hB hkein m hm
          have h2 : W.lsicht L c ≤ vorSicht ord W t W.g.speicher M'' wahl c := by
            rw [vorDef]; exact locksicht_mem _ _ _ L hnimm c
          rw [h.sichtU c hw']
          exact Nat.le_trans h1 h2
    · have ht0 : L ∈ offen (W.g.faeden t).spur := by
        rw [← rufSchrittG_fremd hs t htu]; exact ht
      by_cases hw : SchreibG W.g M'' u c
      · have hu := (zugriff_haelt sp init hO hex hr hs hB (zugriff_of_schreib hw)).1
        exact absurd ht0 (exklusivG hO sp init hex hr u t (Ne.symm htu) L hu)
      · rw [h.histU c (fun h' => hw ((hSchreibG c).mp h'))] at hm
        rw [h.sichtF t htu]
        exact hI.halter c L hB t ht0 m hm
  · -- `sperre`
    intro c L hB hkein m hm
    rw [hg] at hkein
    by_cases hw : SchreibG W.g M'' u c
    · exact absurd (zugriff_haelt sp init hO hex hr hs hB (zugriff_of_schreib hw)).2 (hkein u)
    · rw [h.histU c (fun h' => hw ((hSchreibG c).mp h'))] at hm
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
            rw [rufSchrittG_fremd hs t e] at this
            exact this ht
        have hgib := gegeben_von hO hs hu (hkein u)
        have h1 := hI.halter c L hB u hu m hm
        rw [h.lsicht L, if_pos (by rw [hMσ]; exact hgib)]
        exact Nat.le_trans h1 (Nat.le_trans (sicht_waechst h u c) (Sicht.verein_rechts _ _ c))
  · -- `stimmt`
    intro c ⟨t, ht⟩ m hm hmax
    by_cases hw : SchreibG W.g M'' u c
    · have hw' := (hSchreibG c).mpr hw
      rw [h.histS c hw'] at hm hmax
      -- the writer's view reached every old message
      have hb : ∀ m ∈ W.hist c, m.ts ≤ W.sicht u c := by
        by_cases hB : ∃ L, Bewacht c L
        · obtain ⟨L, hB⟩ := hB
          exact hI.halter c L hB u (zugriff_haelt sp init hO hex hr hs hB (zugriff_of_schreib hw)).1
        · have hB' : ∀ L, ¬ Bewacht c L := fun L h' => hB ⟨L, h'⟩
          have htu := frei_schreiber hO hvoll hAbg hWurzel hFuss hr hs hB' hw ht
          subst htu
          exact hI.frei c t hB' ht
      rcases List.mem_cons.mp hm with rfl | hm
      · exact traegerGleich_refl _ c
      · have h1 := hneu c hw hb m hm
        have h2 := hmax _ List.mem_cons_self
        simp only [nachricht] at h2
        omega
    · have hw' : ¬ SchreibG (mitSpeicher W.g W.g.speicher) M'' u c :=
        fun h' => hw ((hSchreibG c).mp h')
      rw [h.histU c hw'] at hm hmax
      exact traegerGleich_trans (h.speicherU c hw') (hI.stimmt c ⟨t, ht⟩ m hm hmax)

/-- **The invariant on every machine W reaches.** -/
theorem sichtInv_erreichbar (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f) (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    SichtInv (P := P) (O := O) (passes := passes) sp init K W := by
  induction hr with
  | start => exact sichtInv_start sp init K
  | schritt W W' u _ hs ih =>
      obtain ⟨σ, M'', wahl, neu, h⟩ := hs
      exact (schritt_sichtInv hO hvoll hAbg hWurzel hFuss hex ih h).2

/-- **THE DRF THEOREM, one step**: from every state W reaches on a checked program, every
    step of W is a step of G from W's G-part to the successor's G-part. -/
theorem schwach_ist_g (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f) (hex : StartExklusiv init) {W W' : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) {u : Faden}
    (hs : RufSchrittW P O passes ord W u W') : RufSchrittG P O passes W.g u W'.g := by
  obtain ⟨σ, M'', wahl, neu, h⟩ := hs
  exact (schritt_sichtInv hO hvoll hAbg hWurzel hFuss hex
    (sichtInv_erreichbar hO hvoll hAbg hWurzel hFuss hex hr) h).1

/-- **THE DRF THEOREM, runs**: every machine W reaches on a checked program has a G-part
    that G reaches. -/
theorem g_aus_w (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f) (hex : StartExklusiv init) {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W) :
    RufErreichbarG P O passes (RufStartG P sp init) W.g :=
  (sichtInv_erreichbar hO hvoll hAbg hWurzel hFuss hex hr).erreicht

end Schritt

#print axioms Gabbro.Grammatik.getrennt_of_frei
#print axioms Gabbro.Grammatik.liest_neueste
#print axioms Gabbro.Grammatik.praesentiert_g
#print axioms Gabbro.Grammatik.schritt_sichtInv
#print axioms Gabbro.Grammatik.sichtInv_erreichbar
#print axioms Gabbro.Grammatik.schwach_ist_g
#print axioms Gabbro.Grammatik.g_aus_w

end Gabbro.Grammatik
