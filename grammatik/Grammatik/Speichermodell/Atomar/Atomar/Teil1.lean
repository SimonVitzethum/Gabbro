module

public import Grammatik.Speichermodell.Maschine.DRF

@[expose] public section



namespace Gabbro.Grammatik

open Speichermodell

variable {D : Deklaration}

/-! ## 1. The footprint check with the atomic exemption -/

/-- **The footprint property with atomics exempt**: `FussS` (every footprint carrier guarded
    by a signature lock, local, or protected by a lock invariant; device carriers guarded or
    local) with ONE more disjunct for the footprint carriers: the carrier is an `atomic`
    global. Plain carriers keep every demand of `FussS`. -/
def FussSA (P : Programm D) (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (f : D.Fn) : Prop :=
  (∀ c ∈ fussOrte P f, (sigB f c || lok c) = true ∨ (∃ L, Bewacht c L ∧ c ∈ S.orte L) ∨
    AtomarAusgenommen c) ∧
  (∀ c ∈ (P.rumpf f).regs.flatMap D.rtraeger, (sigB f c || lok c) = true)

/-- **Embedding**: the old footprint property gives the new one (every program the old check
    admits, the new one admits). -/
theorem fussSA_of_fussS {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
    {f : D.Fn} (h : FussS P S lok f) : FussSA P S lok f :=
  ⟨fun c hc => (h.1 c hc).elim Or.inl (fun h => Or.inr (Or.inl h)), h.2⟩

/-- On a non-atomic carrier the two properties say the same. -/
theorem fussSA_plain {P : Programm D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {f : D.Fn}
    (h : FussSA P S lok f) {c : D.Tab ⊕ D.Glob} (hc : c ∈ fussOrte P f)
    (hA : ¬ AtomarAusgenommen c) : (sigB f c || lok c) = true ∨ ∃ L, Bewacht c L ∧ c ∈ S.orte L :=
  (h.1 c hc).elim Or.inl (fun h => h.elim Or.inr (fun h' => absurd h' hA))

/-- **An unguarded, NON-atomic footprint carrier is thread-local** (`getrennt_of_frei` with
    the atomic disjunct excluded). -/
theorem getrennt_of_freiA {P : Programm D} {S : SperrInv D} {K : Faden → D.Fn → Bool} {f : D.Fn}
    (hF : FussSA P S (lokK P K) f) {c : D.Tab ⊕ D.Glob} (hc : c ∈ fussOrteG P f)
    (hB : ∀ L, ¬ Bewacht c L) (hA : ¬ AtomarAusgenommen c) : GetrenntK P K c := by
  have hsig : sigB f c = false := by
    cases h : sigB f c
    · rfl
    · obtain ⟨L, hL, _⟩ := List.any_eq_true.mp h
      exact absurd (waechterVon_mem.mp hL) (hB L)
  rcases List.mem_append.mp hc with hc | hc
  · rcases fussSA_plain hF hc hA with h | ⟨L, hL, _⟩
    · rw [hsig, Bool.false_or] at h
      exact lokK_ok h
    · exact absurd hL (hB L)
  · have h := hF.2 c hc
    rw [hsig, Bool.false_or] at h
    exact lokK_ok h

/-! ## 2. Machine GA: G whose atomic reads may be answered by any value -/

/-- **One step of GA.** Thread `u` takes a step of G on a PRESENTED memory `σ` that agrees with
    G's memory at every carrier that is not an `atomic` global -- at an atomic carrier `σ` is
    arbitrary, the havoc at an atomic read. As in W (`SchrittW.speicherS`/`speicherU`), the
    successor's memory takes the written carriers from the step and keeps every other one. -/
def RufSchrittGA (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D)
    (u : Faden) (M' : RufMaschineG D) : Prop :=
  ∃ (σ : Speicher D) (M'' : RufMaschineG D),
    RufSchrittG P O passes (mitSpeicher M σ) u M'' ∧
    (∀ c, ¬ AtomarAusgenommen c → TraegerGleich σ M.speicher c) ∧
    (∀ c, SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M''.speicher c) ∧
    (∀ c, ¬ SchreibG (mitSpeicher M σ) M'' u c → TraegerGleich M'.speicher M.speicher c) ∧
    M'.faeden = M''.faeden ∧ M'.lauf = M''.lauf ∧ M'.start = M''.start

/-- **The machines GA reaches** from `M0`. -/
inductive RufErreichbarGA (P : Programm D) (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D) :
    RufMaschineG D → Prop where
  | start : RufErreichbarGA P O passes M0 M0
  | schritt (M M' : RufMaschineG D) (u : Faden) :
      RufErreichbarGA P O passes M0 M → RufSchrittGA P O passes M u M' →
        RufErreichbarGA P O passes M0 M'

section GA

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **Every G step is a GA step** (present G's own memory). -/
theorem schrittGA_of_g {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O passes M u M') :
    RufSchrittGA P O passes M u M' := by
  refine ⟨M.speicher, M', by rw [mitSpeicher_selbst]; exact hs, fun c _ => traegerGleich_refl _ c,
    fun c _ => traegerGleich_refl _ c, fun c hw => ?_, rfl, rfl, rfl⟩
  have h := traegerGleich_of_nicht_schreib hw
  rw [mitSpeicher_selbst] at h
  exact h

/-- **Every G run is a GA run**: GA adds behaviour, it removes none. -/
theorem ga_aus_g {M0 M : RufMaschineG D} (hr : RufErreichbarG P O passes M0 M) :
    RufErreichbarGA P O passes M0 M := by
  induction hr with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ _ ih (schrittGA_of_g hs)

/-- **A property of the threads alone holds on every GA run** once it holds at the start and
    every G step keeps it: GA changes G's steps only in the memory they are presented and
    the memory they leave, never in the threads. -/
theorem gaInv {I : RufMaschineG D → Prop}
    (hfa : ∀ M M' : RufMaschineG D, M.faeden = M'.faeden → I M → I M')
    {M0 : RufMaschineG D} (h0 : I M0)
    (hs : ∀ (M M' : RufMaschineG D) (u : Faden), I M → RufSchrittG P O passes M u M' → I M')
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes M0 M) : I M := by
  induction hr with
  | start => exact h0
  | schritt M M' u _ hst ih =>
      obtain ⟨σ, M'', hs', _, _, _, hfa', _, _⟩ := hst
      have h1 : I (mitSpeicher M σ) := hfa M _ rfl ih
      exact hfa _ _ hfa'.symm (hs _ _ _ h1 hs')

/-- The trace invariant (every trace consistent, every access event good) on every GA run. -/
theorem gaInv_spur (hO : GutO O) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) : SpurInv M :=
  gaInv (I := SpurInv) (fun M M' e h t => by rw [← e]; exact h t) (spurInv_start P sp init)
    (fun _ _ _ h hs => spurInv_schritt hO hs h) hr

/-- The frame read bound on every GA run. -/
theorem gaInv_orte (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, OrteInvG P (M.faeden t) := by
  refine gaInv (I := fun M => ∀ t, OrteInvG P (M.faeden t)) (fun M M' e h t => by rw [← e]; exact h t)
    (orteInvG_erreichbar (O := O) (pa := passes) sp init .start) ?_ hr
  intro M M' u h hs t
  by_cases htu : t = u
  · subst htu; exact orteInvG_schritt hs (h t)
  · rw [rufSchrittG_fremd hs t htu]; exact h t

/-- The feature invariant (frames stay in the thread's call graph) on every GA run. -/
theorem gaInv_merk (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (Z : Faden → D.Fn → Prop) (A : Faden → D.Fn → Merkmal D)
    (hA : ∀ t, MerkAbg P (Z t) (A t)) (hZ : ∀ t, Z t (init t).1) {M : RufMaschineG D}
    (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) :
    ∀ t, MerkInvG (Z t) (A t) (M.faeden t) := by
  refine gaInv (I := fun M => ∀ t, MerkInvG (Z t) (A t) (M.faeden t))
    (fun M M' e h t => by rw [← e]; exact h t)
    (merkInvG_erreichbar (O := O) (pa := passes) sp init Z A hA hZ .start) ?_ hr
  intro M M' u h hs t
  by_cases htu : t = u
  · subst htu; exact merkInvG_schritt (hA t) hs (h t)
  · rw [rufSchrittG_fremd hs t htu]; exact h t

/-- Lock exclusivity, as a property of a machine. -/
def Exklusiv (M : RufMaschineG D) : Prop :=
  ∀ (f g : Faden), f ≠ g → ∀ L : D.Lock, L ∈ offen (M.faeden f).spur → L ∉ offen (M.faeden g).spur

/-- **Lock exclusivity on every GA run** (the step argument of `exklusivG`, over GA). -/
theorem gaInv_exklusiv (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) : Exklusiv M := by
  refine gaInv (I := Exklusiv) (fun M M' e h => by unfold Exklusiv; rw [← e]; exact h)
    (exklusivG (O := O) (passes := passes) hO sp init hex .start) ?_ hr
  intro M M' f0 ih hs f g hfg L hLf hLg
  have hfremd : ∀ t, t ≠ f0 → M'.faeden t = M.faeden t := fun t ht => rufSchrittG_fremd hs t ht
  by_cases hf : f = f0
  · subst hf
    have hg : g ≠ f := fun e => hfg e.symm
    rw [hfremd g hg] at hLg
    rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', _, e⟩
    · rw [e] at hLf; exact ih f g hfg L hLf hLg
    · rw [e] at hLf
      rcases List.mem_cons.mp hLf with rfl | hLf
      · exact hfrei g hg hLg
      · exact ih f g hfg L hLf hLg
    · rw [e] at hLf; exact ih f g hfg L (List.mem_of_mem_erase hLf) hLg
  · rw [hfremd f hf] at hLf
    by_cases hg : g = f0
    · subst hg
      rcases offen_schrittG hO hs with e | ⟨L', hfrei, e⟩ | ⟨L', _, e⟩
      · rw [e] at hLg; exact ih f g hfg L hLf hLg
      · rw [e] at hLg
        rcases List.mem_cons.mp hLg with rfl | hLg
        · exact hfrei f hf hLf
        · exact ih f g hfg L hLf hLg
      · rw [e] at hLg; exact ih f g hfg L hLf (List.mem_of_mem_erase hLg)
    · rw [hfremd g hg] at hLg; exact ih f g hfg L hLf hLg

/-- **Every access holds the guard**, from the trace invariant after the step alone (the
    reachability `zugriff_haelt` asks for is used there only for this invariant). -/
theorem zugriff_haeltA (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') (hI' : SpurInv M') {c : D.Tab ⊕ D.Glob} {L : D.Lock}
    (hB : Bewacht c L) (hz : ZugriffG M M' f c) :
    L ∈ offen (M.faeden f).spur ∧ L ∈ offen (M'.faeden f).spur := by
  rcases hz with ⟨w, hw⟩ | hm
  · obtain ⟨h1, h2⟩ := ereignis_haelt hO hs hI' hw hB
    exact ⟨h1, by rw [h2]; exact h1⟩
  · have h1 : L ∈ offen (M.faeden f).spur := by
      apply Classical.byContradiction
      intro hn
      exact hm (schritt_traeger hO hs c (Or.inl ⟨L, hB, hn⟩))
    rcases schritt_delta hO hs with ⟨_, _, _, _, _, hoff⟩ | ⟨_, hsp⟩
    · exact ⟨h1, by rw [hoff]; exact h1⟩
    · exact absurd (by rw [hsp]; exact traegerGleich_refl _ c) hm

/-- **A step's accesses, bounded by the acting function**, from the frame read bound alone. -/
theorem schritt_zugriffeA (hO : GutO O) {M M' : RufMaschineG D} {f : Faden}
    (hI : OrteInvG P (M.faeden f)) (hs : RufSchrittG P O passes M f M') (c : D.Tab ⊕ D.Glob) :
    (ZugriffG M M' f c → c ∈ fussOrteG P (M.faeden f).kopf.f ∨
      TraegerSchreibt (M.faeden f).kopf.f c = true) ∧
    (SchreibG M M' f c → TraegerSchreibt (M.faeden f).kopf.f c = true) := by
  obtain ⟨X, hX, hok⟩ := schritt_ev hO hs (hI _ List.mem_cons_self)
  have hmem : ¬ TraegerGleich M'.speicher M.speicher c →
      TraegerSchreibt (M.faeden f).kopf.f c = true := by
    intro hn
    cases hb : TraegerSchreibt (M.faeden f).kopf.f c
    · exact absurd (schritt_traeger hO hs c (Or.inr hb)) hn
    · rfl
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rcases hz with ⟨w, hw⟩ | hm
    · have h := zugriffe_ev hX hok hw
      cases w
      · exact Or.inl (istIn_iff.mp (h.1 rfl))
      · exact Or.inr (h.2 rfl)
    · exact Or.inr (hmem hm)
  · rcases hz with hw | hm
    · exact (zugriffe_ev hX hok hw).2 rfl
    · exact hmem hm

end GA

/-! ## 3. The view invariant with racing atomics -/

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat} {ord : D.Glob → Ordnung}
  {S : SperrInv D} {fs : List D.Fn} (sp : Speicher D)
  (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool)

/-- **The view invariant of W with racing atomics.** As `SichtInv` (DRF.lean), with two
    changes: G's part is reached by GA (not by G), and the fields `frei` and `stimmt` speak
    about NON-atomic carriers only -- at an atomic carrier W's reads are free. -/
structure SichtInvA (W : RufMaschineW D) : Prop where
  erreicht : RufErreichbarGA P O passes (RufStartG P sp init) W.g
  frei : ∀ c t, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → LesbarK P K t c →
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  halter : ∀ c L, Bewacht c L → ∀ t, L ∈ offen (W.g.faeden t).spur →
    ∀ m ∈ W.hist c, m.ts ≤ W.sicht t c
  sperre : ∀ c L, Bewacht c L → (∀ t, L ∉ offen (W.g.faeden t).spur) →
    ∀ m ∈ W.hist c, m.ts ≤ W.lsicht L c
  stimmt : ∀ c, ¬ AtomarAusgenommen c → (∃ t, LesbarK P K t c) → ∀ m ∈ W.hist c,
    (∀ m' ∈ W.hist c, m'.ts ≤ m.ts) → TraegerGleich W.g.speicher m.wert c

theorem sichtInvA_start :
    SichtInvA (P := P) (O := O) (passes := passes) sp init K (RufStartW (RufStartG P sp init)) where
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

/-- **What a read tells, on a GA-reached machine**: the reader's graph reads the carrier, and
    it holds every guard lock of it (`lies_fakten` over GA). -/
theorem lies_faktenA (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {M : RufMaschineG D}
    (hr : RufErreichbarGA P O passes (RufStartG P sp init) M) {σ : Speicher D}
    {M'' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O passes (mitSpeicher M σ) u M'')
    {c : D.Tab ⊕ D.Glob} (hl : LiestG (mitSpeicher M σ) M'' u c) :
    LesbarK P K u c ∧ ∀ L, Bewacht c L → L ∈ offen (M.faeden u).spur := by
  refine ⟨?_, fun L hB => ?_⟩
  · have hI : OrteInvG P ((mitSpeicher M σ).faeden u) := gaInv_orte sp init hr u
    obtain ⟨X, hX, hok⟩ := schritt_ev hO hs (hI _ List.mem_cons_self)
    have h := (zugriffe_ev hX hok hl).1 rfl
    have hInv := gaInv_merk (P := P) (O := O) (passes := passes) sp init (fun t f => K t f = true)
      (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
    exact ⟨_, (hInv u _ List.mem_cons_self).1, istIn_iff.mp h⟩
  · have hI0 : SpurInv M := gaInv_spur hO sp init hr
    have hI : SpurInv (mitSpeicher M σ) := hI0
    exact (ereignis_haelt hO hs (spurInv_schritt hO hs hI) hl hB).1

/-- **A read of a NON-atomic carrier is the newest message, and it carries G's value.** -/
theorem liest_neuesteA (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W W' : RufMaschineW D}
    (hI : SichtInvA (P := P) (O := O) (passes := passes) sp init K W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    {c : D.Tab ⊕ D.Glob} (hA : ¬ AtomarAusgenommen c) (hl : LiestG (mitSpeicher W.g σ) M'' u c) :
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
theorem praesentiert_gA (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) {W W' : RufMaschineW D}
    (hI : SichtInvA (P := P) (O := O) (passes := passes) sp init K W) {u : Faden}
    {σ : Speicher D} {M'' : RufMaschineG D} {wahl : D.Tab ⊕ D.Glob → NachrichtW D}
    {neu : D.Tab ⊕ D.Glob → Nat} (h : SchrittW P O passes ord W u W' σ M'' wahl neu)
    (c : D.Tab ⊕ D.Glob) (hA : ¬ AtomarAusgenommen c) : TraegerGleich σ W.g.speicher c := by
  by_cases hl : LiestG (mitSpeicher W.g σ) M'' u c
  · have h1 := (h.lies c hl).2
    have h2 := (liest_neuesteA hO hvoll hAbg hWurzel hI h hA hl).2
    exact traegerGleich_trans h1 (traegerGleich_symm h2)
  · exact h.ungelesen c hl

/-- A write of thread `u` to an unguarded NON-atomic carrier some thread `t` reads: `t` is
    `u` (over a GA-reached machine). -/
theorem frei_schreiberA (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) (hFuss : ∀ f, FussSA P S (lokK P K) f)
    {M : RufMaschineG D} (hr : RufErreichbarGA P O passes (RufStartG P sp init) M)
    {σ : Speicher D} {M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes (mitSpeicher M σ) u M') {c : D.Tab ⊕ D.Glob}
    (hB : ∀ L, ¬ Bewacht c L) (hA : ¬ AtomarAusgenommen c)
    (hw : SchreibG (mitSpeicher M σ) M' u c) {t : Faden} (ht : LesbarK P K t c) : t = u := by
  apply Classical.byContradiction
  intro htu
  obtain ⟨f, hf, hc⟩ := ht
  have hOrte : OrteInvG P ((mitSpeicher M σ).faeden u) := gaInv_orte sp init hr u
  have hInv := gaInv_merk (P := P) (O := O) (passes := passes) sp init (fun t f => K t f = true)
    (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
  have hK : K u ((mitSpeicher M σ).faeden u).kopf.f = true := (hInv u _ List.mem_cons_self).1
  have hgw := (schritt_zugriffeA hO hOrte hs c).2 hw
  have := getrennt_of_freiA (hFuss f) hc hB hA t u htu f hf hc _ hK
  rw [this] at hgw
  cases hgw

/-- **ONE STEP OF W ON A PROGRAM WITH RACING ATOMICS IS A STEP OF GA, and keeps the
    invariant.** -/
end Schritt
end Gabbro.Grammatik
