/-
  File:      Grammatik/Speichermodell/Atomar.lean
  Subject:   UNGUARDED ATOMIC COMMUNICATION OVER MACHINE W -- the MEMORY half of OFFEN O25
             (Opus lane O25, 2026-09-26). Standalone: `Zielsatz/Spec.lean` does not import
             this file, and no premise or leg of the goal theorem changes here.

  THE QUESTION. The DRF theorem of `DRF.lean` (`schwach_ist_g`) holds BY EXCLUSION: the
  checker's footprint component (`FussS`) demands that every carrier a thread's graph reads is
  thread-local or lock-guarded -- `atomic` carriers included. So a flag, a spin, a counter read
  by a monitor thread and the fold of a per-core accumulator are refused, and W's non-SC
  outcomes never occur on an accepted program. What happens when the refusal is lifted for
  ATOMIC carriers only?

  THE ANSWER PROVED HERE (`schwach_ist_gA`, `ga_aus_w`): on every program whose footprints
  satisfy `FussSA` -- `FussS` with ONE more disjunct, "the carrier is an `atomic` global"
  (`AtomarAusgenommen`) -- machine W still reads the NEWEST message at every NON-atomic
  carrier, so a W step is a step of G on a memory that agrees with G's at every plain carrier
  and differs, if at all, at atomic carriers only. Those steps form MACHINE GA
  (`RufSchrittGA`): G whose ATOMIC reads may be answered by any value -- the "havoc at an
  atomic read" that OFFEN O25 names as the rely. So:
  * plain carriers stay SEQUENTIALLY CONSISTENT (the DRF theorem, now with racing atomics);
  * atomic reads are answered per W: coherent (`schrittW_kohaerent`) and with release/acquire
    views (`schrittW_erwerb`, and here `schrittW_freigabe`, `hb_uebergabe`: a release write
    carries the writer's view, an acquire read of it hands that view on, and every later read
    of the reader returns a message at or above it -- the happens-before hand-off of a
    `publishes`/`awaits` pair);
  * the thread-local invariants of G hold on every GA run -- the trace invariant `SpurInv`
    (memory safety of the trace), the frame read bound `OrteInvG`, the feature invariant
    `MerkInvG` and lock EXCLUSIVITY (`gaInv_*`): none of them reads memory.
  Every G run is a GA run (`ga_aus_g`) and `FussS` implies `FussSA` (`fussSA_of_fussS`), so
  every program `schwach_ist_g` covers is covered here, with the stronger conclusion there.

  WHAT IS NOT HERE (and why O25 stays open, narrowed -- `messung/OPUS-O25-ATOMICS.md`):
  the CONTRACT legs of `Ziel` (`VertragAmOrtG`, `SperrInvG`, `InvAmOrtG`, ...) come from the
  REPLAY of the user's sequential proof (`execEndH`, `KoerperGutS`) into G. On a GA run a
  thread reads an atomic value its sequential world does not have; covering that needs the
  sequential semantics to answer a shared atomic read with ANY value of its type (a havoc at
  the read, beside the one `Umwelt` makes at a lock take) and every residue lemma of the
  replay (`ZielOrt*`, `Sperre*`, some 30 000 lines) to carry it. This file gives the replay
  its MEMORY premise -- what a GA step presents -- and nothing more.
-/
import Grammatik.Speichermodell.DRF

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
theorem rennfreiGA {fs : List D.Fn} (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hex : StartExklusiv init) (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true)
    (hsep : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c → SchreibGetrenntK P K c)
    (ms : Nat → RufMaschineG D) (ts : Nat → Faden) (n : Nat)
    (hl : LaufGA P O passes (RufStartG P sp init) ms ts n)
    (i j : Nat) (c : D.Tab ⊕ D.Glob) (hij : i < j) (hjn : j < n) (hfg : ts i ≠ ts j)
    (hzi : ZugriffG (ms i) (ms (i + 1)) (ts i) c) (hzj : ZugriffG (ms j) (ms (j + 1)) (ts j) c)
    (hw : SchreibG (ms i) (ms (i + 1)) (ts i) c ∨ SchreibG (ms j) (ms (j + 1)) (ts j) c)
    (hA : ¬ AtomarAusgenommen c) : ∃ L, Bewacht c L ∧ GeordnetG ms ts L i j := by
  -- what one step of the run tells about an access
  have schritt : ∀ k, k < n → ∀ (Lk : D.Lock), Bewacht c Lk →
      ZugriffG (ms k) (ms (k + 1)) (ts k) c →
      Lk ∈ offen ((ms k).faeden (ts k)).spur ∧ Lk ∈ offen ((ms (k + 1)).faeden (ts k)).spur := by
    intro k hk Lk hB hz
    obtain ⟨σ, M'', hs, hfa, hZ, _, _⟩ := schrittGA_zerlegen (hl.2 k hk)
    have hr' := laufGA_erreichbar hl (k + 1) (by omega)
    have hSp' : SpurInv M'' := by
      have := gaInv_spur hO sp init hr'
      intro t; rw [← hfa]; exact this t
    have := zugriff_haeltA hO hs hSp' hB (hZ c hz)
    exact ⟨this.1, by rw [hfa]; exact this.2⟩
  have graph : ∀ k, k < n →
      (ZugriffG (ms k) (ms (k + 1)) (ts k) c → ∃ g, K (ts k) g = true ∧
        (c ∈ fussOrteG P g ∨ TraegerSchreibt g c = true)) ∧
      (SchreibG (ms k) (ms (k + 1)) (ts k) c → ∃ g, K (ts k) g = true ∧
        TraegerSchreibt g c = true) := by
    intro k hk
    obtain ⟨σ, M'', hs, _, hZ, hS, _⟩ := schrittGA_zerlegen (hl.2 k hk)
    have hr := laufGA_erreichbar hl k (by omega)
    have hOrte : OrteInvG P ((mitSpeicher (ms k) σ).faeden (ts k)) := gaInv_orte sp init hr (ts k)
    have hInv := gaInv_merk (P := P) (O := O) (passes := passes) sp init (fun t f => K t f = true)
      (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
    have hK : K (ts k) ((mitSpeicher (ms k) σ).faeden (ts k)).kopf.f = true :=
      (hInv (ts k) _ List.mem_cons_self).1
    have hb := schritt_zugriffeA hO hOrte hs c
    exact ⟨fun hz => ⟨_, hK, hb.1 (hZ c hz)⟩, fun hz => ⟨_, hK, hb.2 (hS c hz)⟩⟩
  by_cases hB : ∃ L, Bewacht c L
  · obtain ⟨L, hL⟩ := hB
    have hi := schritt i (by omega) L hL hzi
    have hj := schritt j hjn L hL hzj
    exact ⟨L, hL, sperre_ordnetGA sp init hO hex hl i j hij hjn hfg L hi.2 hj.1⟩
  · have hsc := hsep c (fun L h => hB ⟨L, h⟩) hA
    have gi := graph i (by omega)
    have gj := graph j hjn
    exfalso
    rcases hw with hw | hw
    · obtain ⟨g, hg, hgw⟩ := gi.2 hw
      obtain ⟨h, hh, hhz⟩ := gj.1 hzj
      obtain ⟨h1, h2⟩ := hsc _ _ hfg g hg hgw h hh
      rcases hhz with hhz | hhz
      · exact h2 hhz
      · rw [h1] at hhz; cases hhz
    · obtain ⟨g, hg, hgw⟩ := gj.2 hw
      obtain ⟨h, hh, hhz⟩ := gi.1 hzi
      obtain ⟨h1, h2⟩ := hsc _ _ (Ne.symm hfg) g hg hgw h hh
      rcases hhz with hhz | hhz
      · exact h2 hhz
      · rw [h1] at hhz; cases hhz

end Rennen

#print axioms Gabbro.Grammatik.fussSA_of_fussS
#print axioms Gabbro.Grammatik.ga_aus_g
#print axioms Gabbro.Grammatik.gaInv_exklusiv
#print axioms Gabbro.Grammatik.schritt_sichtInvA
#print axioms Gabbro.Grammatik.schwach_ist_gA
#print axioms Gabbro.Grammatik.plain_liest_neueste
#print axioms Gabbro.Grammatik.ga_aus_w
#print axioms Gabbro.Grammatik.w_spur_exklusiv
#print axioms Gabbro.Grammatik.schwach_ist_gA_vor
#print axioms Gabbro.Grammatik.schrittW_freigabe
#print axioms Gabbro.Grammatik.hb_uebergabe
#print axioms Gabbro.Grammatik.sperre_ordnetGA
#print axioms Gabbro.Grammatik.rennfreiGA

end Gabbro.Grammatik
