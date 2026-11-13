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
module
public import Grammatik.Speichermodell.Atomar.AtomarAkteur
public import Grammatik.Speichermodell.Atomar.Atomar
@[expose] public section


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
    {lok : D.Tab ⊕ D.Glob → Bool} (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O passes M u M')
    (hH : ∀ t, HaeltInvG (M.faeden t)) (hex : Exklusiv M)
    (hMk : ∀ t, ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, K t F.f = true)
    (t : Faden) (htu : t ≠ u) (F : RufRahmenG D) (hF : F ∈ (M.faeden t).kopf :: (M.faeden t).stapel)
    (c : D.Tab ⊕ D.Glob) (hc : c ∈ stabilS P S lok F.f F.rest.2.2.1) :
    TraegerGleich M'.speicher M.speicher c := by
  rcases stabilS_mem.mp hc with hc | ⟨L, hL, hcL⟩
  · have hsf := (sicher_mem.mp hc).2
    simp only [Bool.or_eq_true] at hsf
    rcases hsf with hsig | hfrei
    · obtain ⟨L, hB, hLh⟩ := sigB_ok hsig
      have hLt := (hH t).signatur F hF L hLh
      exact schritt_traeger hO hs c (Or.inl ⟨L, hB, hex t u htu L hLt⟩)
    · exact schritt_traeger hO hs c (Or.inr (hlokK c hfrei t u htu F.f (hMk t F hF)
        (sicher_mem.mp hc).1 _ (hMk u _ List.mem_cons_self)))
  · have hLt := (hH t).alle F hF L hL
    exact schritt_traeger hO hs c (Or.inl ⟨L, hS.1 L c hcL, hex t u htu L hLt⟩)

end Rely

/-! ## 3. The oracle rely of the replay over GX (C08 R3b) -/

section Antwort

/-- **The answer facts at every reachable question.** At every machine GX reaches, on
    every memory the weak memory may present, the current question of each thread is
    answered within `Q`. This is what the replay records at a foreign step. -/
def AntwortQLauf (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) : Prop :=
  ∀ M : RufMaschineG D, RufErreichbarGX P O passes Tg M0 M → ∀ σ : Speicher D,
    (∀ c, ¬ Tg c → TraegerGleich σ M.speicher c) → ∀ t : Faden, AntwortQ Q O (mitSpeicher M σ) t

/-- **The oracle rely of the replay**: the oracle is in the body duties' class (so the
    replay oracle is too, `orakelAus_vertragOP`), and every question the run asks is
    answered within `Q`. -/
def RelyQ (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (Tg : D.Tab ⊕ D.Glob → Prop) (M0 : RufMaschineG D) : Prop :=
  AxVertragOP (PreQ P) Q O ∧ AntwortQLauf P O passes Q Tg M0

/-- The full summary premise gives the rely on every run. -/
theorem antwortQLauf_of_O {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M0 : RufMaschineG D} (h : AxVertragO Q O) :
    AntwortQLauf P O passes Q Tg M0 := by
  intro M _ σ _ t a σ1 ρ _ v hv
  exact h a (σ1.fragt (.inl a)) ρ v hv

theorem relyQ_of_O {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}
    {Tg : D.Tab ⊕ D.Glob → Prop} {M0 : RufMaschineG D} (h : AxVertragO Q O) :
    RelyQ P O passes Q Tg M0 :=
  ⟨axVertragOP_of_O _ h, antwortQLauf_of_O h⟩

end Antwort

end Gabbro.Grammatik
