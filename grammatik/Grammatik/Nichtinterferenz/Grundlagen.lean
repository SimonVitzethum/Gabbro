/-
  File:      Grammatik/Nichtinterferenz/Grundlagen.lean
  Subject:   NONINTERFERENCE ON MACHINE G -- labels, low-equivalence, the
             observation of a domain, the unwinding conditions, and the
             metatheorem (`ni_aus_abwicklung`), plus its scheduler form
             (`ni_planer`, `ni_zeitplan`).

  Design: `dokumente/NICHTINTERFERENZ.md`.

  * A flow POLICY over a type of domains (`Politik`): a reflexive,
    transitive `darf a b` ("data of `a` may flow to `b`").
  * LABELS: every carrier (table or global) has a domain (`lab`), every
    thread has a domain (`fdom`).
  * The OBSERVATION of domain `B` (`beob`): the memory of every carrier
    whose label may flow to `B`, and the ghost-free state (`kern`: stack,
    head frame, trace -- without the entry worlds `s0` and the call log,
    which are proof bookkeeping that copies ALL of memory) of every thread
    whose domain may flow to `B`. The global run log `lauf` is not
    observed: it is instrumentation over every thread.
  * LOW-EQUIVALENCE `NiGleich`: the two machines agree on that observation
    (`beob_gleich_iff`: equal observations iff low-equivalent -- that is
    output consistency, a property of the definitions).
  * The UNWINDING CONDITIONS for one step of G (`AbwicklungG`): local
    respect (a step of a thread whose domain may not flow to `B` leaves
    the `B`-observation unchanged) and step consistency (a step of a
    `B`-visible thread from two low-equivalent machines ends in
    low-equivalent machines).
  * The METATHEOREM, generic over any pair of step relations
    (`ni_allgemein`) and instantiated for G (`ni_aus_abwicklung`): the
    unwinding conditions, two runs with the SAME schedule, starts that
    agree on the `B`-visible memory (the same `B`-inputs) -- the two runs
    show `B` the same observation at every index.
  * The SCHEDULER form (`ni_planer_allgemein`, `ni_planer`): the schedule
    is not a parameter but the output of a choice function
    `plan k M`; if the choice depends only on the `B`-observation, NI
    holds for the runs the scheduler produces. The fixed-timetable
    partition scheduler (seL4's configuration) is the instance
    `ni_zeitplan`.

  What is NOT stated here (see the design document): timing, the ORDER of
  steps chosen by a load-dependent scheduler (the scheduler theorem demands
  a low choice), enabledness (both runs must follow the schedule; that one
  run cannot -- a thread blocked on a lock -- is outside), declassification.
-/
import Grammatik.RennfreiVoll
import Grammatik.ZielOrtMehrfaden

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Policy and labels -/

/-- **A flow policy** over the domains `Dom`: `darf a b` -- data of domain
    `a` may flow to domain `b`. Reflexive and transitive (a preorder; a
    lattice is a special case, a two-point `{A, B}` with only the diagonal
    is the tenant case). -/
structure Politik (Dom : Type) where
  darf : Dom → Dom → Bool
  refl : ∀ d, darf d d = true
  trans : ∀ a b c, darf a b = true → darf b c = true → darf a c = true

/-- **Labels over a declaration**: the domain of every carrier and of every
    thread. A thread's domain is the domain of its entry root (the
    `domain D` annotation on a `concurrent`/`entry` root). -/
structure Etiketten (D : Deklaration) (Dom : Type) where
  lab : D.Tab ⊕ D.Glob → Dom
  fdom : Faden → Dom

section Beob

variable {Dom : Type} (π : Politik Dom) (E : Etiketten D Dom) (B : Dom)

/-- A carrier is `B`-visible: its label may flow to `B`. -/
def sichtbarC (c : D.Tab ⊕ D.Glob) : Bool := π.darf (E.lab c) B

/-- A thread is `B`-visible: its domain may flow to `B`. -/
def sichtbarF (t : Faden) : Bool := π.darf (E.fdom t) B

end Beob

/-! ## 2. The ghost-free thread state -/

/-- A frame without its entry world `s0` (bookkeeping for the call log). -/
structure KRahmen (D : Deklaration) where
  f : D.Fn
  rho : Env D (D.params f)
  rest : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
    Env D Γ × GRest D (vertragVon D f) l Γ Λ

/-- A thread state without the entry worlds and without the call log. -/
structure KFaden (D : Deklaration) where
  stapel : List (KRahmen D)
  kopf : KRahmen D
  spur : List (Ereignis D)

def RufRahmenG.kern (r : RufRahmenG D) : KRahmen D := ⟨r.f, r.rho, r.rest⟩

/-- **The ghost-free state of a thread**: its frames (function, parameters,
    residue) and its trace. -/
def RufFadenG.kern (z : RufFadenG D) : KFaden D :=
  ⟨z.stapel.map RufRahmenG.kern, z.kopf.kern, z.spur⟩

/-! ## 3. Low-equivalence and the observation -/

/-- Two memories agree on every carrier `S` admits. -/
def SpeicherGleich (S : D.Tab ⊕ D.Glob → Bool) (s s' : Speicher D) : Prop :=
  ∀ c, S c = true → TraegerGleich s s' c

theorem SpeicherGleich.refl (S : D.Tab ⊕ D.Glob → Bool) (s : Speicher D) : SpeicherGleich S s s :=
  fun c _ => traegerGleich_refl s c

theorem SpeicherGleich.symm {S : D.Tab ⊕ D.Glob → Bool} {s s' : Speicher D}
    (h : SpeicherGleich S s s') : SpeicherGleich S s' s := by
  intro c hc
  have := h c hc
  cases c with
  | inl t => exact this.symm
  | inr g => exact this.symm

theorem SpeicherGleich.trans {S : D.Tab ⊕ D.Glob → Bool} {s s' s'' : Speicher D}
    (h1 : SpeicherGleich S s s') (h2 : SpeicherGleich S s' s'') : SpeicherGleich S s s'' := by
  intro c hc
  have e1 := h1 c hc
  have e2 := h2 c hc
  cases c with
  | inl t => exact e1.trans e2
  | inr g => exact e1.trans e2

section Gleich

variable {Dom : Type} (π : Politik Dom) (E : Etiketten D Dom) (B : Dom)

/-- **Low-equivalence for observer `B`**: the `B`-visible memory agrees and
    every `B`-visible thread has the same ghost-free state. -/
def NiGleich (M N : RufMaschineG D) : Prop :=
  SpeicherGleich (sichtbarC π E B) M.speicher N.speicher ∧
  ∀ t, sichtbarF π E B t = true → (M.faeden t).kern = (N.faeden t).kern

theorem NiGleich.refl (M : RufMaschineG D) : NiGleich π E B M M :=
  ⟨SpeicherGleich.refl _ _, fun _ _ => rfl⟩

variable {π E B}

theorem NiGleich.symm {M N : RufMaschineG D} (h : NiGleich π E B M N) : NiGleich π E B N M :=
  ⟨h.1.symm, fun t ht => (h.2 t ht).symm⟩

theorem NiGleich.trans {M N K : RufMaschineG D} (h1 : NiGleich π E B M N)
    (h2 : NiGleich π E B N K) : NiGleich π E B M K :=
  ⟨h1.1.trans h2.1, fun t ht => (h1.2 t ht).trans (h2.2 t ht)⟩

variable (π E B)

/-- **What domain `B` observes of a machine**: the slots of every visible
    table, the value of every visible global, the ghost-free state of every
    visible thread; `none` everywhere else. -/
structure BeobB (D : Deklaration) where
  slots : ∀ t : D.Tab, Option (Int → ∀ f : D.Feld t, Wert D (D.typ t f))
  globs : ∀ g : D.Glob, Option (Wert D (D.gtyp g))
  faeden : Faden → Option (KFaden D)

def beob (M : RufMaschineG D) : BeobB D :=
  ⟨fun t => if sichtbarC π E B (.inl t) = true then some (M.speicher.slots t) else none,
   fun g => if sichtbarC π E B (.inr g) = true then some (M.speicher.globs g) else none,
   fun u => if sichtbarF π E B u = true then some (M.faeden u).kern else none⟩

/-- **Output consistency**: low-equivalent machines show `B` the same
    observation, and conversely. -/
theorem beob_gleich_iff (M N : RufMaschineG D) :
    beob π E B M = beob π E B N ↔ NiGleich π E B M N := by
  constructor
  · intro h
    have hs := congrArg BeobB.slots h
    have hg := congrArg BeobB.globs h
    have hf := congrArg BeobB.faeden h
    refine ⟨fun c hc => ?_, fun t ht => ?_⟩
    · cases c with
      | inl t =>
          have := congrFun hs t
          simp only [beob, hc, if_true] at this
          exact Option.some.inj this
      | inr g =>
          have := congrFun hg g
          simp only [beob, hc, if_true] at this
          exact Option.some.inj this
    · have := congrFun hf t
      simp only [beob, ht, if_true] at this
      exact Option.some.inj this
  · intro h
    simp only [beob, BeobB.mk.injEq]
    refine ⟨funext fun t => ?_, funext fun g => ?_, funext fun u => ?_⟩
    · by_cases hc : sichtbarC π E B (.inl t) = true
      · rw [if_pos hc, if_pos hc, show M.speicher.slots t = N.speicher.slots t from h.1 _ hc]
      · rw [if_neg hc, if_neg hc]
    · by_cases hc : sichtbarC π E B (.inr g) = true
      · rw [if_pos hc, if_pos hc, show M.speicher.globs g = N.speicher.globs g from h.1 _ hc]
      · rw [if_neg hc, if_neg hc]
    · by_cases hc : sichtbarF π E B u = true
      · rw [if_pos hc, if_pos hc, h.2 u hc]
      · rw [if_neg hc, if_neg hc]

end Gleich

/-! ## 4. The metatheorem, generic -/

/-- **Unwinding, generic.** Two step relations `s₁`, `s₂` (two runs, e.g.
    with two oracles), invariants `I₁`, `I₂` kept by their steps, a
    symmetric transitive equivalence `gl` (low-equivalence), a visibility
    of actors. Local respect for invisible actors in both runs, step
    consistency for visible actors: then two runs with the SAME schedule
    `fs` from low-equivalent starts stay low-equivalent at every index.

    Possibilistic and schedule-parametric: both runs are GIVEN (each step
    of each run exists); nothing is claimed about a run that cannot follow
    the schedule. -/
theorem ni_allgemein {σ : Type} {A : Type}
    (s₁ s₂ : σ → A → σ → Prop) (I₁ I₂ : σ → Prop) (sicht : A → Bool)
    (gl : σ → σ → Prop)
    (hsymm : ∀ a b, gl a b → gl b a) (htrans : ∀ a b c, gl a b → gl b c → gl a c)
    (hI₁ : ∀ M a M', I₁ M → s₁ M a M' → I₁ M') (hI₂ : ∀ M a M', I₂ M → s₂ M a M' → I₂ M')
    (hLR₁ : ∀ M a M', I₁ M → sicht a = false → s₁ M a M' → gl M M')
    (hLR₂ : ∀ M a M', I₂ M → sicht a = false → s₂ M a M' → gl M M')
    (hSC : ∀ M N a M' N', I₁ M → I₂ N → sicht a = true → gl M N →
      s₁ M a M' → s₂ N a N' → gl M' N')
    (ms ns : Nat → σ) (fs : Nat → A) (n : Nat)
    (hm : ∀ k, k < n → s₁ (ms k) (fs k) (ms (k + 1)))
    (hn : ∀ k, k < n → s₂ (ns k) (fs k) (ns (k + 1)))
    (hI0 : I₁ (ms 0)) (hJ0 : I₂ (ns 0)) (h0 : gl (ms 0) (ns 0)) :
    ∀ k, k ≤ n → gl (ms k) (ns k) ∧ I₁ (ms k) ∧ I₂ (ns k) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨h0, hI0, hJ0⟩
  | succ k ih =>
      intro hk
      obtain ⟨hg, hi, hj⟩ := ih (by omega)
      have h1 := hm k (by omega)
      have h2 := hn k (by omega)
      refine ⟨?_, hI₁ _ _ _ hi h1, hI₂ _ _ _ hj h2⟩
      cases hv : sicht (fs k) with
      | true => exact hSC _ _ _ _ _ hi hj hv hg h1 h2
      | false =>
          have a1 := hLR₁ _ _ _ hi hv h1
          have a2 := hLR₂ _ _ _ hj hv h2
          exact htrans _ _ _ (hsymm _ _ a1) (htrans _ _ _ hg a2)

/-- **The scheduler form, generic.** The schedule is the output of a choice
    function `plan k M` (step index, current machine). If the choice depends
    only on the low-equivalence class (`hplan`), two runs produced by the
    scheduler from low-equivalent starts take the same actor at every step
    and stay low-equivalent. -/
theorem ni_planer_allgemein {σ : Type} {A : Type}
    (s₁ s₂ : σ → A → σ → Prop) (I₁ I₂ : σ → Prop) (sicht : A → Bool)
    (gl : σ → σ → Prop)
    (hsymm : ∀ a b, gl a b → gl b a) (htrans : ∀ a b c, gl a b → gl b c → gl a c)
    (hI₁ : ∀ M a M', I₁ M → s₁ M a M' → I₁ M') (hI₂ : ∀ M a M', I₂ M → s₂ M a M' → I₂ M')
    (hLR₁ : ∀ M a M', I₁ M → sicht a = false → s₁ M a M' → gl M M')
    (hLR₂ : ∀ M a M', I₂ M → sicht a = false → s₂ M a M' → gl M M')
    (hSC : ∀ M N a M' N', I₁ M → I₂ N → sicht a = true → gl M N →
      s₁ M a M' → s₂ N a N' → gl M' N')
    (plan : Nat → σ → A) (hplan : ∀ k M N, gl M N → plan k M = plan k N)
    (ms ns : Nat → σ) (n : Nat)
    (hm : ∀ k, k < n → s₁ (ms k) (plan k (ms k)) (ms (k + 1)))
    (hn : ∀ k, k < n → s₂ (ns k) (plan k (ns k)) (ns (k + 1)))
    (hI0 : I₁ (ms 0)) (hJ0 : I₂ (ns 0)) (h0 : gl (ms 0) (ns 0)) :
    ∀ k, k ≤ n → gl (ms k) (ns k) ∧ (k < n → plan k (ms k) = plan k (ns k)) := by
  have hall : ∀ k, k ≤ n → gl (ms k) (ns k) ∧ I₁ (ms k) ∧ I₂ (ns k) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨h0, hI0, hJ0⟩
    | succ k ih =>
        intro hk
        obtain ⟨hg, hi, hj⟩ := ih (by omega)
        have h1 := hm k (by omega)
        have h2 := hn k (by omega)
        rw [← hplan k _ _ hg] at h2
        refine ⟨?_, hI₁ _ _ _ hi h1, hI₂ _ _ _ hj h2⟩
        cases hv : sicht (plan k (ms k)) with
        | true => exact hSC _ _ _ _ _ hi hj hv hg h1 h2
        | false =>
            have a1 := hLR₁ _ _ _ hi hv h1
            have a2 := hLR₂ _ _ _ hj hv h2
            exact htrans _ _ _ (hsymm _ _ a1) (htrans _ _ _ hg a2)
  intro k hk
  exact ⟨(hall k hk).1, fun _ => hplan k _ _ (hall k hk).1⟩

/-! ## 5. The unwinding conditions for machine G -/

section G

variable {Dom : Type} (π : Politik Dom) (E : Etiketten D Dom) (B : Dom)
variable (P : Programm D) (O : Orakel D) (passes : Nat)
  (init : Faden → Σ f : D.Fn, Env D (D.params f))

/-- The machines of machine G reachable from SOME start memory with the
    entry assignment `init` (the invariant both runs carry). -/
def ErreichbarVon (M : RufMaschineG D) : Prop :=
  ∃ sp : Speicher D, RufErreichbarG P O passes (RufStartG P sp init) M

theorem erreichbarVon_schritt {M M' : RufMaschineG D} {f : Faden}
    (h : ErreichbarVon P O passes init M) (hs : RufSchrittG P O passes M f M') :
    ErreichbarVon P O passes init M' :=
  let ⟨sp, hr⟩ := h
  ⟨sp, .schritt _ _ _ hr hs⟩

/-- **The unwinding conditions for one step of machine G**, for observer
    `B`, on every machine reachable from a start with entry `init`.

    * `lokal` (LOCAL RESPECT): a step of a thread whose domain may NOT
      flow to `B` leaves the `B`-observation unchanged.
    * `schritt` (STEP CONSISTENCY): a step of a `B`-visible thread, taken
      from two low-equivalent machines, ends in low-equivalent machines.

    OUTPUT CONSISTENCY -- low-equivalent machines show `B` the same
    observation -- holds by definition (`beob_gleich_iff`). -/
structure AbwicklungG : Prop where
  lokal : ∀ (M M' : RufMaschineG D) (f : Faden), ErreichbarVon P O passes init M →
    sichtbarF π E B f = false → RufSchrittG P O passes M f M' → NiGleich π E B M M'
  schritt : ∀ (M N M' N' : RufMaschineG D) (f : Faden), ErreichbarVon P O passes init M →
    ErreichbarVon P O passes init N → sichtbarF π E B f = true → NiGleich π E B M N →
    RufSchrittG P O passes M f M' → RufSchrittG P O passes N f N' → NiGleich π E B M' N'

/-- The start machines of two memories are low-equivalent iff the memories
    agree on the visible carriers: the ghost-free start state of a thread
    does not mention memory. -/
theorem niGleich_start (sp₁ sp₂ : Speicher D)
    (h : SpeicherGleich (sichtbarC π E B) sp₁ sp₂) :
    NiGleich π E B (RufStartG P sp₁ init) (RufStartG P sp₂ init) := by
  refine ⟨h, fun t _ => ?_⟩
  show RufFadenG.kern (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp₁.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp₁.welt [])]⟩ : RufFadenG D)) =
    RufFadenG.kern (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp₂.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp₂.welt [])]⟩ : RufFadenG D))
  cases init t
  rfl

/-- **THE METATHEOREM (`ni_aus_abwicklung`).** Under the unwinding
    conditions of machine G for observer `B`: two runs of the same program
    with the same oracle, the SAME schedule `fs` and start memories that
    agree on every `B`-visible carrier (the same `B`-inputs) show `B` the
    same observation at every index `k ≤ n`. -/
theorem ni_aus_abwicklung (hA : AbwicklungG π E B P O passes init)
    (sp₁ sp₂ : Speicher D) (hsp : SpeicherGleich (sichtbarC π E B) sp₁ sp₂)
    (ms ns : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat)
    (hm : LaufG P O passes (RufStartG P sp₁ init) ms fs n)
    (hn : LaufG P O passes (RufStartG P sp₂ init) ns fs n) :
    ∀ k, k ≤ n → beob π E B (ms k) = beob π E B (ns k) := by
  intro k hk
  have := ni_allgemein (RufSchrittG P O passes) (RufSchrittG P O passes)
    (ErreichbarVon P O passes init) (ErreichbarVon P O passes init) (sichtbarF π E B)
    (NiGleich π E B) (fun _ _ h => h.symm) (fun _ _ _ h1 h2 => h1.trans h2)
    (fun _ _ _ h hs => erreichbarVon_schritt P O passes init h hs)
    (fun _ _ _ h hs => erreichbarVon_schritt P O passes init h hs)
    (fun M a M' hi hv hs => hA.lokal M M' a hi hv hs)
    (fun M a M' hi hv hs => hA.lokal M M' a hi hv hs)
    (fun M N a M' N' hi hj hv hg h1 h2 => hA.schritt M N M' N' a hi hj hv hg h1 h2)
    ms ns fs n hm.2 hn.2 (by rw [hm.1]; exact ⟨sp₁, .start⟩) (by rw [hn.1]; exact ⟨sp₂, .start⟩)
    (by rw [hm.1, hn.1]; exact niGleich_start π E B P init sp₁ sp₂ hsp) k hk
  exact (beob_gleich_iff π E B _ _).mpr this.1

/-- **The scheduler form (`ni_planer`).** The runs are produced by a
    scheduler `plan k M` whose choice depends only on what `B` observes
    (`hplan`: equal observations, equal choice). Then the two runs take the
    same thread at every step and show `B` the same observation. This is
    the theorem that explains the schedule instead of fixing it: a
    scheduler that looks at `A`-state (load, `A`'s queue lengths) does NOT
    meet `hplan`, and NI is not claimed for it. -/
theorem ni_planer (hA : AbwicklungG π E B P O passes init)
    (plan : Nat → RufMaschineG D → Faden)
    (hplan : ∀ k M N, beob π E B M = beob π E B N → plan k M = plan k N)
    (sp₁ sp₂ : Speicher D) (hsp : SpeicherGleich (sichtbarC π E B) sp₁ sp₂)
    (ms ns : Nat → RufMaschineG D) (n : Nat)
    (hm0 : ms 0 = RufStartG P sp₁ init) (hn0 : ns 0 = RufStartG P sp₂ init)
    (hm : ∀ k, k < n → RufSchrittG P O passes (ms k) (plan k (ms k)) (ms (k + 1)))
    (hn : ∀ k, k < n → RufSchrittG P O passes (ns k) (plan k (ns k)) (ns (k + 1))) :
    ∀ k, k ≤ n → beob π E B (ms k) = beob π E B (ns k) ∧
      (k < n → plan k (ms k) = plan k (ns k)) := by
  intro k hk
  have := ni_planer_allgemein (RufSchrittG P O passes) (RufSchrittG P O passes)
    (ErreichbarVon P O passes init) (ErreichbarVon P O passes init) (sichtbarF π E B)
    (NiGleich π E B) (fun _ _ h => h.symm) (fun _ _ _ h1 h2 => h1.trans h2)
    (fun _ _ _ h hs => erreichbarVon_schritt P O passes init h hs)
    (fun _ _ _ h hs => erreichbarVon_schritt P O passes init h hs)
    (fun M a M' hi hv hs => hA.lokal M M' a hi hv hs)
    (fun M a M' hi hv hs => hA.lokal M M' a hi hv hs)
    (fun M N a M' N' hi hj hv hg h1 h2 => hA.schritt M N M' N' a hi hj hv hg h1 h2)
    plan (fun k M N h => hplan k M N ((beob_gleich_iff π E B M N).mpr h))
    ms ns n hm hn (by rw [hm0]; exact ⟨sp₁, .start⟩) (by rw [hn0]; exact ⟨sp₂, .start⟩)
    (by rw [hm0, hn0]; exact niGleich_start π E B P init sp₁ sp₂ hsp) k hk
  exact ⟨(beob_gleich_iff π E B _ _).mpr this.1, this.2⟩

/-- **The fixed-timetable partition scheduler (`ni_zeitplan`)** -- seL4's
    configuration: the thread of step `k` is `tafel k`, fixed before the
    run and independent of every state. It meets `hplan` trivially. -/
theorem ni_zeitplan (hA : AbwicklungG π E B P O passes init) (tafel : Nat → Faden)
    (sp₁ sp₂ : Speicher D) (hsp : SpeicherGleich (sichtbarC π E B) sp₁ sp₂)
    (ms ns : Nat → RufMaschineG D) (n : Nat)
    (hm : LaufG P O passes (RufStartG P sp₁ init) ms tafel n)
    (hn : LaufG P O passes (RufStartG P sp₂ init) ns tafel n) :
    ∀ k, k ≤ n → beob π E B (ms k) = beob π E B (ns k) := fun k hk =>
  (ni_planer π E B P O passes init hA (fun k _ => tafel k) (fun _ _ _ _ => rfl) sp₁ sp₂ hsp
    ms ns n hm.1 hn.1 hm.2 hn.2 k hk).1

end G

end Gabbro.Grammatik
