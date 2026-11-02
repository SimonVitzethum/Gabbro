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
module
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
@[expose] public section


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

end Gabbro.Grammatik
