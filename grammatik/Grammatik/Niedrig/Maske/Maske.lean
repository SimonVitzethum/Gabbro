/-
  File:      Grammatik/Niedrig/Maske/Maske.lean
  Subject:   INTERRUPT MASKING AS A PER-CORE STATE (L7a): `CoreMask`,
    `MaskEvent`, and the step relation `MaskStep`, with the frame,
    determinism, entry-refusal, leave-refusal, depth, enter/leave-roundtrip,
    and balanced-sequence theorems.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; nothing imports this module except the witness).
  * `CoreMask` holds, per core, the mask bit, the nesting depth of handlers
    running on it, and the stack of saved mask bits (L7 names entry masking
    and saved-bit restore; nesting with priorities is L7b, not this package).
  * `MaskStep` is the four-event relation: masking and unmasking change only
    the acting core; a handler enters only on an unmasked core, masks it,
    grows the depth, and pushes the entry bit; leaving pops the saved bit,
    restores it, and shrinks the depth.
  * The theorems say the machine is tight: an event changes no other core,
    the step is deterministic, no handler enters masked, no leave leaves an
    empty stack, entering grows and leaving shrinks the depth by exactly one,
    one enter/leave pair restores the mask bit, and every balanced sequence
    restores every core's mask bit.
-/
module

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Maske

/-- The per-core interrupt state: mask bit, handler nesting depth, and the
    stack of saved mask bits (one entry per running handler). -/
structure KernZustand where
  maskiert : Bool
  tiefe : Nat
  stapel : List Bool
  deriving DecidableEq

/-- The per-core interrupt mask state: one state per core. -/
structure CoreMask where
  zustand : Nat → KernZustand

/-- The state with core `c` replaced by `z`; every other core is untouched. -/
def aufKern (s : CoreMask) (c : Nat) (z : KernZustand) : CoreMask :=
  { zustand := fun c' => if c' = c then z else s.zustand c' }

/-- Reading back the acting core gives the installed state. -/
theorem aufKernEq (s : CoreMask) (c : Nat) (z : KernZustand) :
    (aufKern s c z).zustand c = z := by
  show (if c = c then z else s.zustand c) = z
  have hc : c = c := rfl
  rw [if_pos hc]

/-- Reading back another core gives the old state. -/
theorem aufKernAnderer (s : CoreMask) (c c' : Nat) (z : KernZustand)
    (hne : c' ≠ c) :
    (aufKern s c z).zustand c' = s.zustand c' := by
  show (if c' = c then z else s.zustand c') = s.zustand c'
  rw [if_neg hne]

/-- Masking installs `true` and keeps depth and stack. -/
def maskiereNach (s : CoreMask) (c : Nat) : CoreMask :=
  aufKern s c { s.zustand c with maskiert := true }

/-- Unmasking installs `false` and keeps depth and stack. -/
def entmaskiereNach (s : CoreMask) (c : Nat) : CoreMask :=
  aufKern s c { s.zustand c with maskiert := false }

/-- Entering masks the core, grows the depth, and pushes the entry bit
    (`false`: entry needs the core unmasked, so L7a pushes `false`). -/
def betreteNach (s : CoreMask) (c : Nat) : CoreMask :=
  aufKern s c
    { maskiert := true
      tiefe := (s.zustand c).tiefe + 1
      stapel := false :: (s.zustand c).stapel }

/-- Leaving pops the saved bit `b`, restores it, and shrinks the depth. -/
def verlasseNach (s : CoreMask) (c : Nat) (b : Bool) (bs : List Bool) :
    CoreMask :=
  aufKern s c
    { maskiert := b
      tiefe := (s.zustand c).tiefe - 1
      stapel := bs }

/-- Entering pushes the entry bit on the stack. -/
theorem betreteNachStapel (s : CoreMask) (c : Nat) :
    ((betreteNach s c).zustand c).stapel = false :: (s.zustand c).stapel := by
  unfold betreteNach
  rw [aufKernEq]

/-- Entering grows the depth by exactly one. -/
theorem betreteNachTiefe (s : CoreMask) (c : Nat) :
    ((betreteNach s c).zustand c).tiefe = (s.zustand c).tiefe + 1 := by
  unfold betreteNach
  rw [aufKernEq]

/-- Leaving restores the popped bit. -/
theorem verlasseNachMaskiert (s : CoreMask) (c : Nat) (b : Bool)
    (bs : List Bool) :
    ((verlasseNach s c b bs).zustand c).maskiert = b := by
  unfold verlasseNach
  rw [aufKernEq]

/-- Leaving shrinks the depth by exactly one. -/
theorem verlasseNachTiefe (s : CoreMask) (c : Nat) (b : Bool)
    (bs : List Bool) :
    ((verlasseNach s c b bs).zustand c).tiefe = (s.zustand c).tiefe - 1 := by
  unfold verlasseNach
  rw [aufKernEq]

/-- The four L7a mask events (row L7 names no more: re-entry and handler
    tables are later packages). -/
inductive MaskEvent
  | maskiere : Nat → MaskEvent
  | entmaskiere : Nat → MaskEvent
  | betreteHandler : Nat → Nat → MaskEvent
  | verlasseHandler : Nat → MaskEvent
  deriving DecidableEq

/-- The core an event acts on. -/
def kernVon : MaskEvent → Nat
  | MaskEvent.maskiere c => c
  | MaskEvent.entmaskiere c => c
  | MaskEvent.betreteHandler c _ => c
  | MaskEvent.verlasseHandler c => c

/-- One mask step: mask/unmask change only the acting core; a handler enters
    only unmasked (and then masks); leaving needs a running handler. -/
inductive MaskStep : MaskEvent → CoreMask → CoreMask → Prop where
  | maskiere (s : CoreMask) (c : Nat) :
      MaskStep (MaskEvent.maskiere c) s (maskiereNach s c)
  | entmaskiere (s : CoreMask) (c : Nat) :
      MaskStep (MaskEvent.entmaskiere c) s (entmaskiereNach s c)
  | betrete (s : CoreMask) (c v : Nat) (hunmask : (s.zustand c).maskiert = false) :
      MaskStep (MaskEvent.betreteHandler c v) s (betreteNach s c)
  | verlasse (s : CoreMask) (c : Nat) (b : Bool) (bs : List Bool)
      (hstapel : (s.zustand c).stapel = b :: bs) :
      MaskStep (MaskEvent.verlasseHandler c) s (verlasseNach s c b bs)

/-! ## The step changes no other core and is deterministic -/

/-- An event of core `c` changes no other core's state. -/
theorem schrittRahmen (e : MaskEvent) (s s' : CoreMask)
    (h : MaskStep e s s') :
    ∀ c', c' ≠ kernVon e → (s'.zustand c') = (s.zustand c') := by
  cases h with
  | maskiere s c =>
    intro c' hne
    unfold maskiereNach
    exact aufKernAnderer s c c' _ hne
  | entmaskiere s c =>
    intro c' hne
    unfold entmaskiereNach
    exact aufKernAnderer s c c' _ hne
  | betrete s c _ _ =>
    intro c' hne
    unfold betreteNach
    exact aufKernAnderer s c c' _ hne
  | verlasse s c _ _ _ =>
    intro c' hne
    unfold verlasseNach
    exact aufKernAnderer s c c' _ hne

/-- `MaskStep` is deterministic: one event from one state reaches one state. -/
theorem schrittDet (e : MaskEvent) (s a b : CoreMask)
    (h1 : MaskStep e s a) (h2 : MaskStep e s b) : a = b := by
  cases h1 with
  | maskiere _ _ =>
    cases h2
    rfl
  | entmaskiere _ _ =>
    cases h2
    rfl
  | betrete _ _ _ _ =>
    cases h2
    rfl
  | verlasse s c b bs hst =>
    cases h2 with
    | verlasse _ _ b' bs' hst' =>
      rw [hst] at hst'
      cases hst'
      rfl

/-! ## Entry, leave, and depth -/

/-- No handler enters on a masked core. -/
theorem keinBetreteMaskiert (s s' : CoreMask) (c v : Nat)
    (hm : (s.zustand c).maskiert = true)
    (h : MaskStep (MaskEvent.betreteHandler c v) s s') : False := by
  cases h with
  | betrete _ _ _ hunmask =>
    rw [hunmask] at hm
    exact Bool.noConfusion hm

/-- A leave without a running handler has no step: an empty stack never
    leaves, so the depth never goes below zero. -/
theorem keinVerlasseLeer (s s' : CoreMask) (c : Nat)
    (hleer : (s.zustand c).stapel = [])
    (h : MaskStep (MaskEvent.verlasseHandler c) s s') : False := by
  cases h with
  | verlasse _ _ _ _ hst =>
    rw [hleer] at hst
    cases hst

/-- Entering grows the depth by exactly one. -/
theorem tiefeBetrete (s m : CoreMask) (c v : Nat)
    (h : MaskStep (MaskEvent.betreteHandler c v) s m) :
    (m.zustand c).tiefe = (s.zustand c).tiefe + 1 := by
  cases h with
  | betrete s c _ _ =>
    exact betreteNachTiefe s c

/-- Leaving shrinks the depth by exactly one. -/
theorem tiefeVerlasse (s s' : CoreMask) (c : Nat)
    (h : MaskStep (MaskEvent.verlasseHandler c) s s') :
    (s'.zustand c).tiefe = (s.zustand c).tiefe - 1 := by
  cases h with
  | verlasse s c _ _ _ =>
    exact verlasseNachTiefe s c _ _

/-! ## One enter/leave pair restores the mask bit -/

/-- After one enter/leave pair on a core its mask bit is what it was. -/
theorem betreteVerlasseMaske (s m s' : CoreMask) (c v : Nat)
    (h1 : MaskStep (MaskEvent.betreteHandler c v) s m)
    (h2 : MaskStep (MaskEvent.verlasseHandler c) m s') :
    (s'.zustand c).maskiert = (s.zustand c).maskiert := by
  cases h1 with
  | betrete s c v hunmask =>
    cases h2 with
    | verlasse _ _ b bs hst =>
      rw [betreteNachStapel s c] at hst
      cases hst
      rw [verlasseNachMaskiert]
      exact hunmask.symm

/-! ## Balanced sequences restore every core's mask bit -/

/-- A balanced handler sequence: adjacent enter/leave pairs, possibly on
    different cores. -/
inductive Ausgeglichen : List MaskEvent → CoreMask → CoreMask → Prop where
  | leer (s : CoreMask) : Ausgeglichen [] s s
  | paar (k v : Nat) (s m s' s'' : CoreMask) (rest : List MaskEvent)
      (h1 : MaskStep (MaskEvent.betreteHandler k v) s m)
      (h2 : MaskStep (MaskEvent.verlasseHandler k) m s')
      (hrest : Ausgeglichen rest s' s'') :
      Ausgeglichen (MaskEvent.betreteHandler k v ::
        MaskEvent.verlasseHandler k :: rest) s s''

/-- A balanced sequence restores every core's mask bit. -/
theorem ausgeglichenMaske (l : List MaskEvent) (s s' : CoreMask)
    (h : Ausgeglichen l s s') (c : Nat) :
    (s'.zustand c).maskiert = (s.zustand c).maskiert := by
  induction h with
  | leer s => rfl
  | paar k v s m s' s'' rest h1 h2 hrest ih =>
    by_cases heq : k = c
    · subst heq
      rw [ih]
      exact betreteVerlasseMaske s m s' k v h1 h2
    · have hne : c ≠ k := fun hcc => heq hcc.symm
      have e1 : (s'.zustand c).maskiert = (m.zustand c).maskiert := by
        cases h2 with
        | verlasse _ _ _ _ _ =>
          unfold verlasseNach
          exact congrArg KernZustand.maskiert (aufKernAnderer m k c _ hne)
      have e2 : (m.zustand c).maskiert = (s.zustand c).maskiert := by
        cases h1 with
        | betrete _ _ _ _ =>
          unfold betreteNach
          exact congrArg KernZustand.maskiert (aufKernAnderer s k c _ hne)
      rw [ih, e1, e2]

/-! ## Connection to `KernPlan` and `KernMaske` (statement only, not proved)

  `KernPlan` (grammatik/Grammatik/Zielsatz/Kern/Spec/Teil1.lean:268) says a
  handler takes its first step only where no other thread of its core holds a
  lock declared `masks irqs` (ENTRY ONLY WHEN UNMASKED, Teil1.lean:259), and
  runs to completion afterwards (Teil1.lean:263). `MaskeKern`
  (KernMaskea.lean:221) keeps per core the masking (thread, lock) pairs, and
  `KernSchritt.eintritt` (KernMaske.lean:105) needs that core's list empty.
  (Note: no definition named `Reihenfolge` exists in Teil1.lean; the run-side
  order twin is `MaskenOrdnung` over the event log, cited at Teil1.lean:266.)
  This package says the same "no handler on a masked core" as a state
  machine (`keinBetreteMaskiert`). A later refinement lemma (L7b) would
  state: under the handler discipline, every `MaskStep` run projects to a
  `KernPlan` fragment, with `(s.zustand c).maskiert = false` in place of
  `mk c = []`. Left out: the nesting/priority order and that projection.
-/

#print axioms Gabbro.Grammatik.Niedrig.Maske.schrittRahmen
#print axioms Gabbro.Grammatik.Niedrig.Maske.schrittDet
#print axioms Gabbro.Grammatik.Niedrig.Maske.keinBetreteMaskiert
#print axioms Gabbro.Grammatik.Niedrig.Maske.betreteVerlasseMaske
#print axioms Gabbro.Grammatik.Niedrig.Maske.ausgeglichenMaske

end Gabbro.Grammatik.Niedrig.Maske
