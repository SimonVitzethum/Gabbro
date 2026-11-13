/-
  File:      Grammatik/Niedrig/Maske/PrioSaetze.lean
  Subject:   THEOREMS OVER PRIORITY NESTING (L7b): the strictly decreasing
    stack invariant and that the current level stays above it, the refusal
    of levels at or below the current one, the frame, determinism, the
    raise/lower roundtrip, and the entry mask bit for both values.

  The depth bound (stack length at most the current level) is stated in the
  closing doc comment and left out: its induction needs a strictly
  decreasing-list length argument beyond the short-proof budget.
-/
module

public import Grammatik.Niedrig.Maske.Prio

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Maske

/-- The stack of interrupted levels is strictly decreasing from the top:
    each element below the head is strictly smaller than its predecessor. -/
def StapelStreng : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b < a ∧ StapelStreng (b :: rest)

/-- Every stacked level lies strictly below the bound. -/
def AlleKleiner : Nat → List Nat → Prop
  | _, [] => True
  | b, x :: xs => x < b ∧ AlleKleiner b xs

/-- The per-core invariant: a strictly decreasing stack, all below current. -/
def KernInv (k : KernPrio) : Prop :=
  StapelStreng k.unterbrochen ∧ AlleKleiner k.aktuell k.unterbrochen

/-- The global invariant: every core satisfies `KernInv`. -/
def PrioInv (s : PrioMaske) : Prop :=
  ∀ c, KernInv (s.prio c)

/-! ## The invariant holds initially -/

/-- The invariant holds initially: thread level with an empty stack. -/
theorem prioAnfangInv (m : CoreMask) : PrioInv (anfangPrioMaske m) := by
  intro c
  show StapelStreng ((anfangPrioMaske m).prio c).unterbrochen ∧
    AlleKleiner ((anfangPrioMaske m).prio c).aktuell
      ((anfangPrioMaske m).prio c).unterbrochen
  show StapelStreng ([] : List Nat) ∧ AlleKleiner 0 []
  exact ⟨trivial, trivial⟩

/-! ## Small list helpers (each by one `cases` plus recursion) -/

/-- Raising the bound keeps every stacked level below it. -/
theorem alleMono (xs : List Nat) (b b' : Nat)
    (h : AlleKleiner b xs) (hlt : b < b') : AlleKleiner b' xs := by
  cases xs with
  | nil => trivial
  | cons y ys =>
      have hpair : y < b ∧ AlleKleiner b ys := h
      have hy : y < b' := by omega
      have htail : AlleKleiner b' ys := alleMono ys b b' hpair.2 hlt
      show y < b' ∧ AlleKleiner b' ys
      exact ⟨hy, htail⟩

/-- Pushing `a` over a strictly decreasing stack below `a` stays strict. -/
theorem strengSchiebe (a : Nat) (xs : List Nat)
    (hstreng : StapelStreng xs) (halle : AlleKleiner a xs) :
    StapelStreng (a :: xs) := by
  cases xs with
  | nil => trivial
  | cons y ys =>
      have hpair : y < a ∧ AlleKleiner a ys := halle
      show y < a ∧ StapelStreng (y :: ys)
      exact ⟨hpair.1, hstreng⟩

/-- Pushing `a` below the new level `p` keeps every level below `p`. -/
theorem alleSchiebe (a p : Nat) (xs : List Nat)
    (halle : AlleKleiner a xs) (hlt : a < p) :
    AlleKleiner p (a :: xs) := by
  have hxs : AlleKleiner p xs := alleMono xs a p halle hlt
  show a < p ∧ AlleKleiner p xs
  exact ⟨hlt, hxs⟩

/-- The tail of a strict stack is strict. -/
theorem strengSenke (a : Nat) (xs : List Nat)
    (h : StapelStreng (a :: xs)) : StapelStreng xs := by
  cases xs with
  | nil => trivial
  | cons y ys =>
      have hpair : y < a ∧ StapelStreng (y :: ys) := h
      exact hpair.2

/-- Lowering to `a` keeps every remaining level below `a`: the head comes
    from strictness, the tail from the induction hypothesis lifted by
    monotonicity. -/
theorem alleSenkeNeu (xs : List Nat) (a b : Nat)
    (hstreng : StapelStreng (a :: xs))
    (halle : AlleKleiner b (a :: xs)) : AlleKleiner a xs := by
  cases xs with
  | nil => trivial
  | cons y ys =>
      have hspair : y < a ∧ StapelStreng (y :: ys) := hstreng
      have h1 : a < b ∧ AlleKleiner b (y :: ys) := halle
      have hys_y : AlleKleiner y ys :=
        alleSenkeNeu ys y b hspair.2 h1.2
      have hys_a : AlleKleiner a ys := alleMono ys y a hys_y hspair.1
      show y < a ∧ AlleKleiner a ys
      exact ⟨hspair.1, hys_a⟩

/-! ## The invariant is preserved -/

/-- Raising preserves the per-core invariant. -/
theorem erhoeheKernInv (s : PrioMaske) (c p : Nat) (b : Bool)
    (hinv : KernInv (s.prio c)) (hgt : (s.prio c).aktuell < p) :
    KernInv ((erhoeheNach s c p b).prio c) := by
  have hakt := erhoeheNachAktuell s c p b
  have hst := erhoeheNachStapel s c p b
  have hstreng : StapelStreng ((s.prio c).unterbrochen) := hinv.1
  have halle : AlleKleiner ((s.prio c).aktuell) ((s.prio c).unterbrochen) :=
    hinv.2
  show StapelStreng ((erhoeheNach s c p b).prio c).unterbrochen ∧
    AlleKleiner ((erhoeheNach s c p b).prio c).aktuell
      ((erhoeheNach s c p b).prio c).unterbrochen
  rw [hakt, hst]
  constructor
  · exact strengSchiebe (s.prio c).aktuell
      ((s.prio c).unterbrochen) hstreng halle
  · exact alleSchiebe (s.prio c).aktuell p
      ((s.prio c).unterbrochen) halle hgt

/-- Lowering preserves the per-core invariant. -/
theorem senkeKernInv (s : PrioMaske) (c alt : Nat) (rest : List Nat)
    (hinv : KernInv (s.prio c))
    (hst : (s.prio c).unterbrochen = alt :: rest) :
    KernInv ((senkeNach s c alt rest).prio c) := by
  have hakt := senkeNachAktuell s c alt rest
  have hstp := senkeNachStapel s c alt rest
  have hstreng : StapelStreng ((s.prio c).unterbrochen) := hinv.1
  have halle : AlleKleiner ((s.prio c).aktuell) ((s.prio c).unterbrochen) :=
    hinv.2
  show StapelStreng ((senkeNach s c alt rest).prio c).unterbrochen ∧
    AlleKleiner ((senkeNach s c alt rest).prio c).aktuell
      ((senkeNach s c alt rest).prio c).unterbrochen
  rw [hakt, hstp]
  rw [hst] at hstreng
  rw [hst] at halle
  constructor
  · exact strengSenke alt rest hstreng
  · exact alleSenkeNeu rest alt ((s.prio c).aktuell) hstreng halle

/-- Every step preserves the global invariant. -/
theorem prioSchrittInv (e : PrioEvent) (s s' : PrioMaske)
    (h : PrioStep e s s') (hinv : PrioInv s) : PrioInv s' := by
  cases h with
  | erhoehe s c p maskNeu hmask hp1 hgt =>
      intro c'
      by_cases heq : c' = c
      · rw [heq]
        exact erhoeheKernInv s c p maskNeu (hinv c) hgt
      · have heqPrio : (erhoeheNach s c p maskNeu).prio c' = s.prio c' :=
          erhoeheNachAndererPrio s c c' p maskNeu heq
        rw [heqPrio]
        exact hinv c'
  | senke s c alt rest hstapel =>
      intro c'
      by_cases heq : c' = c
      · rw [heq]
        exact senkeKernInv s c alt rest (hinv c) hstapel
      · have heqPrio : (senkeNach s c alt rest).prio c' = s.prio c' :=
          senkeNachAndererPrio s c c' alt rest heq
        rw [heqPrio]
        exact hinv c'

/-! ## What the invariant says -/

/-- The stack is strictly decreasing from the top. -/
theorem prioStapelStreng (s : PrioMaske) (hinv : PrioInv s) (c : Nat) :
    StapelStreng ((s.prio c).unterbrochen) :=
  (hinv c).1

/-- The current level is strictly above every stacked level. -/
theorem prioAktuellUeber (s : PrioMaske) (hinv : PrioInv s) (c : Nat) :
    AlleKleiner ((s.prio c).aktuell) ((s.prio c).unterbrochen) :=
  (hinv c).2

/-! ## Refusal, frame, determinism -/

/-- No handler at or below the current level enters. -/
theorem keinEintrittKlein (s s' : PrioMaske) (c p : Nat) (b : Bool)
    (hle : p ≤ (s.prio c).aktuell)
    (h : PrioStep (PrioEvent.erhoehe c p b) s s') : False := by
  cases h with
  | erhoehe s c p b hmask hp1 hgt =>
      omega

/-- A step of one core changes no other core: neither its mask state nor
    its priority record. -/
theorem schrittRahmenPrio (e : PrioEvent) (s s' : PrioMaske)
    (h : PrioStep e s s') (c' : Nat) (hne : c' ≠ prioKernVon e) :
    (s'.maske.zustand c') = (s.maske.zustand c') ∧
      (s'.prio c') = (s.prio c') := by
  cases h with
  | erhoehe s c p b hmask hp1 hgt =>
      have hne' : c' ≠ c := hne
      have hm : ((erhoeheNach s c p b).maske.zustand c') =
          (s.maske.zustand c') := by
        unfold erhoeheNach maskeSetze
        rw [aufPrioMaske]
        exact aufKernAnderer s.maske c c' _ hne'
      have hp : (erhoeheNach s c p b).prio c' = s.prio c' :=
        erhoeheNachAndererPrio s c c' p b hne'
      exact ⟨hm, hp⟩
  | senke s c alt rest hst =>
      have hne' : c' ≠ c := hne
      have hm : ((senkeNach s c alt rest).maske.zustand c') =
          (s.maske.zustand c') := by
        have heq : (senkeNach s c alt rest).maske = s.maske := by
          unfold senkeNach
          rw [aufPrioMaske]
        rw [heq]
      have hp : (senkeNach s c alt rest).prio c' = s.prio c' :=
        senkeNachAndererPrio s c c' alt rest hne'
      exact ⟨hm, hp⟩

/-- `PrioStep` is deterministic. -/
theorem schrittDetPrio (e : PrioEvent) (s a b : PrioMaske)
    (h1 : PrioStep e s a) (h2 : PrioStep e s b) : a = b := by
  cases h1 with
  | erhoehe s c p m hmask hp1 hgt =>
      cases h2
      rfl
  | senke s c alt rest hst =>
      cases h2 with
      | senke _ _ alt' rest' hst' =>
          rw [hst] at hst'
          cases hst'
          rfl

/-! ## Raise then lower restores the level and the stack -/

/-- After raise then lower on one core the level and the stack are back. -/
theorem raiseSenkePrio (s m s' : PrioMaske) (c p : Nat) (b : Bool)
    (h1 : PrioStep (PrioEvent.erhoehe c p b) s m)
    (h2 : PrioStep (PrioEvent.senke c) m s') :
    (s'.prio c).aktuell = (s.prio c).aktuell ∧
      (s'.prio c).unterbrochen = (s.prio c).unterbrochen := by
  cases h1 with
  | erhoehe s c p b hmask hp1 hgt =>
      cases h2 with
      | senke _ _ alt rest hst =>
          rw [erhoeheNachStapel s c p b] at hst
          cases hst
          exact ⟨senkeNachAktuell _ _ _ _, senkeNachStapel _ _ _ _⟩

/-! ## The entry mask bit, for both values -/

/-- A raise step installs its entry mask bit (stated for both values of
    `maskNeu`: `false` leaves the core unmasked for further preemption,
    `true` masks it). -/
theorem erhoeheSchrittMaske (s m : PrioMaske) (c p : Nat) (b : Bool)
    (h : PrioStep (PrioEvent.erhoehe c p b) s m) :
    (m.maske.zustand c).maskiert = b := by
  cases h with
  | erhoehe s c p b hmask hp1 hgt =>
      exact erhoeheNachMaske s c p b

/-! ## Connection to `KernPlan` (statement only, not proved)

  `KernPlan` (grammatik/Grammatik/Zielsatz/Kern/Spec/Teil1.lean:259) says a
  handler takes its FIRST step only where no other thread of its core holds
  a lock declared `masks irqs` (ENTRY ONLY WHEN UNMASKED, Teil1.lean:259),
  and runs to completion afterwards (RUN TO COMPLETION, Teil1.lean:263):
  no other thread of its core steps until the handler is finished
  (Teil1.lean:263-265). Nesting relates to it as follows: a nested handler
  is a SEPARATE handler activation on the SAME core that completes before
  the interrupted one continues (LIFO); the interrupted handler's remaining
  run is a second run-to-completion fragment after the nested one finishes.
  The refinement lemma a later package owes: under the handler discipline,
  every `PrioStep` run projects to a `KernPlan` fragment per activation,
  with `(s.prio c).aktuell` marking which activation runs and the stack
  marking the suspended ones; equal levels never preempt (`keinEintrittKlein`)
  and each activation completes before its predecessor resumes
  (`raiseSenkePrio`). Left out: that projection and the depth bound below.

  Depth bound (left out, listed): for every core with `PrioInv`, the stack
  length is at most the current level. It follows from strict decrease of
  naturals but needs a decreasing-list length induction beyond the
  short-proof budget of this package.
-/

#print axioms Gabbro.Grammatik.Niedrig.Maske.prioSchrittInv
#print axioms Gabbro.Grammatik.Niedrig.Maske.keinEintrittKlein
#print axioms Gabbro.Grammatik.Niedrig.Maske.schrittRahmenPrio
#print axioms Gabbro.Grammatik.Niedrig.Maske.schrittDetPrio
#print axioms Gabbro.Grammatik.Niedrig.Maske.raiseSenkePrio

end Gabbro.Grammatik.Niedrig.Maske
