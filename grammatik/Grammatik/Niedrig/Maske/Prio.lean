/-
  File:      Grammatik/Niedrig/Maske/Prio.lean
  Subject:   PRIORITY NESTING OF HANDLERS (L7b), DEFINITIONS: `KernPrio`,
    `PrioMaske`, `PrioEvent`, and the step relation `PrioStep` over a
    per-core current level and a stack of interrupted levels, reusing
    `CoreMask` for the mask check.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; `Maske.lean` is not changed).
  * Each core has a current level (`Nat`, 0 is thread level) and a stack of
    interrupted levels; a handler has a declared level `p >= 1`.
  * `PrioEvent` is a NEW inductive beside `MaskEvent` (not an extension of
    its vocabulary): `erhoehe c p maskNeu` raises core `c` to level `p`,
    `senke c` lowers it. Rationale: `Maske.lean` is frozen, and priority
    gating is orthogonal to the L7a mask/unmask/enter/leave vocabulary;
    the mask side is reused by reading `(s.maske.zustand c).maskiert`.
  * Entry needs the core unmasked AND a strictly greater level (equal is
    refused: no re-entry of the same level); entering pushes the old level
    and installs `p`; leaving pops. Whether entering also masks is a Bool
    parameter `maskNeu` of the entry event (see below).

  ON MASKING AT ENTRY (row L7 and PLAN-COMPILER-READY section 4.4).
  * Row L7 (PLAN-COMPILER-READY.md:183) says: "interrupts beyond `KernPlan`:
    re-entry, nesting with priority levels, masking as a per-core state of
    the context, the handler tables the kernel installs as proved statements
    about its own tables (was X3)".
  * Section 4.4 (PLAN-COMPILER-READY.md:296) says for `IrqDelivery`: "an
    interrupt is delivered at an instruction boundary, to the installed
    handler, under the mask and priority the kernel set".
  * Neither sentence says entering sets the mask; the low-level plan only
    names "interrupt nesting/masking and core locality" as an obligation
    (LOW-LEVEL-SYNTAX-PLAN.md:193) and notes "Interrupt masking is not a
    multicore lock" (LOW-LEVEL-SYNTAX-PLAN.md:194). The plan therefore
    leaves auto-masking open, so entry carries `maskNeu : Bool` and every
    mask theorem below is stated for both values.
-/
module

public import Grammatik.Niedrig.Maske.Maske

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Maske

/-- The per-core priority state: current level and stack of interrupted
    levels (`0` is thread level; handlers live at `p >= 1`). -/
structure KernPrio where
  aktuell : Nat
  unterbrochen : List Nat
  deriving DecidableEq

/-- The combined per-core state: the L7a mask state plus the L7b priority
    state (one priority record per core). -/
structure PrioMaske where
  maske : CoreMask
  prio : Nat → KernPrio

/-- Pushing level `p` over the record `k`: install `p`, keep `k.aktuell`
    on top of the stack. -/
def schiebePrio (k : KernPrio) (p : Nat) : KernPrio :=
  { aktuell := p
    unterbrochen := k.aktuell :: k.unterbrochen }

/-- Popping to level `alt` with the remaining stack `rest`. -/
def nimmPrio (alt : Nat) (rest : List Nat) : KernPrio :=
  { aktuell := alt
    unterbrochen := rest }

/-- The state with core `c` replaced by `k`; every other core is untouched. -/
def aufPrio (s : PrioMaske) (c : Nat) (k : KernPrio) : PrioMaske :=
  { maske := s.maske
    prio := fun c' => if c' = c then k else s.prio c' }

/-- Reading back the acting core gives the installed record. -/
theorem aufPrioEq (s : PrioMaske) (c : Nat) (k : KernPrio) :
    (aufPrio s c k).prio c = k := by
  show (if c = c then k else s.prio c) = k
  have hc : c = c := rfl
  rw [if_pos hc]

/-- Reading back another core gives the old record. -/
theorem aufPrioAnderer (s : PrioMaske) (c c' : Nat) (k : KernPrio)
    (hne : c' ≠ c) :
    (aufPrio s c k).prio c' = s.prio c' := by
  show (if c' = c then k else s.prio c') = s.prio c'
  rw [if_neg hne]

/-- Replacing the priority record keeps the mask state. -/
theorem aufPrioMaske (s : PrioMaske) (c : Nat) (k : KernPrio) :
    (aufPrio s c k).maske = s.maske :=
  rfl

/-- The initial priority record of every core: thread level, empty stack. -/
def anfangPrio : Nat → KernPrio :=
  fun _ =>
    { aktuell := 0
      unterbrochen := [] }

/-- The combined state over the mask state `m` with every core initial. -/
def anfangPrioMaske (m : CoreMask) : PrioMaske :=
  { maske := m
    prio := anfangPrio }

/-- Setting the mask bit of core `c` to `b`; the priorities are untouched. -/
def maskeSetze (s : PrioMaske) (c : Nat) (b : Bool) : PrioMaske :=
  { maske := aufKern s.maske c { (s.maske.zustand c) with maskiert := b }
    prio := s.prio }

/-- Raising core `c` to level `p`: set the mask bit to `maskNeu`, push the
    old level, install `p`. Leaving keeps the mask bit as is. -/
def erhoeheNach (s : PrioMaske) (c p : Nat) (maskNeu : Bool) : PrioMaske :=
  aufPrio (maskeSetze s c maskNeu) c (schiebePrio (s.prio c) p)

/-- Lowering core `c`: pop the head `alt` of its stack, keep the mask bit. -/
def senkeNach (s : PrioMaske) (c alt : Nat) (rest : List Nat) : PrioMaske :=
  aufPrio s c (nimmPrio alt rest)

/-- Raising installs the new level. -/
theorem erhoeheNachAktuell (s : PrioMaske) (c p : Nat) (b : Bool) :
    ((erhoeheNach s c p b).prio c).aktuell = p := by
  unfold erhoeheNach
  rw [aufPrioEq]
  rfl

/-- Raising pushes the old level on the stack. -/
theorem erhoeheNachStapel (s : PrioMaske) (c p : Nat) (b : Bool) :
    ((erhoeheNach s c p b).prio c).unterbrochen =
      (s.prio c).aktuell :: (s.prio c).unterbrochen := by
  unfold erhoeheNach
  rw [aufPrioEq]
  rfl

/-- Raising sets the mask bit to the entry parameter (both values). -/
theorem erhoeheNachMaske (s : PrioMaske) (c p : Nat) (b : Bool) :
    ((erhoeheNach s c p b).maske.zustand c).maskiert = b := by
  unfold erhoeheNach maskeSetze
  rw [aufPrioMaske, aufKernEq]

/-- Raising changes no other core's mask bit. -/
theorem erhoeheNachAndererMaske (s : PrioMaske) (c c' p : Nat) (b : Bool)
    (hne : c' ≠ c) :
    ((erhoeheNach s c p b).maske.zustand c').maskiert =
      (s.maske.zustand c').maskiert := by
  unfold erhoeheNach maskeSetze
  rw [aufPrioMaske]
  exact congrArg KernZustand.maskiert (aufKernAnderer s.maske c c' _ hne)

/-- Raising changes no other core's priority record. -/
theorem erhoeheNachAndererPrio (s : PrioMaske) (c c' p : Nat) (b : Bool)
    (hne : c' ≠ c) :
    (erhoeheNach s c p b).prio c' = s.prio c' := by
  unfold erhoeheNach maskeSetze
  rw [aufPrioAnderer _ _ _ _ hne]

/-- Lowering installs the popped level. -/
theorem senkeNachAktuell (s : PrioMaske) (c alt : Nat) (rest : List Nat) :
    ((senkeNach s c alt rest).prio c).aktuell = alt := by
  unfold senkeNach
  rw [aufPrioEq]
  rfl

/-- Lowering installs the remaining stack. -/
theorem senkeNachStapel (s : PrioMaske) (c alt : Nat) (rest : List Nat) :
    ((senkeNach s c alt rest).prio c).unterbrochen = rest := by
  unfold senkeNach
  rw [aufPrioEq]
  rfl

/-- Lowering keeps every core's mask bit, including the acting core. -/
theorem senkeNachMaske (s : PrioMaske) (c alt : Nat) (rest : List Nat)
    (c' : Nat) :
    ((senkeNach s c alt rest).maske.zustand c').maskiert =
      (s.maske.zustand c').maskiert := by
  unfold senkeNach
  rw [aufPrioMaske]

/-- Lowering changes no other core's priority record. -/
theorem senkeNachAndererPrio (s : PrioMaske) (c c' alt : Nat)
    (rest : List Nat) (hne : c' ≠ c) :
    (senkeNach s c alt rest).prio c' = s.prio c' := by
  unfold senkeNach
  rw [aufPrioAnderer _ _ _ _ hne]

/-- The L7b priority events, beside `MaskEvent`: raise core `c` to level
    `p` (with the entry mask bit `maskNeu`), or lower core `c`. -/
inductive PrioEvent
  | erhoehe : Nat → Nat → Bool → PrioEvent
  | senke : Nat → PrioEvent
  deriving DecidableEq

/-- The core an event acts on. -/
def prioKernVon : PrioEvent → Nat
  | PrioEvent.erhoehe c _ _ => c
  | PrioEvent.senke c => c

/-- One priority step: a handler of level `p` enters on core `c` only when
    the core is unmasked and `p` is strictly above the current level
    (equal levels are refused); entering pushes and installs; leaving pops
    the head of the stack and keeps the mask bit. -/
inductive PrioStep : PrioEvent → PrioMaske → PrioMaske → Prop where
  | erhoehe (s : PrioMaske) (c p : Nat) (maskNeu : Bool)
      (hmask : (s.maske.zustand c).maskiert = false)
      (hp1 : 1 ≤ p)
      (hgt : (s.prio c).aktuell < p) :
      PrioStep (PrioEvent.erhoehe c p maskNeu) s (erhoeheNach s c p maskNeu)
  | senke (s : PrioMaske) (c alt : Nat) (rest : List Nat)
      (hstapel : (s.prio c).unterbrochen = alt :: rest) :
      PrioStep (PrioEvent.senke c) s (senkeNach s c alt rest)

end Gabbro.Grammatik.Niedrig.Maske
