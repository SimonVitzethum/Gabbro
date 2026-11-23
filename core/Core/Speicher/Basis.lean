/-
  File:      core/Core/Speicher/Basis.lean
  Subject:   THE AXIOMATIC MEMORY MODEL W, part 1: access modes, event labels, execution graphs and
             the relation algebra (closure, acyclicity) the consistency axioms are written in.

  WHY AXIOMATIC (PERFECT-MODEL §3.4/§3.5, step M3). `seq_cst` must be truly sequentially consistent
  and `acquire`/`release`/`relaxed` must have exactly their RC11 outcomes with `po ∪ rf` acyclic.
  A promise-free view machine (timestamps per location, views per thread) cannot carry RC11's
  `seq_cst`: forcing an SC read
  to take the newest message is STRONGER than RC11 on mixed programs (it forbids an outcome RC11 and
  Armv8 allow: `T1: r1 = y.rlx; x.sc = 1 ‖ T2: z.sc = 1; y.rlx = 1 ‖ T3: r3 = x.sc; r4 = z.sc` with
  `r1 = r3 = 1, r4 = 0`), and treating it as release/acquire is weaker (store buffering). The
  axiomatic formulation of Lahav, Vafeiadis, Kang, Hur, Dreyer, "Repairing sequential consistency in
  C/C++11" (PLDI 2017) is exact by construction, and the in-order execution of its graphs is
  recovered by the prefix lemma (`Praefix.lean`): with `po ∪ rf` acyclic every consistent graph is
  produced event by event in program order, every prefix consistent.

  Fences are not part of the fragment: the language has no fence form (the order of an access is
  the mode of its location). They are added together with a fence form.

  OUTSIDE EVENTS. Both machines of M4 -- the implementation machine and the ideal meaning `I` --
  record their runs as graph events: a context (thread, handler, core), a location, a mode and a
  value (`Graphmaschine.lean`). Besides memory accesses a run has outside and device events
  (catalogue questions and answers, device register accesses, interrupts): events of kind
  `aussen`, ordered by program order like every event, neither reading nor writing memory, their
  location and value naming the outside object and the datum (M4 chooses `Ort` and `Wert`).
-/
module

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **The access mode of a location.** Gabbro fixes ONE mode per carrier by its declaration:
    `na` a plain carrier, `rlx` a `relaxed` atomic (or one without an ordering word), `ra` an
    `acquire`/`release` atomic (release stores, acquire loads, acq_rel read-modify-writes), `sc` a
    `seq` atomic (`seq_cst` on every access). -/
inductive Modus where
  | na
  | rlx
  | ra
  | sc
  deriving DecidableEq, Repr

namespace Modus

/-- Atomic (RC11's `⊒rlx`): every mode but `na`. -/
def atomar : Modus → Prop
  | na => False
  | rlx => True
  | ra => True
  | sc => True

/-- At least release/acquire (RC11's `⊒rel` on writes, `⊒acq` on reads). -/
def stark : Modus → Prop
  | na => False
  | rlx => False
  | ra => True
  | sc => True

theorem stark_atomar {m : Modus} (h : m.stark) : m.atomar := by
  cases m with
  | na => exact False.elim h
  | rlx => exact False.elim h
  | ra => exact trivial
  | sc => exact trivial

theorem atomar_ne_na {m : Modus} (h : m.atomar) : m ≠ na := by
  intro e
  subst e
  exact h

end Modus

/-- **The kind of an event**: a read, a write, an update (a read-modify-write: one event that
    reads and writes, RC11's `U`), or an outside event (a catalogue question or answer, a device
    access, an interrupt: in program order, but neither a read nor a write of memory). -/
inductive Art where
  | lesen
  | schreiben
  | rmw
  | aussen
  deriving DecidableEq, Repr

namespace Art

/-- The event reads. -/
def liest : Art → Prop
  | lesen => True
  | schreiben => False
  | rmw => True
  | aussen => False

/-- The event writes. -/
def schreibt : Art → Prop
  | lesen => False
  | schreiben => True
  | rmw => True
  | aussen => False

end Art

/-- **The label of an event**: kind, location, mode, the value read (meaningful for reads and
    updates) and the value written (meaningful for writes and updates). -/
structure Etikett (Ort Wert : Type) where
  art : Art
  ort : Ort
  modus : Modus
  gelesen : Wert
  geschrieben : Wert

/-- **An execution graph**: labelled events with program order `po`, reads-from `rf` (from a
    write to a read) and modification order `mo`. Initial values are ordinary write events. The
    shape conditions are `Wohlgeformt` (Relationen.lean). -/
structure Graph (E Ort Wert : Type) where
  lab : E → Etikett Ort Wert
  po : E → E → Prop
  rf : E → E → Prop
  mo : E → E → Prop

/-! ## Relation algebra -/

section Relationen

variable {E : Type}

/-- A relation is acyclic: its transitive closure is irreflexive. -/
def Azyklisch (r : E → E → Prop) : Prop := ∀ a, ¬ Relation.TransGen r a a

theorem transGen_mono {r s : E → E → Prop} (h : ∀ a b, r a b → s a b) {a b : E}
    (hr : Relation.TransGen r a b) : Relation.TransGen s a b := by
  induction hr with
  | single h1 => exact .single (h _ _ h1)
  | tail _ h2 ih => exact .tail ih (h _ _ h2)

theorem azyklisch_mono {r s : E → E → Prop} (h : ∀ a b, r a b → s a b) (hs : Azyklisch s) :
    Azyklisch r := fun a ha => hs a (transGen_mono h ha)

/-- The closure of a transitive relation is the relation itself. -/
theorem transGen_von_trans {r : E → E → Prop} (ht : ∀ a b c, r a b → r b c → r a c) {a b : E}
    (h : Relation.TransGen r a b) : r a b := by
  induction h with
  | single h1 => exact h1
  | tail _ h2 ih => exact ht _ _ _ ih h2

/-- A rank that every edge increases makes a relation acyclic. -/
theorem azyklisch_von_rang {r : E → E → Prop} (f : E → Nat) (h : ∀ a b, r a b → f a < f b) :
    Azyklisch r := by
  have hlt : ∀ a b, Relation.TransGen r a b → f a < f b := by
    intro a b hab
    induction hab with
    | single h1 => exact h _ _ h1
    | tail _ h2 ih => exact Nat.lt_trans ih (h _ _ h2)
  exact fun a ha => Nat.lt_irrefl _ (hlt a a ha)

/-- Closure commutes with a map that carries every edge. -/
theorem transGen_abbild {F : Type} {r : F → F → Prop} {s : E → E → Prop} (g : F → E)
    (h : ∀ a b, r a b → s (g a) (g b)) {a b : F} (hr : Relation.TransGen r a b) :
    Relation.TransGen s (g a) (g b) := by
  induction hr with
  | single h1 => exact .single (h _ _ h1)
  | tail _ h2 ih => exact .tail ih (h _ _ h2)

/-- Acyclicity is reflected along a map that carries every edge. -/
theorem azyklisch_abbild {F : Type} {r : F → F → Prop} {s : E → E → Prop} (g : F → E)
    (h : ∀ a b, r a b → s (g a) (g b)) (hs : Azyklisch s) : Azyklisch r :=
  fun a ha => hs (g a) (transGen_abbild g h ha)

/-- The first edge of a closure path. -/
theorem transGen_kopf {r : E → E → Prop} {a b : E} (h : Relation.TransGen r a b) :
    ∃ c, r a c := by
  induction h with
  | single h1 => exact ⟨_, h1⟩
  | tail _ _ ih => exact ih

/-- The last edge of a closure path. -/
theorem transGen_ende {r : E → E → Prop} {a b : E} (h : Relation.TransGen r a b) :
    ∃ c, r c b := by
  cases h with
  | single h1 => exact ⟨_, h1⟩
  | tail _ h2 => exact ⟨_, h2⟩

end Relationen

end Gabbro.Core.Speicher
