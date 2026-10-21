/-
  File:      Grammatik/Gen/Familie/ZellFamilie.lean
  Subject:   The DECLARATIONS for the CELLS (`Gen/Abdeckung/Zellen.lean`): members that the cell driver adds to the
             family, so that the sixteen members of `Familie.lean` -- and every measurement and theorem that quantifies
             over them -- stay as they are. A cell needs more than one function, a function with reasons, a function that
             holds a lock by signature, a floor, a masking lock next to a plain one, a guarded and an unguarded carrier,
             an atomic: each member below is plain `Spez` data, nothing about syntax.

  They are plain specifications, so every field the model reads is filled by `Spez.deklaration` and the four proof
  fields hold by construction (`Spez.lean`); no member is refused.
-/
import Grammatik.Gen.Familie.Familie

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

private def zu8 : Ty := .int 0 255
private def zb1 : Ty := .int 0 1
private def zi3 : Ty := .int 0 3

/-- A -- three functions over a guarded and an unguarded table, an atomic, a plain and a guarded static, a plain lock
    (rank 1) and a masking lock (rank 2): one that writes only unguarded carriers, one meant to take the plain lock, one
    meant to take the masking lock. The declared floor is the rank of the lock the function is meant to take; the
    language computes the floor from the body, so a body that takes another lock (or none) does not print and the
    unit is skipped by name. -/
def zA : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }], sperre := some 0, geteilt := true },
           { count := 2, felder := [{ typ := zi3 }] }]
  globs := [{ typ := zb1, atomar := true, geteilt := true }, { typ := zb1 },
            { typ := zb1, sperre := some 1, geteilt := true }]
  locks := [{ rang := 1 }, { rang := 2, maskiert := true }]
  sigs := [{ schreibt := [1], gschreibt := [1] },
           { boden := some 1, schreibt := [0] },
           { boden := some 2, gschreibt := [2] }]
  fns := [0, 1, 2]

/-- D -- a function with reasons (no root), one that holds a lock by signature AND has reasons, next to one that writes
    an unguarded table and an atomic. -/
def zD : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }] },
           { count := 2, felder := [{ typ := zi3 }], sperre := some 0, geteilt := true }]
  globs := [{ typ := zb1, atomar := true, geteilt := true }]
  locks := [{ rang := 1 }]
  sigs := [{ gruende := 2, erg := some zi3 }, { schreibt := [0], gschreibt := [0] },
           { haelt := [0], gruende := 2, erg := some zi3 }]
  fns := [0, 1, 2]

/-- E -- a device register whose state lives in an unguarded table (the register part of the footprint), two functions
    that write the table. -/
def zE : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }] }]
  regs := [{ typ := zi3, klasse := .rw, traeger := [0] }]
  sigs := [{ schreibt := [0] }, { schreibt := [0] }]
  fns := [0, 1]

/-- B -- two functions of one signature that write the same unguarded table and the same atomic (a pool and a race),
    a lock of rank 1 that masks, a foreign body with `never`. -/
def zB : Spez where
  tabs := [{ count := 2, felder := [{ typ := zb1 }] },
           { count := 2, felder := [{ typ := zb1 }], sperre := some 0, geteilt := true }]
  globs := [{ typ := zb1, atomar := true, geteilt := true }]
  locks := [{ rang := 1, maskiert := true }]
  axs := [{ erg := some .never }, { schreibt := [0], gschreibt := [0] }]
  sigs := [{ schreibt := [0], gschreibt := [0] }, { haelt := [0] }]
  fns := [0, 0, 1]

/-- C -- a table guarded by a lock and an invariant over it, a second guarded by another lock, registers whose carrier is
    a table (the register part of the footprint), two functions. -/
def zC : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }], sperre := some 0, geteilt := true },
           { count := 2, felder := [{ typ := zb1 }], sperre := some 1, geteilt := true }]
  locks := [{ rang := 1 }, { rang := 2 }]
  regs := [{ typ := zi3, klasse := .rw, traeger := [0] }, { typ := zb1, klasse := .r, traeger := [1], zusage := false }]
  invs := [{ traeger := [0, 1] }]
  sigs := [{ schreibt := [0], haelt := [0, 1] }, { schreibt := [1], haelt := [1] }]
  fns := [0, 1]

/-- **The members the cell driver adds** to `familie`. -/
def zellFamilie : List Spez := [zA, zB, zC, zD, zE]

/-! ## Members from RULES

  The members above are written by hand. These are generated: one fixed basis of carriers, locks and registers, and
  a MENU of signatures DERIVED from it (every held lock set times every write target, the floor the one the language
  derives); a member is a list of one or two functions, each one signature of the menu (two of one signature make a
  pool), in non-decreasing order so that no permutation is counted twice. Nothing about syntax is written: a
  member is plain `Spez` data, the bodies come from the generator, the text from the printer. -/

/-- The carriers and locks every rule member shares, all of type `bool` (the cells read no value): an unguarded and
    a guarded table, an unguarded shared atomic, a plain static, an atomic guarded by the plain lock, a static guarded
    by the masking lock; a plain lock of rank 1 and a masking lock of rank 2; a device register whose state lives in
    the guarded table and a readable register of an EMPTY type. -/
def regelBasis : Spez where
  tabs := [{ count := 2, felder := [{ typ := .bool }] },
           { count := 2, felder := [{ typ := .bool }], sperre := some 0, geteilt := true }]
  globs := [{ typ := .bool, atomar := true, geteilt := true }, { typ := .bool },
            { typ := .bool, atomar := true, sperre := some 0, geteilt := true },
            { typ := .bool, sperre := some 1, geteilt := true }]
  locks := [{ rang := 1 }, { rang := 2, maskiert := true }]
  regs := [{ typ := .bool, klasse := .rw, traeger := [1] }, { typ := .int 1 0, klasse := .r }]

/-- What a signature may write: nothing, one carrier of the basis, or both tables (tables, statics). -/
def regelZiele : List (List Nat × List Nat) :=
  [([], []), ([0], []), ([1], []), ([], [0]), ([], [1]), ([], [2]), ([], [3]), ([0, 1], [])]

/-- The locks that guard what a signature writes, read off the basis. -/
def regelWaechter (z : List Nat × List Nat) : List Nat :=
  (z.1.filterMap fun t => (regelBasis.tabs.getD t { count := 0, felder := [] }).sperre) ++
  (z.2.filterMap fun g => (regelBasis.globs.getD g { typ := .bool }).sperre)

/-- The floor a body writing `z` while holding `h` derives: the least rank of a guard it must take. -/
def regelBoden (z : List Nat × List Nat) (h : List Nat) : Option Int :=
  ((regelWaechter z).filter (!h.contains ·)).foldl (fun a L =>
    let r := (regelBasis.locks.getD L { rang := 0 }).rang
    match a with | none => some r | some m => some (min m r)) none

/-- **The menu of signatures**, derived from the basis: every lock set a function may hold (none, either lock) times
    every write target, the declared floor the one the language derives from such a body; and one reason channel. -/
def regelSigs : List SigZ :=
  ([[], [0], [1]].flatMap fun h => regelZiele.map fun z =>
    { haelt := h, schreibt := z.1, gschreibt := z.2, boden := regelBoden z h }) ++
  [{ gruende := 2, erg := some .bool }]

/-- The multisets of `k` indices below `n`, as non-decreasing lists. -/
def multimengen : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, n => (List.range n).flatMap fun a => (multimengen k n).filterMap fun r =>
      if r.all (a ≤ ·) then some (a :: r) else none

/-- **The rule members**: every list of one or two functions over the menu (two of one signature make a pool). -/
def regelMitglieder : List Spez :=
  ((List.range 2).flatMap fun k => multimengen (k + 1) regelSigs.length).map fun fns =>
    { regelBasis with sigs := regelSigs, fns := fns }

end Gabbro.Grammatik.Gen
