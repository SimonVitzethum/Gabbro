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

  The members above are written by hand. These are generated: one fixed set of carriers and locks (an unguarded and a
  guarded table, an atomic, a plain static, an atomic guarded by the plain lock, a static guarded by the masking lock; a
  plain lock of rank 1 and a masking lock of rank 2, each protecting something) and a MENU of signatures; a member is a
  list of one to three functions, each one signature of the menu (repetitions allowed: two functions of one signature
  make a pool), in non-decreasing order so that no permutation is counted twice. Nothing about syntax is written: a
  member is plain `Spez` data, the bodies come from the generator, the text from the printer. -/

/-- The carriers and locks every rule member shares. -/
def regelBasis : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }] },
           { count := 2, felder := [{ typ := zi3 }], sperre := some 0, geteilt := true }]
  globs := [{ typ := zb1, atomar := true, geteilt := true }, { typ := zb1 },
            { typ := zb1, atomar := true, sperre := some 0, geteilt := true },
            { typ := zb1, sperre := some 1, geteilt := true }]
  locks := [{ rang := 1 }, { rang := 2, maskiert := true }]

/-- **The menu of signatures** (index = position). A declared floor is the rank of the lock the function is meant to
    take, which is what the language derives from such a body. -/
def regelSigs : List SigZ :=
  [{},                                                       -- 0 nothing
   { schreibt := [0], gschreibt := [1] },                    -- 1 unguarded table and plain static
   { gschreibt := [0] },                                     -- 2 the atomic
   { boden := some 1, schreibt := [1] },                     -- 3 guarded table, takes the plain lock
   { haelt := [0], schreibt := [1] },                        -- 4 guarded table, holds the plain lock
   { boden := some 2, gschreibt := [3] },                    -- 5 static of the masking lock, takes it
   { boden := some 1, gschreibt := [2] },                    -- 6 atomic guarded by the plain lock, takes it
   { schreibt := [0], gschreibt := [0] },                    -- 7 unguarded table and the atomic
   { haelt := [1], gschreibt := [3] },                       -- 8 static of the masking lock, holds it
   { gruende := 2, erg := some zi3 },                        -- 9 a reason channel
   { boden := some 1, schreibt := [0, 1] }]                  -- 10 both tables, takes the plain lock

/-- The multisets of `k` indices below `n`, as non-decreasing lists. -/
def multimengen : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, n => (List.range n).flatMap fun a => (multimengen k n).filterMap fun r =>
      if r.all (a ≤ ·) then some (a :: r) else none

/-- **The rule members**: every list of one to three functions over the menu. -/
def regelMitglieder : List Spez :=
  ((List.range 3).flatMap fun k => multimengen (k + 1) regelSigs.length).map fun fns =>
    { regelBasis with sigs := regelSigs, fns := fns }

end Gabbro.Grammatik.Gen
