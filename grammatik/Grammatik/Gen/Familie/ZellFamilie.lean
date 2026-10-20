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

/-- A -- three functions over a guarded and an unguarded table, an atomic and a plain static, a plain lock (rank 1) and a
    masking lock (rank 2): a function that writes only unguarded carriers, one that holds the plain lock by signature
    (so it is no root), one with a floor above the plain lock (taking the plain lock breaks the floor). -/
def zA : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }], sperre := some 0, geteilt := true },
           { count := 2, felder := [{ typ := zi3 }] }]
  globs := [{ typ := zb1, atomar := true, geteilt := true }, { typ := zb1 },
            { typ := zb1, sperre := some 1, geteilt := true }]
  locks := [{ rang := 1 }, { rang := 2, maskiert := true }]
  sigs := [{ schreibt := [1], gschreibt := [1] },
           { haelt := [0], schreibt := [0] },
           { boden := some 2 }]
  fns := [0, 1, 2]

/-- D -- a function with reasons (no root), one that holds a lock by signature AND has reasons, next to one that writes
    an unguarded table and an atomic. -/
def zD : Spez where
  tabs := [{ count := 2, felder := [{ typ := zi3 }] },
           { count := 2, felder := [{ typ := zi3 }], sperre := some 0, geteilt := true }]
  globs := [{ typ := zb1, atomar := true, geteilt := true }]
  locks := [{ rang := 1 }]
  sigs := [{ gruende := 2 }, { schreibt := [0], gschreibt := [0] }, { haelt := [0], gruende := 2 }]
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

end Gabbro.Grammatik.Gen
