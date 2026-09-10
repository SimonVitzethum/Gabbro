/-
  File:     Grammatik/Adressraum.lean
  Subject:  **The user/kernel boundary as a shape** -- the design piece that
             `messung/TOCTOU-ADRESSRAUM.md` finds missing (verdict GAP).

             SYNTAX §3 has six spaces and no user one; `Ty.ptr` drops the space;
             `Expr.durch` is one read with one guard set; `World` (both the
             grammar's and `Body.lean`'s) is a single flat mapping; M3 holds
             rights and placement and never check-then-copy. So a `copy_from_user`
             shape -- validate a user range, then copy from it, while the user
             side may rewrite the bytes between the two reads -- is neither
             writable, statable, nor refused anywhere.

             This file draws the shape and nothing else: defs only, no theorems,
             no proofs. What it gives:

               `Seite`         -- the two sides of one boundary.
               `UserRegion`    -- a user-memory region: base plus length.
               `Richtung`      -- which way the bytes move (`vonUser` is the
                                  `copy_from_user` shape).
               `Kopie`         -- the copy primitive: user address, kernel
                                  address, byte count, direction, in ONE datum.
               `innerhalb`     -- the check, as a Prop: the accessed range lies
                                  inside the region.
               `GepruefteKopie`-- validation-then-copy, inseparable: the check
                                  and the copy name the SAME region, address,
                                  and length. A check over one triple paired
                                  with a copy over another is not of this shape.
               `Lesung` / `PruefDannKopie` -- the TOCTOU sequence: the checked
                                  reading and the copied reading, as two data.
               `ohneToctou`    -- the soundness shape, as a Prop: the checked
                                  value IS the copied value -- one snapshot,
                                  read once. A sequence whose two readings can
                                  differ has this property nowhere.
               `KernAnweisung` / `kreuzt` -- boundary-crossing statement shapes:
                                  a kernel step is pure or carries exactly one
                                  copy; crossing is an existential over the term.

             Mirror (standalone -- the lane forbids editing the `Grammatik.lean`
             index, so this file takes no import, not even the siblings; names
             are chosen to wire up later):

             | here                | there                                        |
             |---------------------|----------------------------------------------|
             | `UserRegion`        | the missing seventh `space` (SYNTAX §3)      |
             | `Kopie`             | the missing copy primitive (no `Expr` ctor)  |
             | `GepruefteKopie`    | the missing rule (no M3 rule fires on it)    |
             | `ohneToctou`        | the missing statement (one flat `World`)     |
             | `Nat` addresses     | wiring: byte offsets into `Tab`/`Glob` later |

             CUTS (booked, not hidden):
             C1. Addresses and values are `Nat`: placeholders for byte offsets
                 and byte strings. The wiring replaces them with `Tab` slots /
                 `Byte` lists (`Typen.lean`: `Byte`, `bytesZuZahl`).
             C2. No clock: `PruefDannKopie` orders the two readings by position
                 (check first, copy second), not by time. A writer between them
                 is the environment, named as an assumption like `Hardware.*`.
             C3. One copy per statement: a loop copying a range chunk by chunk
                 is `n` terms of this shape, each checked -- that per-chunk
                 check is exactly what the shape demands.
             C4. `vonUser` only is the hazard direction. `nachUser` shares the
                 datatype so the check is not skipped on the way out; the
                 TOCTOU reading hazard runs check-then-copy from user.

             Core only: no `mathlib`, no import at all. Zero `sorry`.
-/

namespace Gabbro.Grammatik.Adressraum

/-! ## 1. The two sides, and the region the far side lives in -/

/-- The two sides of one boundary: kernel memory and user memory. -/
inductive Seite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- A region of user memory: base plus length, both in bytes (cut C1). -/
structure UserRegion where
  basis : Nat
  laenge : Nat
  deriving DecidableEq, Repr

/-- Which way the bytes move across the boundary. -/
inductive Richtung where
  /-- `copy_from_user` shape: kernel reads user bytes. -/
  | vonUser
  /-- `copy_to_user` shape: kernel writes user bytes. -/
  | nachUser
  deriving DecidableEq, Repr

/-! ## 2. The copy primitive: validation-then-copy, inseparable -/

/-- One boundary-crossing copy: the user address, the kernel address, the byte
    count, and the direction -- in ONE datum, so no half of it can travel
    without the rest. -/
structure Kopie where
  userAddr : Nat
  kernAddr : Nat
  laenge : Nat
  richtung : Richtung
  deriving DecidableEq, Repr

/-- The check: the whole `[addr, addr + laenge)` lies inside the region. -/
def innerhalb (r : UserRegion) (addr laenge : Nat) : Prop :=
  r.basis ≤ addr ∧ addr + laenge ≤ r.basis + r.laenge

/-- The validation: the copy's user range lies inside the region. -/
def validiert (r : UserRegion) (k : Kopie) : Prop :=
  innerhalb r k.userAddr k.laenge

/-- Validation-then-copy: the check and the copy name the SAME region,
    address, and length. A check over one triple paired with a copy over
    another is not of this shape -- that pairing is the TOCTOU below. -/
structure GepruefteKopie where
  region : UserRegion
  kopie : Kopie
  gecheckt : validiert region kopie

/-- The checked triple, read back off the shape: what was validated is what
    is copied, by construction. -/
def GepruefteKopie.bereich (g : GepruefteKopie) : Nat × Nat :=
  (g.kopie.userAddr, g.kopie.laenge)

/-! ## 3. The TOCTOU sequence: two readings, one check between them -/

/-- One reading of user memory: the address and the value seen (cut C1: the
    value is one `Nat` standing for the byte string). -/
structure Lesung where
  addr : Nat
  wert : Nat
  deriving DecidableEq, Repr

/-- The check-then-copy sequence: the checked reading first, the copied
    reading second (cut C2: order by position, not by time). -/
structure PruefDannKopie where
  pruefung : Lesung
  kopie : Lesung
  deriving DecidableEq, Repr

/-- No TOCTOU: the checked value IS the copied value -- one snapshot, read
    once. A sequence whose two readings can differ has this property nowhere;
    holding it means the copy did not re-read mutable bytes. -/
def ohneToctou (s : PruefDannKopie) : Prop :=
  s.pruefung = s.kopie

/-- The snapshot reading: the single address both readings agree on. Only
    meaningful where `ohneToctou` holds; stated separately so the shape, not
    a proof, carries the address. -/
def snapshotAddr (s : PruefDannKopie) : Nat :=
  s.pruefung.addr

/-! ## 4. Boundary-crossing statement shapes -/

/-- A kernel statement: either pure (no crossing) or exactly one copy
    (cut C3: a chunked loop is `n` terms of this shape). -/
inductive KernAnweisung where
  | rein : KernAnweisung
  | kopie : Kopie → KernAnweisung
  deriving DecidableEq, Repr

/-- A statement crosses the boundary exactly when it carries a copy. -/
def kreuzt : KernAnweisung → Prop
  | .rein => False
  | .kopie _ => True

/-- The carried copy, where there is one: which bytes cross, and which way. -/
def getrageneKopie : KernAnweisung → Option Kopie
  | .rein => none
  | .kopie k => some k

/-- A crossing statement with its validation: the statement, the region it
    was checked against, and the check -- the three travel together, as in
    `GepruefteKopie` above. -/
structure GepruefterUebergang where
  anweisung : KernAnweisung
  region : UserRegion
  kopie : Kopie
  traegt : getrageneKopie anweisung = some kopie
  gecheckt : validiert region kopie

end Gabbro.Grammatik.Adressraum
