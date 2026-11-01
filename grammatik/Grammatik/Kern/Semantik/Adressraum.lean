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

              This file draws the shape and proves what the shape carries:
              a checked copy run as ONE copy through the checked handle shows
              no check-then-copy TOCTOU -- under the single-copy-atomicity
              premise `EinSnapshot`, named explicitly (the Koernung shape:
              `Koernung.lean` runs one event indivisibly; here check and copy
              are one indivisible copy). An unvalidated crossing runs in the
              same sequence shape with the premise dropped -- the named gap.
              What it gives:

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
                `UserMem` / `laufSequenz` -- the run: check-time and copy-time
                                   snapshots feeding the checked handle.
                `EinSnapshot`   -- the premise, named explicitly: both
                                   snapshots agree at the checked address
                                   (single-copy atomicity, Koernung shape).
               safety / gap    -- `gepruefteKopie_ohneToctou` under the
                                    premise; `toctouZeuge_toctou` and
                                    `laufSequenz_toctou_ohneSnapshot` name
                                    the gap without it.
               wiring (§7)     -- `weltByte`/`weltBytes` read the checked
                                    address out of `World` (the same
                                    `World.bytesAb` the `leseBytes` read
                                    path binds); `schreibSlot_liestSelbe`
                                    lands the write where the read looks;
                                    `modellSequenz_ohneToctou` proves the
                                    safety INSIDE the model, and
                                    `modellSequenz_toctou_ohneSnapshotWelt`
                   names the gap there. The region check
                   itself (`validiert`) still has no `exec`
                   counterpart -- that is cut C6, not §7.
                partition (§8, design only, no discharge) -- `KernRegion` /
                    `SeitenRegion` name both sides of `Seite`; `execFordertBereich`
                    is the range-check-inside-`exec` shape (out-of-region refuses
                    as `ausserhalbVerweigert`); `adresseInRegion` /
                    `schluesselInRegion` / `benutzerTeil` hang the user side of
                    the world mapping on `UserRegion`, `bereicheGetrennt` names
                    the split. No transition discharges any of it -- cut C7.

              Mirror (this file takes one same-project import,
              `Grammatik.Semantik`; the `Grammatik.lean` index is untouched,
              so the file wires itself -- names were chosen for this):

             | here                | there                                        |
             |---------------------|----------------------------------------------|
             | `UserRegion`        | the missing seventh `space` (SYNTAX §3)      |
             | `Kopie`             | the missing copy primitive (no `Expr` ctor)  |
             | `GepruefteKopie`    | the missing rule (no M3 rule fires on it)    |
              | `ohneToctou`        | the missing statement (one flat `World`)     |
               | `Nat` addresses     | wiring: byte offsets into a byte carrier     |
               |                     | (§7: `weltByte` over `World.bytesAb`)        |
               | `EinSnapshot`       | the atomic event (`Koernung.lean`: `EreignisAtomar`)|

              CUTS (booked, not hidden):
              C1. Addresses and values are `Nat`: placeholders for byte offsets
                  and byte strings. §7 wires ONE byte carrier: a `Nat` address
                  is the `Int` index into a table field typed `.int 0 255`
                  (`Typen.lean`: `Byte`), read through `World.bytesAb` --
                  the same function the `leseBytes` read path binds. Every
                  other carrier (all remaining `Tab` slots / `Glob`s) is
                  still unwired.
              C2. No clock: `PruefDannKopie` orders the two readings by position
                  (check first, copy second), not by time. A writer between them
                  is the environment, named as an assumption like `Hardware.*`.
                  §7 keeps this: the two model reads take two worlds, and
                  nothing in `exec` orders them.
              C3. One copy per statement: a loop copying a range chunk by chunk
                  is `n` terms of this shape, each checked -- that per-chunk
                  check is exactly what the shape demands.
               C4. `vonUser` only is the hazard direction. `nachUser` shares the
                   datatype so the check is not skipped on the way out; the
                   TOCTOU reading hazard runs check-then-copy from user.
                   Wiring (§7): `vonUser` is the read path (`bytesAb`, as in
                   `eval`'s `leseBytes` branch); `nachUser` is the write path
                   (`schreibSlot`/`schreibBytes`, as in `execStmt`).
               C5. No writer modelled: `m₁`/`m₂` are check-time/copy-time
                   snapshots; `EinSnapshot` says they agree at the checked
                   address. A writer between them is environment (like
                   `Hardware.*`), never a transition here. One `Nat` per
                   address again (cut C1, at the run): no byte-list wiring.
                   §7 carries this over: `σ₁`/`σ₂` are two worlds, and
                   `EinSnapshotWelt` says they agree at the checked byte.
               C6. The region check is still beside `exec`: `World` is one
                   flat mapping with no `Seite`, and no `Stmt`/`Block`
                   transition discharges `validiert` -- an out-of-region
                   `Kopie` still reads and writes in the model, because the
                   model memory is total. The Adressraum side is closed
                   (§9): a step shape whose transition requires `validiert`
                   (`BereichSchritt.geprueft` carries `h`, the `Stmt`
                   premise style), an executable check with its holds-lemma,
                   Seite-tagged reading of the world mapping, and the
                   validated copy run through the model write path. What
                   remains is the Semantik side: an `exec` branch taking
                   such a step, and a `Seite` partition in `World`.
               C7. The discharge inside `exec` stays future work (§8 books the
                   shape, not the transition): no `Stmt`/`Block` transition
                   requires `execFordertBereich`, and no `World` carries a
                   `Seite` partition yet -- `benutzerTeil`/`bereicheGetrennt`
                   name the user side it could check against.

               Core only: no `mathlib`; one same-project import
               (`Grammatik.Semantik`), no new dependency. Zero `sorry`,
               no `admit`, no new `axiom`. `#print axioms` below shows §§1-6
               rest on nothing; §7 rests on Lean core only (`propext`,
               `Classical.choice`, `Quot.sound`) -- the same baseline every
               `Semantik`-based file of the project shows, carried by the
               `World` types, not by any proof step here.
-/
module

public import Grammatik.Kern.Semantik.Adressraum.Teil1
public import Grammatik.Kern.Semantik.Adressraum.Teil2
