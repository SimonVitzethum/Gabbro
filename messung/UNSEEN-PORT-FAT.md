# The Unseen Port — FAT16 geometry + CRC32 from `caprock-part`/`caprock-fat`

*Ported 2026-09-03. Source: `../caprock-messbasis/crates/caprock-fat/src/lib.rs`
(`parse_boot`, 60 lines) and `../caprock-messbasis/crates/caprock-part/src/lib.rs`
(`Crc32::update`, 8 lines). The port author had never opened `beispiele/03-format.gab`
or `beispiele/37-umlauf-rechnet.gab` before attempt 1; every friction below was
recorded at first contact. Attempt = one `gabbro check` run.*

## Result

**8 attempts, 5 files, 2 green.** The geometry reader (`fat-reader2`) checks with
`0 errors, 0 hints`, emits C, and the C compiles under
`cc -std=c11 -Wall -Wextra -Werror -O2`. The CRC32 inner loop does NOT port:
the idiom it is written in (`wrapping_neg` mask, `for _ in 0..8`, `^=`) has no
word in Gabbro, and the workarounds cost more refusal cycles than the loop is
worth. That is the finding, not a failure to finish.

## Attempt log

| # | file | result | what the checker taught |
|---|------|--------|-------------------------|
| 1 | `fat-port` (`format BootGeo`) | 2 errors (`P001` typo — mine, `P006` follow-on) | `format` tiles from offset 0; no field-at-byte-510. Fix: typo only, then green |
| 2 | `fat-reader` (`where`, `let..else`, `spc & (spc-1)`) | 3 errors (`P001`, `M104`, `M119`) | `let … else (e) { … }` needs the channel; `u8 - u8` underflows the WIDTH, not the value — ranges belong at declaration |
| 3 | `fat-reader2` (ranged operands, `narrow`, wider-bind) | 1 error (`K001`: body costs 11, promised 8) | `gabbro costs` computes the number; the promise copies it. Fixed to 11 → **GREEN, emits, `cc -O2` clean** |
| 4 | `crc` (guessed `for`, `^=`, `wrapping` annotation, `u32` suffix) | 5 errors (`L003`, `P001`, `P017`, `P035`, `M119`) | four refusals in one file: no `for` (only `traverse`/`retry`/`forever`), no `^=`, no suffix, `wrapping` is not a `let` annotation |
| 5 | `crc2` (`retry`, `wrapping` params, `let mut`) | 1 error (`P001`: `wrapping` not a param annotation) | `wrapping` lives ONLY on slot/reg declarations (`SYNTAX.md`: `slottype`, `regdecl`), never on locals or params |
| 6–7 | `crc3`–`crc4` (table-slot carrier for the wrap word) | `M104` (`0 - bit0` leaves `u32`), `K006` (pass costs 10 > `bounded 8`) | the mask idiom `(x & 1).wrapping_neg()` is inexpressible: negation of a `u32` is untypable, and there is no branch-free substitute |
| 8 | `crc7` (`if bit0 == 1 { return POLY; } return 0;`) | **GREEN** | the branch version of the mask checks. The loop around it (attempt 5 shape) was not re-attempted — see §3 |

## The three frictions, ordered by weight

**F1 — `wrapping` is storage-only.** `u32 wrapping` exists on `slot` and `reg`
fields and nowhere else: not on params, not on returns, not on `let`. A checksum
loop carries its state in a LOCAL, so the one word that would make `0 - bit0`
definiert cannot name it. Workaround (table with one slot as the carrier) parses
but moves the state through `t.slots[0].w` at every step — five tokens where Rust
writes `z`. *Verdict: S5-shaped (small, measured, one rule). Either `wrapping`
on `let`, or a named refusal that says so.*

**F2 — no counted loop.** `for _ in 0..8` is `P035`: three loop forms and only
these. `retry … bounded 80 ops … on_exceeded <never-fn>` expresses "8 passes"
only by paying for a divergence exit that cannot fire (`crc_gibt_auf`) plus an
`assume`-less `progress`-free shape the checker accepts but the reader has to
learn. Eight CRC rounds are not a retry; calling them one is honest (the bound
holds) but unreadable. *Verdict: S5-shaped. A `repeat N times` sugar over
`retry` — same checks, no new semantics — would have ended this port in
attempt 5.*

**F3 — sub-slice reads have no word.** `rd16(sector, 11)`, `crc32(&h[..92])`,
`entry_at(h, &e[off..end], …)` all read bytes `[a..b]` of a buffer at an
ARBITRARY offset. `format` tiles from 0 and the reader enters through the
header type — which is the F10 verdict and the right default — but a parser
that holds the sector AND the header side by side (caprock-part does: it
reseals `h[16..20]` in place) has no expression for the second view.
*Verdict: S2-adjacent (expressiveness, not plumbing). Named, not built:
Rule A — one port is demand, not a census.*

## What ported cleanly (the control)

* `name83` length/uppercase rule → ordinary body code (`beispiele/32` shape).
* `dir_entry_at`/`entry_at` chunk discipline ("never half an entry") →
  `requires` + `narrow … else { return None; }`.
* `parse_boot` range table (8 error kinds) → `reason GeoFehler` + `where`/`in`
  on fields, one per line. The `checked_add` chain becomes wider-bind
  (`let a : u64 = fat_lba;`) — the checker's own suggestion, and it emits.
* Every refusal message taught its repair: `P001` names the expected token,
  `M104` names both ways out, `K001`/`K006` print computed vs promised,
  `P035` lists the three loop forms. **Zero dead attempts** — the eight
  runs form a chain, each fixing exactly what the previous one named.

## What this re-evaluates on the Beta list (§50)

*Nothing structural.* B1/B2/B3 stand: the port used `gabbro new` + TUTORIAL
shape (attempt 3 is the TUTORIAL §6/`costs` loop verbatim) and never needed a
C driver. The two S5 items (`if`-as-expression was NOT needed — the statement
form sufficed; `wrapping` on `let` — F1 above) gain one measured demand each
without changing order: F1/F2 are the cheapest open language posts with a
foreign witness now attached. F3 joins S2's queue with a count of 1.
