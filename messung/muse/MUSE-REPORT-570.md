# MUSE-REPORT-570: Source world/table values to target byte representation

Lane 570, branch `muse/570`, clone `/home/simon/Dokumente/gabbro-muse/a570`.
Owned files only: `grammatik/Grammatik/X86/SourceMemory.lean` (new, 594 lines),
`grammatik/Grammatik.lean` (one added import line), this report.
6 lane commits on the branch (skeleton → admission → frames → main → witness
defs → witness theorem); no other branches touched, no push, no network.

## What was delivered

The ONE small generic representation interface between real source
`Deklaration`/`World` table carriers and accepted `TableLayout`/`Speicher`
bytes, for the bounded integer fragment (one `.int lo hi` slot as one
little-endian 8-byte word). No new IR, no changed source semantics, no
checker/Spec/goal/emitter edits, no friend-optimizer edits.

Definitions (`grammatik/Grammatik/X86/SourceMemory.lean`):

- `zahlWort`, `wortZahl` — source value ↔ target word maps.
- `repOk` — the ONE checked admission Bool: range (`0 <= lo`,
  `hi < 2 ^ 64`), width (`.int` only), region (8-byte slot fits the entry
  extent, no 64-bit wrap). Any Rust layout hint is re-decided against it.
- `feldOff`, `slotOff`, `slotAddr` — slot byte offset/address from the
  accepted `typWeite`/`zeilenWeite`/`TabLayout` vocabulary.
- `RepSlot` — THE representation: `read64 m a = some (zahlWort value)`.
  Stable producer/consumer interface: the compiler establishes it per slot
  write; validator/TSO bridge consume only this equation plus decided Bools.
- Witness data: `witD` (one table, one `.int 0 100` field, one writing
  function), `witSig`, `witV`, `witO`, `witR`, `witI` (`lit 0`), `witE`
  (`weiter` 42 into `0 .. 100`), `witSigma` (all zero), `witSL`, `witVal`
  (42), `witM`, `witA` (base 4096, off 0), `witM'`, `witHT`, `witHw`,
  `witHL`.

Theorems (every premise used; no `Prop`-typed premise; no syntax
quantification except the main theorem):

- `zahlWort_wortZahl` — roundtrip under the checked bounds.
- `repOk_klingt` — accepted check yields the range/width/region facts.
- `schreibSlot_hit` — source write lands (the exact `execStmt`
  `.assignSlot` operation, `merke` bridge by `rfl`).
- `schreibSlot_fremd_tab/schluessel/feld` — source write preserves other
  table / other row / other field (split per case like
  `CSLInvarianteC`, since cross-table field comparison is ill-typed).
- `rep_fremd_tab/schluessel/feld` — source write + disjoint `write64`
  preserve every other carrier's `RepSlot` (via `read64_rahmen`).
- `disjunkt_von_layout` — two accepted disjoint layout entries give
  disjoint 8-byte footprints (feeds `rep_fremd_*` from decided checks,
  not an assumed disjointness).
- `rep_schritt_bleibt` — MAIN, `execStmt`-facing: one real
  `Stmt.assignSlot` step (unfolded by `simp only [execStmt]`) plus the
  matching `write64` preserves `RepSlot` at the written slot AND the
  bytes parse back (`wortZahl`) to the source value.
- Refusals (all `by decide`): `repOk_zu_gross_verweigert` (range reaches
  `2 ^ 64`), `repOk_bool_verweigert` (width mismatch),
...[truncated 2705 chars]
