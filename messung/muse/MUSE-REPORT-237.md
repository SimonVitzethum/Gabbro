# MUSE-REPORT-237 — Layout-factor muster: word tables + index arithmetic

Lane 237. Scope was exclusive: new example files + this report. No existing file
touched (`git status` shows only the two new files below plus this report).
No codes, no gifts, no OS constants. `MARKE_EMIT*` untouched.

## Deliverables

- `beispiele/151-word-pool-discipline.gab` — byte-addressed pool in word-sized
  storage: `pub table WPOOL count 1024` of `u32`, byte API (`lies_wort`,
  `lies_byte`, `schreibe_byte`) via `i >> 2` / `(i & 3) * 8`.
  `check`: **0 errors, 0 hints**, M1 42/42 typed (100 % coverage).
- `beispiele/152-byte-pool-cost.gab` — the same byte API over
  `pub static mut BYTES : [u8; 4096]`, direct indexing. `check`: **0 errors,
  0 hints**, M1 6/6 typed.
- Both emit (`emit` exit 0) and compile under `cc -std=c11 -Wall -Wextra -Werror`
  at `-O0` and `-O2` with identical outputs, plus UBSan-silent runs
  (`-O1 -fsanitize=undefined -fno-sanitize-recover=all`). Functional drivers
  (scratch, not committed) verified neighbour survival, word sharing
  (`lies_wort(0)` = 0x3CA5 = 15525 after writing 0xA5/0x3C to bytes 0/1), and
  the top byte 4095.

## The layout factor, measured (this is the ×4/×1 answer)

Per-access emitted C, character by character:

| access | emitted C | chars |
|---|---|---|
| 151 word read | `WPOOL_speicher.slots[w].w` | 25 |
| 152 byte read | `((uint64_t)(i) < 4096u ? BYTES[(uint64_t)(i)] : (__builtin_trap(), (uint8_t)0))` | 79 (**×3.16**) |
| 152 byte write | 3-line bind-check-store `_gabbro_i` block | ~150 |

The byte-ARRAY carrier gets the emitter's second-opinion run bound per access
(`leseBytes`/`schreibBytes`, lane-141 path); the word-table access, whose bound
the checker proved once (M103 over `i >> 2`'s range), emits plain C. Byte
TABLES emit plain accesses too — the factor sits on byte ARRAY carriers, and
the "×4" of the task title measures as **×3.16 per read**, booked exactly in
both files' headers. Static storage is ×1 in all four layouts I tried
(table-u8, table-u32, array-u8, array-u32: same bss per payload byte).

Static-link budget ("fits statically"):

| file | .c bytes | .o text | .o bss |
|---|---|---|---|
| 151 (1024 words) | 1932 | 246 | 4096 |
| 152 (4096 bytes) | 1470 | 202 | 4096 |
| scratch big pool (`count 1048576` words = 4 MiB, same discipline) | 1783 | — | 4194336 |

The big pool links on the build machine in 0.07 s into a 16160-byte binary and
runs correct (bytes 0/1000000/4194303). Emitted C is pool-size-independent
(1783 vs 1932 bytes — only the count literal changes); static storage is one
word per word. No linker refusal to paste: it links.

`MARKE_EMIT` delta: **+2** (117 → 119 at merge). Both files emit; no gift files,
no messung/laufzeit/programmlogik files. Counter left alone for the merger.

Costs booked at exactly computed (`gabbro costs`): 151: 2 / 14 / 24 ops;
152: 2 / 3 ops. The word side pays its arithmetic in Gabbro ops, the byte side
in emitted C per access — the trade the two files exist to show.

## Shapes accepted TODAY (all probed green, 0 errors, 100 % coverage)

`i >> 2`, `(i & 3)`, `(i & 3) * 8`, `wort >> s`, `(wort >> s) & 255`,
`u32(255) << s`, `~maske`, `|`-combine, `i / 4`, `i % 1024`,
`(i +% 1) % 1024` as table/array indices; `i - 1` with `i in 1 .. 1024` (k-1);
`j >> 2` with `j : index into BPOOL` (index-typed arithmetic); `narrow`-to-range
then pass-as-`index into` (146 pattern); `i +% 1` on exact `0 .. 2^N-1`
(wraps mod range width — sound by construction, verified against the
`i + 1`/`[1024]` M103 refusals at the same boundary).

## FEED for the per-shape lanes (missing shapes + exact refusals)

- FEED-1 (m1-side): a literal keeps its minimal width at `<<`:
  `255 << s` with `s : u32 in 0 .. 24` → `[M104] ... 'u8 in 255 .. 255 <<
  u32 in 0 .. 24' leaves the width of the result type`. Remedy used in 151:
  `u32(255) << s`. Candidate shape: "a literal takes the shift operand's
  width" (the M153/M154 sentences already grant this for wrapping ops).
- FEED-2 (emit-side, `emit.rs::ausdruck_obergrenze`): no `*`/`+`/`-`/`/`/`%`
  arms — `(i & 3) * 8` at a narrowing assignment (`let s : u8 = …`) gets no O9
  cast while `&`/`>>` do. Measured latent: silent under this machine's
  `cc -Wconversion` (verified against a hand-written control). Candidate shape:
  corners-bound for `*`-of-bounded.
- FEED-3 (decision gate, not a shape lane): wrapping needs exact ranges —
  `WPOOL.slots[i +% 1]` with `i in 0 ..< 1000` → `[M153] wrapping '+%' needs
  both sides on an exact unsigned range '0 .. 2^N - 1', found 'u32 in
  0 .. 999' and 'u8 in 1 .. 1'`. 151 sidesteps it by construction (1024 words).

Correct-refusal texts recorded while probing (all fire as designed):
`i >> 40` → M104 + M103; `i - 1` over `0 .. 4095` → M104 + M103;
`WPOOL.slots[1024]` → M103; `pub`-without-`pub` carrier → N038;
cross-file `pub const` collision → N039 (caught 151+152 in one build; 152's
const is now `POOLBYTES`).

## What I believe is wrong in the task / tree (flagged, none changed)

1. The task locates `ausdruck_obergrenze`/`indexschranke` in `m1.rs` — they live
   in `crates/gabbro-check/src/emit.rs` (lines 12954/12991). Read-only for me
   either way; nothing edited.
2. "TODO.md §-1 lanes 224/236": §-1 lists workers 221–235; there is no lane 236
   in this tree. I treated "236" as the bucket-discipline follow-up and added
   `lies_wort` as the word layer it stands on.
3. `SYNTAX.md` §SG-4 ("no other type reaches an index — `i : index into T`")
   does not match the implementation: ranged `u32` indexes table slots with
   M103 (measured repeatedly, e.g. `WPOOL.slots[i >> 2]` clean,
   `WPOOL.slots[i]` with `i in 0 .. 4095` → M103). Doc stale or aspirational —
   for lanes 224/236 to decide, not mine to edit.
4. Duplicate diagnostics: M104 (and M153) print TWICE for one site (same span,
   same text). Cosmetic; owner is whoever owns m1.rs output (lane 224 owns the
   file — I did not touch it).

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite, with both files
  in the tree — including `keine_zwei_korpusdateien_teilen_eine_nummer`).
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s) in the COMPLETE
  output` (grammatik untouched; Lean adds nothing — no new definitions or
  theorems from this lane, examples only).
- No Lean work, so rules 12/13 (target statements, witnesses) do not apply.
- Scratch probes under `.tmp/probe237/` (not committed, `.tmp` is lane-private).

## Open

- Merge-time: re-measure `MARKE_EMIT` 117 → 119; nothing else moves.
- The three FEED items above belong to the per-shape lanes / the binder-range
  decision gate. The duplicate-diagnostic nit belongs to lane 224's file.
- `u32(255)` vs literal-width shift (FEED-1) is the one papercut a reader of
  151 will feel; the file documents it at the exact line.
