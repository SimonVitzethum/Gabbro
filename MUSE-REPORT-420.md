# MUSE-REPORT-420: ByteSwap (continuous Lean proof reserve)

## What was done

Created `grammatik/Grammatik/X86/ByteSwap.lean` (new reusable module,
imported additively at the end of `grammatik/Grammatik.lean` — that
import line was committed with the skeleton and is unchanged here):
canonical 32/64-bit byte-swap value helpers over the canonical `Wort`
with involution, byte-order memory correspondence, width-extension
effects, flag threading, 16/8-bit refusal, and joint concrete
witnesses. No `Befehl` constructor, no codec bytes, no `schritt`
change, no source correspondence (see CUTS in the file).

Reuse (nothing duplicated): `wortByte`/`bytesWort`/`read64`/`write64`/
`read32`/`write32`/`writeBytesN_hit`/`read64_nach_write64`/
`read32_nach_write32`/`write64_rahmen`/`read64_rahmen`/
`disjunkt_von_intervallen`/`zeugenSpeicher` from `X86/Speicher.lean`,
and `byteOf`/`bswap32n`/`bswap64n`/`bswap32n_lt`/`bswap64n_lt`/
`bswap32n_invol`/`bswap64n_invol`/`split4`/`split8`/`byteOf_nest`/
`byteOf_nest8`/`bswap32n_nest`/`bswap64n_nest` from `Grammatik.Bits`
(new `import Grammatik.Bits`, no cycle: Bits imports only
`Grammatik.Typen`).

## New definitions/theorems

Defs: `bswap64`, `bswap32`, `bswap64f`, `bswap32f`, `bswapBreite`,
`bswapZeugenWort`, `bswapZeugenNach64`, `bswapZeugenNach32`.
Glue: `wortByte_lt`, `wortByte_byteOf`, `bswap64_nat`, `bswap32_nat`,
`toNat_lt256_8`, `bswap32_nest_wort`, `byteOf_bswap64n`,
`byteOf_bswap32n` (+ private `pow2_8/64`, `pow256_0..7` normalisers).
Results: `wortByte_bswap64`, `bswap64_invol`,
`wortByte_bswap32_lo`, `wortByte_bswap32_hi`, `bswap32_zeroExt`,
`bswap32_invol_bounded` (bound `< 2^32` is load-bearing: BSWAP r32
clears the upper half, so unbounded involution would be FALSE),
`bswap64_store_bytes`, `read64_nach_bswap64`,
`bswap64_write_rahmen`, `bswap64_read_rahmen`, `read32_nach_bswap32`,
`bswap64f_wert_flags`, `bswap32f_wert_flags`, `bswapBreite_b8/b16`
(refusals, `none`), `bswapBreite_b32/b64`.
Witnesses/probes: `bswapZeuge_ne`, `probe_bswap64_wert`,
`probe_bswap32_wert`, `probe_bswap32_verwirft_oben` (negative: high
bytes do not survive r32), `probe_bswap64_invol`,
`probe_bswap64_speicher` (write/read-back/changed byte `0x00`->`0x01`
on `0x0102030405060708`), `probe_disjunkt` (`Disjunkt 0 4096` with
decided no-wrap bounds), `probe_bswap64_alias` (disjoint read
survives + own byte changes, jointly), `probe_bswap32_speicher`.
No theorem quantifies over program syntax, so HARD-RULES 13 needs no
`_zeuge`; the joint memory witnesses are non-degenerate regardless
(nonzero value, real store, changed memory).

## Check results (exact)

- `./lean-probe grammatik/Grammatik/X86/ByteSwap.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `#print axioms`: involution/store/witnesses depend only on
  `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel`
  set); projections/frames/refusals on `[propext, Quot.sound]` or
  nothing. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- `./lean-bau`: BLOCKED environmentally, NOT red (see below).
  Last line: `error: Lean exited with code 134`, failing target
  `Grammatik` (the final umbrella link-compile) with
  `libc++abi: terminating ... failed to create thread` after
  `[392/393]` built. Proof it pre-exists my content: stashed my
  uncommitted work (skeleton state) and rebuilt — identical crash.
  Machine had a reported OOM today (swap full); even a trivial
  one-def scratch file crashed the same way three times before
  recovering. My file itself builds as one of the 391 passing
  targets (import resolves, no cycle). The `gabbro_ziel` axiom
  re-check is blocked by the same cause.

## What remains open

- `./lean-bau` green + `gabbro_ziel` axiom re-check must be
  re-run by the merge/coordinator when the machine recovers.
- Native extension (instruction form, codec bytes, `schritt` rule),
  source-`bswap` correspondence, and any TSO/concurrency claim are
  explicitly CUT (file lists all of them).

## Task feedback (the brief was followed throughout; nothing believed wrong)

- The brief's "no invented 16-bit BSWAP" is load-bearing beyond
  refusal: `bswap32` involution genuinely needs its bound.
- Three Lean gotchas for sibling lanes, all diagnosed by minimal
  scratch probes: (1) `rw [lemma]` rewrites only the FIRST matched
  instance — use `simp only` for all-instances; (2) `Eq.trans`
  across the `toNat`/`byteOf` representation gap unfolds
  `Nat.mod`/`Nat.div` (well-founded) and hits maxRecDepth — keep
  both sides in one representation before `exact`; (3) a
  multi-line `{ s with f := <application with nested parens> }`
  misparses — keep the whole update on one line or parenthesise
  the value; (4) paren counting lies — verify nest association
  against the value (`B0*256^3+...`), not the parens.
