# MUSE-REPORT-224 — m1 bound shapes: the `k-1` subtraction class (first per-shape lane)

Lane 224, Rust lane. Three new structural bound shapes in the checker's range
machinery, each with a bound rule + positive probe (passes with it) + poison
probes (still refused). No new codes (`M101`/`M104`/`M103` own the range, as
tasked). `emit.rs`, `MARKE_EMIT*`, Lean and every other file untouched.

## What was built (files: `crates/gabbro-check/src/m1.rs`, `typen.rs` only)

**Shape 1 — `x - (x % c)` rounds down (`Pruefer::abrunden`, `Pruefer::abrunden_ort`, free `ohne_klammern`, all in `m1.rs`).**
Interval subtraction read `0 .. 255 - 0 .. 7` as `-7 .. 255` and fired `M104`,
though the value is the largest multiple of `c` at or below `x` — a subtraction
that cannot underflow by construction (the `k-1` class without a guard). The
bound is exact: `f(x) = x - (x % c) = c * trunc(x / c)` is non-decreasing in `x`
for fixed `c > 0` (`/` truncates toward zero, exactly like C `%`), so the range
is the `f` of the endpoints; `|f(x)| <= |x|`, so it always fits the width the
minuend fits (otherwise `None`, and the ordinary subtraction asks the width
question itself). Gates, each load-bearing: same LOCAL place on both sides by
fact key (`schluessel_und_indizes`, index names included); target/handle in
`lage.lokal` and not a device handle (`griffe` — a handle samples hardware
twice); no `->` suffix; divisor a positive literal or named constant
(`konst_wert_von_namen` — pure lookup, so nothing is typed twice and no finding
is reported twice). Globals, table slots, atomics and registers are excluded on
purpose: a call between the two reads could move any of them.

**Shape 2 — `%` over a negative divisor (`typen::rest`).** `x % d` with
`x : i32 in 0 .. 100`, `d : i32 in -8 .. -1` answered `-7 .. 7` and fell as an
index, where `0 .. 7` is the true bound (C gives the remainder the dividend's
sign). One-line generalization of the existing arm: `0 .. min(max|d|-1, a.max)`
instead of `0 .. min(b.max-1, a.max)` — identical numbers for positive divisors
(`max|d| = b.max` there), tight for all-negative ones. Possibly-negative
dividends keep the symmetric answer; zero-reaching divisors still go to `M102`
before this arm is reached.

**Shape 3 — `k -= k % c` at the `-=` site (same `abrunden_ort`, called from the
`Zuweisung` arm).** The compound form of shape 1: the read carries the target's
facts (`mit_fakt`), so the narrowed range is what is rounded. `None` falls
through to `rechnung_zuweisung`, unchanged.

## Tests (12 new, all green)

- `m1::align_proben`: `gleiche_basis_schweigt`, `konstante_schweigt`,
  `minus_gleich_schweigt` (positives, silent); `fremde_basis_faellt_an_der_operation`
  (`[M104, M101]`), `tabellenplatz_bleibt_ausserhalb` (`[M104, M103]`),
  `minus_fremd_faellt` (`[M104, M101]`) (gate twins — the shape must not fire);
  `offene_basis_behaelt_nur_m103`, `minus_offen_behaelt_m103` (`[M103]` —
  the `M104` is gone, the use-refusal remains).
- `m1::negmod_proben`: `negativer_nenner_schweigt` (positive);
  `negativer_zaehler_behaelt_m103` (`[M103]`), `null_nenner_bleibt_m102`
  (`[M102]`).
- `typen::proben::rest_mit_negativem_nenner` (unit level: positive/negative
  divisor rows, symmetric dividend row).

## Measurements

- **Gap sweep before the change** (21 generated probes over widths, signs,
  literal/const/ranged divisors, mask/shift/alignment families, run against the
  unchanged binary): plain `%-then-*`, masks, `>>`-masks, division narrowing,
  const divisors and conversions all already pass — H-2's lesson
  ("reformulate subtraction-free") stands on today's checker. The three gaps
  above were the only false positives found (`align`: `M104+M103`;
  `negmod`: `M103`; `litshl-u32` (`1 << k`, `k : u32 in 0 .. 31`): `M104` —
  see the negative finding below).
- **"Falls without it"**: the sweep ran on the pre-change binary (same shapes
  refused there); `k -= k % 8` was additionally measured refused (`M104+M101`)
  after shapes 1+2 had landed but before shape 3 existed.
- **Corpus verdict diff**: `pruefe` over all 818 `beispiele/*.gab` +
  `beispiele/gift/*.gab` before vs after — **zero moves**. Every existing
  refusal (incl. gift `01`, `14`-`17`, `22`-`24`, `26`, `1042`, `1043`) falls
  identically; no corpus file exhibits the new shapes, so the proof-gains live
  in the new inline probes (no gift numbers were reserved for this lane, hence
  inline tests after the `vsub`/`m152` precedent, not gift files).
- **`./cargo-pruef`: `== exit 0; failing tests: 0`** (12 new tests included).
- **`./emission-pruef`: `== exit 0`, `ALL PASS`** (37 executed, 280/280 compile,
  ASan clean) — expected: the emitter is untouched.
- **`./lean-bau`**: not affected (no Lean files touched); full-project line
  below if the background run finished in time, otherwise see the note.

## Negative finding (measured, not built): literal-left shifts

`1 << k` with `k : u32 in 0 .. 31` fires `M104` because `schiebe_links` reads
the literal's minimal width (`u8`) instead of adopting the amount's width
(U10 — every other operator adopts via `gemeinsame_form`). I did NOT build the
adoption, for one measured reason: the emitter lowers literal-left shifts as
plain C `int` (`4 << k`, verified in the emitted C), so accepting `k = 31`
blesses C undefined behavior (`1 << 31` overflows `int`) at exactly the corner
the checker would newly accept — "where Gabbro says defined and the product
means undefined, the translation is no longer what was checked" (the same
sentence the `wrapping` lowering answers with casts). Handoff for lane 221
(`emit.rs` owner): render an adopted-width literal with the width's suffix or
cast (e.g. `1u << k` / `(uint32_t)1 << k`); after that, a future per-shape lane
can lift the checker side. The same lane should also decide the `300 << x`
direction (literal keeps minimal width today — silent; under U10 it would be
`M104`), which is a verdict flip, not a silent win.

## The pattern for future per-shape lanes (deliverable 2)

One shape = one syntactic pattern (operator + operand forms) with a bound
tighter than what interval arithmetic propagates, proved sound in Gabbro/C
semantics. Each owes: (1) a measured gap — the program that falls without the
rule, with before/after codes; (2) the rule, placed where the width question is
already asked, reusing it (never a second width rule); (3) a positive probe
(now passes) + a gate twin (same program with the gate broken — different base,
non-local place, wrong sign — still refused with the OLD codes) + a boundary
twin (open range — the operation's refusal gone, the use's refusal remaining);
(4) a full corpus+gift verdict diff with every move listed and each move a
proved bound (zero moves is an acceptable result when no corpus file shows the
shape); (5) no new codes, no emitter changes, no `MARKE_*` moves. Soundness
notes must name what is excluded and why — for every double-read rule: locals
only (no address-of makes two reads one value), never atomics, registers,
device handles, or globals under calls. Residue of this lane for the next ones:
declared-point divisors (`d : u32 in 8 .. 8` at `%` — U10, needs the width
story told once, not per shape); non-local round-down bases (table slots need
per-site call analysis, out of scope here); the `1 << k` adoption after lane
221's literal rendering.

## What the task got wrong / what was missing

- `ausdruck_obergrenze`/`indexschranke` live in `emit.rs` (lane O9/141
  machinery for the emitter's second opinion), not in `m1.rs`. Per the MUST-NOT
  list I touched neither; the shapes above are the checker-side analog.
- `messung/BEFUNDE-bm13.md` (and any `Verdict/` tree) does not exist in this
  clone, so H-2 was reconstructed from the task text plus direct measurement;
  plain `%-then-*` passes on today's checker, and the report above says exactly
  which neighbors did not.
- The lane table reserves this lane no gift numbers ("none (existing M101)"),
  so all probes are inline `#[cfg(test)]` modules, not gift files.

## Open / residue

- Lean closure untouched (`git status`: only the two Rust files); `./lean-bau`:
  `Build completed successfully (274 jobs)`.
- Emitter agreement of the new acceptances: the accepted programs lower
  through unchanged emitter arms (plain `-`, `-=`, `%` — no casts involved,
  values identical with/without the rule); the one corner that does NOT hold
  (`1 << 31`) is deliberately left refused — see the negative finding.
- `x -= ...` for `+=`, `&=`, `|=` has no round-down form; nothing to build there.

Last `./cargo-pruef`: `== exit 0; failing tests: 0`.
Last `./emission-pruef`: `== exit 0`, `EMISSION: ALL PASS`.
Corpus verdict diff: zero moves over 818 files.
