# Certificate measurement (PLAN-BITS.md section 6)

Lane 63. Question: how does Lean 4.33.1 check a certificate "this page
table is correct" for a four-level walk with 512 entries per level (a
table of 512 * 4 = 2048 entries, each a Nat in 0 .. 2^52)? Three shapes:

- (a) encoding N: entries as bare `Nat` literals in a `List Nat`, the
  certificate predicate `List.all` with a `Decidable` instance, closed by
  `decide`; the range proofs attached afterwards by one lemma
  (`certN_all_lt` in `grammatik/Messung/Zertifikat.lean`);
- (b) encoding Z: entries as `Zahl` values carrying their proofs
  (`{ n := (v : Int), lo_le := by decide, le_hi := by decide }`);
- (c) fallback: the certificate cut into 8 blocks, each closed by its own
  `decide`, plus one `decide` over the joined block list.

`native_decide` is forbidden and was not used anywhere.

## Setup

Machine: build server, 16 cores, 110 GB RAM. Lean 4.33.1
(`~/.elan/bin/lean --version`: `4.33.1, x86_64-unknown-linux-gnu`).
Each probe file starts with `import Grammatik.Typen`,
`set_option profiler true`, then the table literal and the certificate.
Timing: `set_option profiler true` rows (elaboration, tactic execution,
type checking = kernel check of the elaborated term) plus wall time and
peak RSS from `/usr/bin/time` around `lake env lean <file>` run from
`grammatik/` through the slot queue. Certificate cost = cert file minus
the matching base file (same table literal, no `decide`).

Entry values: `v_i = (i * 2654435761 + 12345) mod 2^52`, with entry 0
replaced by `0` and the last entry by `2^52 - 1` (both range edges
present). Generator: `$TMPDIR/cert/gen.py` (scratch, not committed);
probe files are scratch under `$TMPDIR/cert/` and are not committed.
The committed artifact is `grammatik/Messung/Zertifikat.lean` (the three
predicates, the attach-afterwards lemma, the block-join lemma, one
8-entry probe) plus this report. Command per row:

```bash
./.tmp/cert/run.sh "$TMPDIR/cert/<file>.lean" <label>
# run.sh cds to grammatik/, runs: /usr/bin/time -f "wall %es maxRSS %MKB" \
#   lean-slot bash -c "~/.elan/bin/lake env lean <file>"
# and the profiler rows come from the file's own `set_option profiler true` output
```

Note on `maxRecDepth`: the default (512) already fails while elaborating
the table literal itself at 512 entries (one nested `List.cons` per
entry), before any certificate runs. All 512- and 2048-entry files
therefore carry `set_option maxRecDepth 32768` at the top. This is an
elaboration option for the literal, not a certificate trick: the 512
base file (no certificate at all) needs it too.

## Results

### (a) Encoding N: bare Nat literals, one `decide`

| entries | base wall / elab | cert wall / elab | decide tactic | kernel check (type checking) | maxRSS cert | completes |
|---|---|---|---|---|---|---|
| 8 | 0.19 s / 4.7 ms | 0.19 s / 5.5 ms | 2.6 ms | 1.0 ms | 478 MB | yes |
| 64 | 0.20 s / 10.3 ms | 0.21 s / 11.3 ms | 6.9 ms | 3.4 ms | 481 MB | yes |
| 512 | 0.35 s / 76 ms | 0.34 s / 69 ms | 35 ms | 25 ms | 504 MB | yes |
| 2048 | 0.84 s / 305 ms | 0.94 s / 336 ms | 163 ms | 101 ms | 581 MB | yes |

Certificate cost at 2048 (cert minus base): wall +0.10 s, of which
`decide` tactic +162 ms and kernel check +97 ms. Everything is far below
any cliff: the realistic table (2048 entries) checks in about one
second wall.

Proof-term size (representation characters of the elaborated `def`
`certd<n> : certN tab<n> = true := by decide`, obtained via
`import Lean.Elab.Command` + `run_cmd` reading `env.find?` and printing
`(repr v).length`): 8 entries 1709 chars, 64 entries 1713, 512 entries
1717, 2048 entries 1721. The `decide` proof term is constant-size
(`of_decide_eq_true` applied to a kernel-computed `Eq.refl true`); it
grows by 4 chars per 8x entries (longer constant names only). There is
no proof-term size problem in encoding N.

### (b) Encoding Z: entries as `Zahl` carrying proofs

| entries | wall | elaboration | tactic | kernel check | maxRSS | completes |
|---|---|---|---|---|---|---|
| 8 | 0.21 s | 4.9 ms | 2.3 ms | 3.5 ms | 479 MB | yes |
| 64 | 0.34 s | 69 ms | 19 ms | 24 ms | 490 MB | yes |
| 512 | 7.60 s | 5.66 s | 257 ms | 193 ms | 816 MB | yes |
| 2048 | 172.5 s | 156 s | — (heartbeat timeout) | — | 4.3 GB | NO |

At 2048 entries the file fails with two deterministic-timeout errors
(`tactic execution`, `synthesize pending MVars`, 800000 heartbeats;
default 200000 heartbeats already failed after 36.7 s). So encoding Z
does NOT complete at full size within any reasonable budget, let alone
20 minutes at larger sizes.

Bisectors (all-zero entry values, isolating literal size from proof
content; same `Zahl` + `by decide` shape):

| shape | wall | elaboration |
|---|---|---|
| List Nat literal, 512 zeros (no proofs at all) | 0.29 s | 57 ms |
| List Zahl, 64 zeros | — | 68 ms |
| List Zahl, 128 zeros | 0.44 s | 184 ms |
| List Zahl, 256 zeros | 1.08 s | 704 ms |
| List Zahl, 512 zeros | 3.88 s | 3.12 s |
| List Zahl, 512 real values | 7.60 s | 5.66 s |

Doubling the Zahl list multiplies elaboration by ~4x (68 / 184 / 704 /
3120 ms): elaboration is quadratic in the number of proof-carrying
entries, while the bare-Nat literal is linear (57 ms at 512). Tactic
execution stays small (94 ms of the 3.12 s at 512 zeros), so the cost is
not `decide` evaluating: it is elaboration (unification / metavariable
context) scaling with the number of per-entry proof terms in one
literal. Explicit `Zahl.mk` instead of structure-instance syntax gives
the same 256-entry cost (685 ms vs 704 ms), so it is not anonymous-
constructor overhead either. Splitting the 512-list into two 256-halves
concatenated with `++` halves the total (2 x 730 ms vs 3.12 s),
confirming superlinear scaling in one literal.

Consequence for PLAN-BITS.md section 6: the plan's worry is confirmed
in the precise direction it names — entries as `Zahl` values carrying
their proofs leave the kernel's fast `Nat` path (the per-entry `Int`
bound proofs elaborate superlinearly), while the bare-`Nat` + `decide`
predicate with range proofs attached afterwards stays flat. Build
encoding N, not encoding Z.

### (c) Fallback: 8 blocks with one `decide` each

| entries (8 blocks) | wall | elaboration | tactic total | kernel check | maxRSS | completes |
|---|---|---|---|---|---|---|
| 64 (8 x 8) | 0.23 s | 15.6 ms | 12.9 ms | 7.3 ms | 481 MB | yes |
| 512 (8 x 64) | 0.39 s | 74 ms | 81.5 ms | 41 ms | 500 MB | yes |
| 2048 (8 x 256) | 0.96 s | 291 ms | 257 ms | 188 ms | 576 MB | yes |

Each block file also closes the joined 8-block list with one `decide`
(`allblk.all certN = true`), which succeeds everywhere. At 2048 the
fallback costs about the same as the single certificate (0.96 s vs
0.94 s wall) with slightly lower peak RSS (576 MB vs 581 MB). It is
available and measured, but at this table size it is not needed: the
single `decide` is already fast and small.

## Scaling verdict

No step exceeded 10 minutes except encoding Z at 2048 (heartbeat
timeout after 172 s wall at 4x budget; default budget fails after
36.7 s). Per the task's stop rule, encoding Z stops scaling at 2048
(recorded as does-not-complete); encodings N and fallback complete all
four sizes including the realistic 2048-entry table in ~1 s.

## Elaboration time vs kernel-check time, separately

The profiler separates them directly: "elaboration" (front end,
includes parsing the literal and running the `decide` tactic) vs "type
checking" (kernel check of the elaborated term) vs "tactic execution"
(the `decide` evaluation itself). At 2048/N: elaboration 336 ms, of
which `decide` tactic 163 ms; kernel check 101 ms. The kernel check is
about one third of the elaboration and scales linearly; neither is a
cliff. For encoding Z at 512, elaboration (5.66 s) dominates kernel
check (193 ms) by 29x — the bottleneck is elaboration, not the kernel.

## What this decides for item 6

1. Certificates are lists of explicit entries checked entry by entry
   with `List.all` over bare `Nat` literals closed by `decide` —
   exactly the shape PLAN-BITS.md section 6 prescribes. Measured:
   2048 entries in ~1 s wall, constant-size proof term.
2. Entries as `Zahl` carrying proofs do not scale (quadratic
   elaboration, timeout at 2048). Do not build encoding Z.
3. The 8-block fallback is measured and works (0.96 s at 2048) but buys
   nothing at this size; keep it as the planned fallback for tables an
   order of magnitude larger, where it should be re-measured before use.
4. `set_option maxRecDepth 32768` (or an equivalent literal-splitting)
   is needed for table literals of 512+ entries regardless of encoding;
   it is a front-end literal limit, unrelated to certificate strength.
