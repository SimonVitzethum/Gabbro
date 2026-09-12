# MUSE-REPORT-63

Lane 63: COMPILE-TIME CERTIFICATE MEASUREMENT (PLAN-BITS.md section 6).
Lean measurement lane; branch `muse/63`.

## What I did

New standalone file `grammatik/Messung/Zertifikat.lean` (NOT imported by
`grammatik/Grammatik.lean`, so it never slows the main build) with the
three certificate shapes from the task:

- encoding N: `bound`, `entryOkN`, `certN` (`List.all` over bare `Nat`
  literals closed by `decide`), range proofs attached afterwards by
  `certN_all_lt`, 8-entry probe `example : certN [0..7] = true := by decide`;
- encoding Z: `EntryZ` (`Zahl 0 (2^52 - 1)`), `certZ`, `certZ_holds`;
- fallback: `cert8` (8 blocks, each closed by its own `decide`),
  join lemma `cert8_flatten`.

Report `messung/ZERTIFIKAT-MESSUNG.md` with every number and the command
that produced it (generator `$TMPDIR/cert/gen.py` and runner
`$TMPDIR/cert/run.sh` are scratch under `$TMPDIR`, not committed).

## Exact names of new definitions/theorems

`Gabbro.Messung.Zertifikat.bound`, `.entryOkN`, `.certN`, `.certN_nil`,
`.certN_all_lt`, `.EntryZ`, `.certZ`, `.certZ_holds`, `.cert8`,
`.cert8_flatten`, plus `#print axioms` for the four theorems:
`certN_nil` and `certZ_holds` depend on no axioms;
`certN_all_lt` and `cert8_flatten` on `[propext, Quot.sound]`
(project baseline subset, no `sorry`/`axiom`/`native_decide`/`unsafe`).

## Last `./lean-bau` result line

`Build completed successfully (36 jobs).`

`./lean-probe grammatik/Messung/Zertifikat.lean`: 0 errors. The text
guardian `pruefe-englisch.py` was already red before my change (ratchets
broken at 7904/7881, 1085/1069, 24/23, 1/0) and stays red for the same
pre-existing reasons; my files use English-only identifiers and comments
(German names from the first draft were renamed before committing).

## Headline measurement (full table: 2048 entries, each in 0..2^52)

- Encoding N (`certN` + one `decide`): wall 0.94 s (base literal alone
  0.84 s), elaboration 336 ms, `decide` tactic 163 ms, kernel check
  101 ms, maxRSS 581 MB. Proof term constant-size (repr 1709/1713/1717/
  1721 chars at 8/64/512/2048 entries). Completes at all four sizes.
- Encoding Z (proofs carried per entry): 512 entries 7.60 s wall
  (elaboration 5.66 s, quadratic: 68/184/704/3120 ms at 64/128/256/512
  zeros); 2048 entries FAILS (deterministic heartbeat timeout, 800000
  heartbeats, 172 s wall, 4.3 GB). Does not complete at full size.
- Fallback (8 blocks + joined `decide`): 2048 entries 0.96 s wall,
  completes everywhere, buys nothing at this size.

Decision for item 6: build encoding N (bare-`Nat` `List.all` + `decide`,
range proofs attached afterwards); do not build encoding Z; keep the
8-block fallback measured but unused until tables an order of magnitude
larger force a re-measurement. `set_option maxRecDepth 32768` is needed
for 512+ entry literals in any encoding (front-end literal limit, also
needed with no certificate at all).

## What remains open

- The 8-block fallback at 10x table sizes is unmeasured (single decide
  is fast enough that the fallback was never needed).
- Proof-term size measured as `repr` character count of the elaborated
  `def` (constant ~1.7 KB); no `.olean` byte-size measurement was taken.
- Elaboration vs kernel time comes from `set_option profiler true`
  rows, not from isolated kernel re-check runs; kernel check here means
  the profiler's "type checking" row.

## What I believe is wrong in the task

Nothing load-bearing. Two remarks: (1) "proof-term size if you can
obtain it" is obtainable and turns out to be the strongest part of the
result — the `decide` term is constant-size, so the feared blowup does
not exist in encoding N. (2) The stop rule "stop scaling when a step
exceeds 10 minutes" is reached only by encoding Z at 2048 via heartbeat
timeout rather than wall time; I recorded it as does-not-complete and
kept the N/fallback ladders complete, which I read as the rule's intent.
