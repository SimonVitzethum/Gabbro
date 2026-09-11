# Premise probe: does the goal chain derive or forward?

Base `76b2510`, branch `k01-praemissenprobe`. Instrument
`instrumente/pruefe-praemisse.py` (auditor-suggested, precedent
`mutiere-pruefer.py --anker` for checker passes). All variant builds ran
on `ki-pc-fisch-101` in the own lane `/tmp/praemisse-k01`, seeded from
`gabbro-k01`; the tree was read, never written.

## The question

A theorem that restates a premise under a new name looks like progress
and measures like none. For each premise of a goal-chain theorem the
probe builds a stripped variant in a scratch copy and reads what breaks:

| verdict | meaning |
|---|---|
| DERIVED | a downstream proof fails that is not the forwarding theorem itself (hyp: variant A shows the premise necessary, variant B shows the rest necessary too -- joint derivation) |
| FORWARDED | only the theorem restating the premise breaks (hyp: A necessary, B builds with the premise alone -- the premise carries the whole conclusion) |
| UNUSED | the stripped cone builds unchanged -- dead weight end to end |
| INCONCLUSIVE | the patch did not apply cleanly -- a site list is printed, nothing is claimed |

Three probe kinds: `THM:prem` weakens a hypothesis to `True` (call-site
arguments at the premise position become `trivial`); `STRUCT.field`
removes a structure field (constructor literals blanked, projections
left to fail); `THM:@Word` deletes conclusion arrows mentioning `Word`
and drops the matching `intro` binders. Every replacement preserves
line numbers, so error lines still point at the tree. `unknown
constant` / `Unknown identifier` fallout of the stripped theorem itself
folds back onto it and never counts as downstream breakage.

## Speech test (both directions)

`./instrumente/pruefe-praemisse.py --sprechprobe` -- hermetic, two small
Lean files through `lean`, no lake project. The fixtures quote the two
tree proof patterns: the DERIVED fixture mirrors `ungeteilt_aus_lauf`
(`Geteilt.lean`: the stripped premise is one ingredient among several),
the FORWARDED fixture mirrors `ziel_l5_schranke` (`Ziel.lean`: the
premise alone is the conclusion). Green both directions locally and on
fisch (2026-09-11):

- speech derived reads DERIVED (want DERIVED) -- PASS (A red, B red)
- speech forwarded reads FORWARDED (want FORWARDED) -- PASS (A red, B green)

## Baseline verdict table (2026-09-11, fisch, basis GREEN)

No premise is FORWARDED today. Every stripped premise breaks a genuine
derivation, and every variant-B (rest weakened) breaks too: the chain
derives jointly everywhere it was probed.

| probe | kind | verdict | what breaks |
|---|---|---|---|
| `serial_chain_from_run:hLink` | hyp | DERIVED | A+B: `serial_chain_from_run` (Function expected / Application type mismatch) |
| `einfaedig_aus_verlauf_getragen:hT` | hyp | DERIVED | A+B: `einfaedig_aus_verlauf_getragen` (Application type mismatch) |
| `ungeteilt_aus_lauf:hl` | hyp | DERIVED | A: target + `example@780`; B: target, example cascades |
| `stabil_from_spec:hFree` | hyp | DERIVED | A: target + `stabil_from_spec_invariantForm` (No goals); B: target |
| `stabil_from_spec_invariantForm:hForm` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `MaschinenLauf.hvoll` | field | DERIVED | `maschinenWelten_gut`, `w1w2w4_aus_maschine`, `gesittet_aus_maschine` (Invalid field) |
| `MaschinenLauf.hvers` | field | DERIVED | same three as `hvoll` |
| `MaschinenLauf.hausschluss` | field | DERIVED | `gesittet_aus_maschine` only -- W3 feeds the bridge alone |
| `MaschinenLauf.hEin` | field | DERIVED | `w1w2w4_aus_maschine`, `gesittet_aus_maschine` |
| `MaschinenLauf.hungeteilt` | field | DERIVED | `gesittet_aus_maschine` only -- W5 feeds the bridge alone |
| `interferenceFree_wo_frei:@LockFrei` | gate | DERIVED | body: Unknown identifier `hFreiNach` (gates consumed, not decorative) |

Scope note: `serial_chain_from_run` and
`einfaedig_aus_verlauf_getragen` have no in-tree consumers yet
(remainder state) -- their DERIVED rests on the A/B pair (necessary,
insufficient alone), not on a downstream break. The field split matches
the documented shape: W1/W2/W4 (`hvoll`, `hvers`, `hEin`) feed
`w1w2w4_aus_maschine` and the bridge; W3 (`hausschluss`) and W5
(`hungeteilt`) feed the bridge alone.

## Recompute

```bash
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' \
      --exclude '.claude/worktrees/' ./ ki-pc-fisch-101:gabbro-k01/
./instrumente/pruefe-praemisse.py --sprechprobe
./instrumente/pruefe-praemisse.py \
  serial_chain_from_run:hLink einfaedig_aus_verlauf_getragen:hT \
  ungeteilt_aus_lauf:hl stabil_from_spec:hFree \
  stabil_from_spec_invariantForm:hForm \
  MaschinenLauf.hvoll MaschinenLauf.hvers MaschinenLauf.hausschluss \
  MaschinenLauf.hEin MaschinenLauf.hungeteilt \
  interferenceFree_wo_frei:@LockFrei
```

Full runs take about six minutes (basis plus up to two incremental
`lake build` per probe). Per-probe logs: `/tmp/probe-k01-final2.log`
(hyp), `/tmp/probe-k01-fields2.log` (fields), `/tmp/probe-k01-gate2.log`
(gates) on the invoking host; last remote build log at
`/tmp/praemisse-k01-last.log` on fisch.
