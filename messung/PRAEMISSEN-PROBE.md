# Premise probe: does the goal chain derive or forward?

Base `8329a57`, branch `r02-probenkonjunkt`. Instrument
`instrumente/pruefe-praemisse.py` (auditor-suggested, precedent
`mutiere-pruefer.py --anker` for checker passes). All variant builds ran
on `ki-pc-fisch-101` in the own lane `/tmp/praemisse-r02`, seeded from
`gabbro-r02`; the tree was read, never written.

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

Two extensions probe conjunction conclusions per conjunct, one
tripwire copy `THM__c{i}` per conjunct in a single variant build
(same binders, narrowed conclusion, proof closer isolated; the
original is untouched, so no call site needs patching):

- `THM:prem^c` -- per-conjunct need plus per-conjunct strength.
  Need weakens `prem` (premise-mentioning prefix lines dropped);
  strength weakens every other explicit premise instead, for NEEDS
  conjuncts only.
- `STRUCT.field@TARGET` -- per-conjunct need of `TARGET` against the
  removed field. No strength dual: weakening every other field
  changes the representation itself, not the premise.

| verdict | meaning |
|---|---|
| SPLIT | mixed copies -- the premise feeds only some conjuncts (need `[NEEDS, NEEDS, FREE]`) |
| UNIFORM | every conjunct needs the premise |
| DETACHED | no conjunct needs the premise |
| ALONE | (strength) the needy conjunct follows from the premise alone -- restatement shape, weak |
| JOINT | (strength) the needy conjunct needs the rest too -- joint use, strong |

Only two proof shapes split (`exact ⟨c1, …, cN⟩`, and
`refine ⟨s1, …, sN⟩` with one `·` bullet per `?_` hole in order);
anything else reports INCONCLUSIVE instead of guessing.

## Speech test (all directions)

`./instrumente/pruefe-praemisse.py --sprechprobe` -- hermetic, small
Lean files through `lean`, no lake project. The per-theorem fixtures
quote the two tree proof patterns: the DERIVED fixture mirrors
`ungeteilt_aus_lauf` (`Geteilt.lean`: the stripped premise is one
ingredient among several), the FORWARDED fixture mirrors
`ziel_l5_schranke` (`Ziel.lean`: the premise alone is the conclusion).
The four conjunct fixtures cover both extensions in both directions:
SPLIT (`⟨h, k⟩` probed at `h` reads `[NEEDS, FREE]`), UNIFORM (both
conjuncts from `h` reads `[NEEDS, NEEDS]`), WEAK (a conjunct that IS
`h` reads strength ALONE), STRONG (`Nat.lt_trans h k` reads strength
JOINT). Green all six directions locally and on fisch (2026-09-11):

- speech derived reads DERIVED (want DERIVED) -- PASS (A red, B red)
- speech forwarded reads FORWARDED (want FORWARDED) -- PASS (A red, B green)
- speech split reads SPLIT [NEEDS, FREE] (want SPLIT [NEEDS, FREE]) -- PASS
- speech uniform reads UNIFORM [NEEDS, NEEDS] (want UNIFORM [NEEDS, NEEDS]) -- PASS
- speech weak reads need NEEDS strength ALONE (want need NEEDS strength ALONE) -- PASS
- speech strong reads need NEEDS strength JOINT (want need NEEDS strength JOINT) -- PASS

## Baseline verdict table (2026-09-11, fisch, basis GREEN)

Per-theorem verdicts re-run unchanged (DERIVED 11); the five new
probes flag what the per-theorem view hid. The `w1w2w4` split is now
measured: W1/W2 ride `hvoll`/`hvers`, W4 rides `hEin` alone. The
`serial_chain_from_run` observations conjunct does not need `hLink`
at all; the HB conjunct needs it jointly (JOINT -- real use, not a
restatement). One premise reads FORWARDED: `maschinenWelten_speicher_gleich`
follows from its machine premise alone -- the constant-memory
folding shape (`World.merke` never touches slots/globs, so the
conclusion restates the construction).

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
| `serial_chain_from_run:hLink^c` | conj | SPLIT | need [FREE, NEEDS], strength [n/a, JOINT] -- observations free of `hLink`, HB needs it jointly (`Unknown identifier j₁` in c2) |
| `MaschinenLauf.hvoll@w1w2w4_aus_maschine` | conj | SPLIT | need [NEEDS, NEEDS, FREE] -- W1/W2 need `hvoll` (`Unknown identifier hkons/hgut`), W4 builds |
| `MaschinenLauf.hvers@w1w2w4_aus_maschine` | conj | SPLIT | need [NEEDS, NEEDS, FREE] -- same shape as `hvoll` |
| `MaschinenLauf.hEin@w1w2w4_aus_maschine` | conj | SPLIT | need [FREE, FREE, NEEDS] -- W4 alone needs `hEin` (`Invalid field hEin` in c3 only) |
| `maschinenWelten_speicher_gleich:M` | hyp | FORWARDED | A: target breaks; B builds -- premise alone carries the conclusion |

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
      --exclude '.claude/worktrees/' ./ ki-pc-fisch-101:gabbro-r02/
rsync -a beweise/ ki-pc-fisch-101:gabbro-r02/beweise/
./instrumente/pruefe-praemisse.py --sprechprobe
./instrumente/pruefe-praemisse.py \
  serial_chain_from_run:hLink einfaedig_aus_verlauf_getragen:hT \
  ungeteilt_aus_lauf:hl stabil_from_spec:hFree \
  stabil_from_spec_invariantForm:hForm \
  MaschinenLauf.hvoll MaschinenLauf.hvers MaschinenLauf.hausschluss \
  MaschinenLauf.hEin MaschinenLauf.hungeteilt \
  interferenceFree_wo_frei:@LockFrei \
  'serial_chain_from_run:hLink^c' \
  MaschinenLauf.hvoll@w1w2w4_aus_maschine \
  MaschinenLauf.hvers@w1w2w4_aus_maschine \
  MaschinenLauf.hEin@w1w2w4_aus_maschine \
  maschinenWelten_speicher_gleich:M
```

Full runs take about ten minutes (basis plus up to two incremental
`lake build` per probe). Per-probe logs: `/tmp/opencode/r02/batch6.log`
(per-theorem regression, DERIVED 11), `/tmp/opencode/r02/batch2.log`
(field splits plus folding flag), `/tmp/opencode/r02/batch5.log`
(SerialLink split plus strength) on the invoking host; last remote
build log at `/tmp/praemisse-r02-last.log` on fisch.
