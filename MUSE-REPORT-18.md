# MUSE-REPORT-18: premise probe per-conjunct blind-spot speech pair

## What I did

Lane 18 asked for a per-conjunct premise probe: per theorem, a conclusion
`A /\ B /\ C` where conjunct C follows from one premise alone reads DERIVED
because A and B need the other premises. The task: split the conclusion,
check each conjunct against each premise, keep the existing speech test
green, add a new speech fixture pair for the blind spot (both directions),
Python only, no whole-tree probe runs, Lean checks only through
`./lean-probe` on fixtures.

Finding on arrival: the instrument (`instrumente/pruefe-praemisse.py`) at
this branch already implements the full per-conjunct mode from the r02
commit 49403aa (tripwire copies `THM__c{i}`, need NEEDS/FREE with
SPLIT/UNIFORM/DETACHED rollup, strength ALONE/JOINT for NEEDS conjuncts,
field form `STRUCT.field@TARGET`, fixtures SPLIT/UNIFORM/WEAK/STRONG, 6/6
green on arrival). What was genuinely missing was exactly the blind-spot
demonstration: no fixture showed a case where the per-THEOREM verdict
cannot tell weak from strong while per-conjunct strength can.

Changes (all in `instrumente/pruefe-praemisse.py`, Python only, no Lean
files touched, no `grammatik/` changes):

- New fixtures `SPEECH_BLIND_WEAK` and `SPEECH_BLIND_STRONG`: three
  conjuncts, probed at `h`. c1 needs h+k jointly (`Nat.lt_trans h k`),
  c2 needs k only (FREE at h), c3 differs: `h` alone (WEAK) vs
  `Nat.lt_trans h k` (STRONG). Per-theorem reads DERIVED for both
  (A red, B red -- c1 carries both variants). Per-conjunct need reads
  `[NEEDS, FREE, NEEDS]` for both. Only strength at c3 separates them:
  ALONE vs JOINT.
- New `blind_cases` loop in `speech_probe()` asserting all three readings
  per fixture: per-theorem verdict + 3-conjunct need vector + strength at
  c3. Both directions.
- One docstring line in the verdict scale noting the per-theorem blind
  spot and pointing at the new pair.

## Exact names

- `SPEECH_BLIND_WEAK`, `SPEECH_BLIND_STRONG` (fixture sources).
- No new functions; the `blind_cases` block reuses `check_single_variant`
  (per-theorem A/B) and `check_conjunct_variant` (need + `weaken_rest`
  strength).

## Verification

- `./lean-probe` (queued) on both extracted fixtures: exit 0 each
  (green basis, a probe result rather than a red fixture).
- `python3 instrumente/pruefe-praemisse.py --sprechprobe`: 8/8 PASS --
  the 6 pre-existing directions unchanged plus
  `blind-weak ... thm DERIVED need [NEEDS, FREE, NEEDS] strength ALONE`
  and `blind-strong ... thm DERIVED need [NEEDS, FREE, NEEDS] strength
  JOINT`, each with `(A red, B red)`.
- `python3 -m py_compile instrumente/pruefe-praemisse.py`: OK.
- No `./lean-bau` run needed (no Lean sources changed); no lane/tree
  probe runs per the task constraint (fixtures only).

## What remains open

- The per-conjunct tripwire vocabulary is still closed (exact-tuple and
  refine-hole closers only); other proof shapes report INCONCLUSIVE.
- No lane runs were performed here, so the new pair has no
  `messung/PRAEMISSEN-PROBE.md` register entry; that table is for the
  owner of the tree runs to extend.

## What in the task I believe is wrong

- The task states the instrument classifies "per THEOREM" and asks to
  "add a per-conjunct mode". That mode already exists (r02, 49403aa)
  with four speech directions; the task text appears to predate it.
  The real gap -- and what I added -- is the blind-spot pair proving
  the per-theorem verdict goes blind exactly where per-conjunct
  strength still speaks. Nothing in the task is wrong as a goal; it is
  stale as a description of the starting point.
