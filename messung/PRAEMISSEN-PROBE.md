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

## Discipline + PC premise baseline (2026-09-11, fisch, t02 lane, basis GREEN)

The discipline package (§8 shape, consumed at §9: `hAbD`, `hFrameTD`,
`hFrameGD`, `hGuardEx`, `hEntry`, `hReturn`, `hWatch` on
`ziel_nutzer_last_aus_maschine`, `Ziel.lean:771-786`, folded through
`invariantenKontext_aus_disziplin`,
`InterferenzAllgemein.lean:1530-1560`) had no register entry: measured
below, per-theorem plus per-conjunct plus strength, together with the
PC premises (`hmark`/`hcar` per step, `PCMarkSep`/`PCUnsharedSep` at
their discharge consumers). Lane: the instrument was retargeted
`r02` to `t02` before any run below (`REMOTE_ROOT`
`/tmp/praemisse-t02`, seed `~/gabbro-t02`); both transfers per agent
rule (`-rlpgoD` tree, `-a` `beweise/`). Speech 6/6 green locally and
on fisch. Every basis GREEN; the tree was read, never written.

Per-theorem discipline verdicts (§9 target, 10-conjunct `refine`
`Ziel.lean:818`): A weakens the premise (call sites take `trivial`),
B weakens every other explicit premise instead. B-red is the
strength analogue: the rest is necessary too (JOINT-equivalent).

| probe | kind | verdict | what breaks |
|---|---|---|---|
| `ziel_nutzer_last_aus_maschine:hAbD` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `ziel_nutzer_last_aus_maschine:hFrameTD` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `ziel_nutzer_last_aus_maschine:hFrameGD` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `ziel_nutzer_last_aus_maschine:hGuardEx` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `ziel_nutzer_last_aus_maschine:hEntry` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `ziel_nutzer_last_aus_maschine:hReturn` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `ziel_nutzer_last_aus_maschine:hWatch` | hyp | DERIVED | A+B: target (Application type mismatch) |
| `invariantenKontext_aus_disziplin:hAb` | hyp | DERIVED | A+B: target (Function expected); downstream `interferenceFree_wo_frei` red |
| `invariantenKontext_aus_disziplin:hFrameT` | hyp | DERIVED | A+B: target (Function expected) |
| `invariantenKontext_aus_disziplin:hFrameG` | hyp | DERIVED | A+B: target (Function expected) |
| `invariantenKontext_aus_disziplin:hGuardEx` | hyp | DERIVED | A+B: target (Function expected / Application type mismatch) |
| `invariantenKontext_aus_disziplin:hEntry` | hyp | DERIVED | A+B: target; downstream `interferenceFree_wo_frei` red |
| `invariantenKontext_aus_disziplin:hReturn` | hyp | DERIVED | A+B: target; downstream `interferenceFree_wo_frei` red |
| `invariantenKontext_aus_disziplin:hWatch` | hyp | DERIVED | A+B: target; downstream `interferenceFree_wo_frei` red |

Per-conjunct + strength discipline verdicts (§9 `^c`, one tripwire
copy per conjunct, strength weakens the rest for NEEDS conjuncts).
Uniform across all seven: only conjunct 3 (the sequential-logic leg,
`Ziel.lean:821-824`) needs the premise, and it needs the rest too.

| probe | kind | verdict | need / strength |
|---|---|---|---|
| `ziel_nutzer_last_aus_maschine:hAbD^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |
| `ziel_nutzer_last_aus_maschine:hFrameTD^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |
| `ziel_nutzer_last_aus_maschine:hFrameGD^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |
| `ziel_nutzer_last_aus_maschine:hGuardEx^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |
| `ziel_nutzer_last_aus_maschine:hEntry^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |
| `ziel_nutzer_last_aus_maschine:hReturn^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |
| `ziel_nutzer_last_aus_maschine:hWatch^c` | conj | SPLIT | need [FREE, FREE, NEEDS, FREE x7], strength c3 JOINT |

PC premise verdicts. `PCMarkSep` (`Maschine.lean:1309-1310`) and
`PCUnsharedSep` (`:1318-1322`) are defs, so they are probed through
the premises that carry them (`hSep`, `hMSep`, `hCSep`) at every
discharge consumer; `hmark`/`hcar` are constructor arguments of
`PCSchritt.leaf` (`:1343-1346`), not theorem premises.

| probe | kind | verdict | what breaks |
|---|---|---|---|
| `pc_discharge_einfaedig:hSep` | hyp | DERIVED | A+B: target; cascade fallout below |
| `pc_discharge_unshared:hSep` | hyp | DERIVED | A+B: target; cascade fallout below |
| `pc_marke_eindeutig:hSep` | hyp | DERIVED | A+B: target; cascade fallout below |
| `pc_gesittet:hMSep` | hyp | DERIVED | A+B: target; cascade fallout below |
| `pc_gesittet:hCSep` | hyp | DERIVED | A+B: target; cascade fallout below |
| `pc_w1w2w4:hMSep` | hyp | DERIVED | A+B: target; cascade fallout below |
| `pc_reduktion:hMSep` | hyp | DERIVED | A+B: target |
| `pc_reduktion:hCSep` | hyp | DERIVED | A+B: target |
| `PCSchritt:hmark` | hyp | INCONCLUSIVE | premise not found in signature (constructor arg, not a theorem premise) |
| `pc_w1w2w4:hMSep^c` | conj | INCONCLUSIVE | fewer bullet blocks than holes (hole closed by following intro/exact block) |
| `pc_gesittet:hMSep^c` | conj | INCONCLUSIVE | conclusion is not a conjunction (`Gesittet` is a structure, `Wettlauf.lean:181`) |

Constructor-arg strips (manual lane `/tmp/praemisse-t02-man`, same
protocol: basis GREEN, line numbers preserved, pristine restored
after): blank the binder (`hmark` `:1343-1344`; `hcar` `:1345` plus
`:1346` up to the constructor-result colon, which shares the line),
drop the arg-position name from the five leaf `rcases` patterns
(`:1389`, `:1408`, `:1419`, `:1497`, `:1542`), rebuild.

| probe | kind | verdict | what breaks |
|---|---|---|---|
| `PCSchritt.leaf` minus `hmark` | manual field-style | DERIVED-narrow | exactly one proved theorem red: `pcSchritt_markInv` at its use site (`:1506`, `Unknown identifier hmark`); rest of cone green |
| `PCSchritt.leaf` minus `hcar` | manual field-style | DERIVED-narrow | exactly one proved theorem red: `pcSchritt_carrierInv` at its use site (`:1551`, `Unknown identifier hcar`); rest of cone green |

No FORWARDED and no ALONE anywhere in the 24 new probes -- stated
plainly because the mission asked where the weak shapes are. The
narrowest measured couplings, named: each discipline premise rides
conjunct 3 alone among the ten conjuncts (SPLIT, NEEDS only at c3),
but c3 needs the rest too (JOINT on all seven) -- joint use, not a
restatement. `hmark` rides `pcSchritt_markInv` alone among proved
theorems and `hcar` rides `pcSchritt_carrierInv` alone -- narrow by
construction (per-step footprint factoring); the joint side of the
same facts (separation over program text) is measured separately at
the discharge theorems, all DERIVED with B red. The ALONE-weak shape
does not occur in this baseline.

`hGuardEx` / `hWatch` classification, argued from tree evidence:

- `hGuardEx` (every carrier has a guard lock) is a DESIGN BURDEN,
  not a HW assumption. It feeds only c3 and jointly (SPLIT c3,
  JOINT), and the fold consumes it at exactly one obtain site
  (`obtain ⟨L, hL⟩ := hGuardEx c`,
  `InterferenzAllgemein.lean:1553`). The existence shape is static:
  `Bewacht` ties the carrier to `L` through the declaration watch
  lists `D.braucht` / `D.gbraucht`, and shared carriers carry
  non-empty lists by declaration well-formedness (`geteilt_bewacht`,
  `Syntax.lean:178`; `ggeteilt_bewacht`, `:183`). Bounded and named
  (one existential per carrier, one consumer). Discharged by the
  declaration author as a decidable table lookup -- no run reasoning.
  Boundary, stated without smoothing: no checker pass verifies
  guard-list non-emptiness per carrier (U003 verifies holding, not
  existence).
- `hWatch` (writing steps hold the guard, `L ∈ D.haelt`) splits by
  carrier class. For TABLES it is a DESIGN BURDEN discharged by
  checker static analysis: the hook is U003 in `gruppe.rs` (per-body
  comment `:236`, per-write-site imprint `schreibstellen` `:457`
  from `sammle` `:424-434`, verdict `:345`), travelling as
  `J.hSchuld`, proved per body by `schuldnerHaelt_gilt`
  (`InterferenzAllgemein.lean:368`) from U003
  `invarianten_gehalten` (`Syntax.lean:181`) via
  `inv_schreiber_sperren` (`Interferenz.lean:159`) and discharged
  per carrier by `wache_aus_schuld` (`:1481-1495`). For GLOBALS it
  is a CHECKER-SIDE ASSUMPTION (bounded, named): U003 is table-only
  (`D.traeger` lists tables; scope prose `:1321-1332`), so the
  general lemma keeps the watch as its single named premise, which
  for globals is owed, not derived; per-site dynamic holding stands
  nowhere (G3 remainder). The premise is already the bounded form --
  a static declared-holds fact (`D.haelt` shape, prose `:1301-1305`)
  per writing step under one guard -- not a universal runtime claim.

Residual gaps (booked, not hidden):

- R1: per-conjunct + strength for `PCMarkSep` / `PCUnsharedSep` at
  `pc_w1w2w4` / `pc_gesittet` stays unmeasured (two INCONCLUSIVE
  above with mechanical reasons); per-theorem DERIVED stands.
- R2: the manual `hmark` / `hcar` strips have no rest-necessity dual
  (no variant B for constructor args); the joint side is measured at
  the discharge theorems instead.
- R3 (instrument note): `classify_build` folds `unknown constant
  TARGET` / `Unknown identifier TARGET` as self-fallout but not
  capital-C `Unknown constant TARGET`. The downstream
  `Unknown constant` lines in the new logs (`pc_reduktion`,
  `interferenceFree_wo_frei`) are that fallout -- the stripped
  target fails to elaborate, so its name is genuinely missing
  downstream -- and were read as cascade, never as independent
  downstream evidence. No verdict depends on them: every DERIVED
  above rests on the target itself failing in both variants. Left
  as a booked limitation so the code matches the logs.

## Recompute (t02)

```bash
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' \
      --exclude '.claude/worktrees/' ./ ki-pc-fisch-101:gabbro-t02/
rsync -a beweise/ ki-pc-fisch-101:gabbro-t02/beweise/
./instrumente/pruefe-praemisse.py --sprechprobe   # local or fisch, 6/6 PASS
./instrumente/pruefe-praemisse.py \
  ziel_nutzer_last_aus_maschine:hAbD \
  'ziel_nutzer_last_aus_maschine:hFrameTD' \
  'ziel_nutzer_last_aus_maschine:hFrameGD' \
  'ziel_nutzer_last_aus_maschine:hGuardEx' \
  'ziel_nutzer_last_aus_maschine:hEntry' \
  'ziel_nutzer_last_aus_maschine:hReturn' \
  'ziel_nutzer_last_aus_maschine:hWatch'
./instrumente/pruefe-praemisse.py \
  invariantenKontext_aus_disziplin:hAb \
  'invariantenKontext_aus_disziplin:hFrameT' \
  'invariantenKontext_aus_disziplin:hFrameG' \
  'invariantenKontext_aus_disziplin:hGuardEx' \
  'invariantenKontext_aus_disziplin:hEntry' \
  'invariantenKontext_aus_disziplin:hReturn' \
  'invariantenKontext_aus_disziplin:hWatch'
./instrumente/pruefe-praemisse.py \
  'ziel_nutzer_last_aus_maschine:hAbD^c' \
  'ziel_nutzer_last_aus_maschine:hFrameTD^c' \
  'ziel_nutzer_last_aus_maschine:hFrameGD^c' \
  'ziel_nutzer_last_aus_maschine:hGuardEx^c' \
  'ziel_nutzer_last_aus_maschine:hEntry^c' \
  'ziel_nutzer_last_aus_maschine:hReturn^c' \
  'ziel_nutzer_last_aus_maschine:hWatch^c'
./instrumente/pruefe-praemisse.py \
  pc_discharge_einfaedig:hSep pc_discharge_unshared:hSep \
  pc_marke_eindeutig:hSep pc_gesittet:hMSep pc_gesittet:hCSep \
  pc_w1w2w4:hMSep pc_reduktion:hMSep pc_reduktion:hCSep \
  PCSchritt:hmark 'pc_w1w2w4:hMSep^c' 'pc_gesittet:hMSep^c'
```

The manual `hmark` / `hcar` strips follow the recipe in the table
above (binder spans plus the five pattern sites, all in
`grammatik/Grammatik/Maschine.lean`); basis must be GREEN first,
pristine restored after.

Per-probe logs on the invoking host: `/tmp/opencode/t02/batch1.log`
(§9 per-theorem, DERIVED 7), `/tmp/opencode/t02/batch2.log` (fold
per-theorem, DERIVED 7), `/tmp/opencode/t02/batch3.log` (§9
per-conjunct + strength, SPLIT 7 c3-JOINT), `/tmp/opencode/t02/batch4.log`
(PC per-theorem DERIVED 8 + INCONCLUSIVE 3), `/tmp/opencode/t02/batchman3.log`
(manual strips, basis GREEN, single use-site break each); last remote
build log at `/tmp/praemisse-t02-last.log` on fisch.
