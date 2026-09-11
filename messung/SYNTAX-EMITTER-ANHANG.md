# Emitter-chain annex: what "no verified emitter" means, per cut

Ledger over `grammatik/Grammatik/Erhaltung.lean` at base `2dc02ad`, written
2026-09-11. It kills the bare sentence "no verified emitter" as an
undocumented claim: each cut below names its status (PROVEN, SHAPE, OPEN),
the witness that decides it, and the command that recomputes it. Nothing
here goes beyond what the tree holds; where the tree is stale or cites
absent notes, the ledger books the skew instead of smoothing it.

Naming note, because two systems share three names. The census classes
C1/C2/C3 (`dokumente/BEWEIS.md` Item 2, lines 731-919: used-and-forbidden,
used-and-unlisted, used-under-generous-reading) are DATA. The spec cuts
C1/C2/C3/C6 (header of `Erhaltung.lean`, lines 53-90) are the contract
positions on that data. This annex follows the SPEC cuts; census ruling
state is booked under C2, where the witness pairs belong.

## Proved legs (used by every cut)

All in `Erhaltung.lean`, each theorem followed by a `#print axioms` line
(lines 679-693) naming only the standard axioms (`propext`,
`Quot.sound`), no `sorry`, no `admit`, no new axiom:

| leg | decides | where |
|---|---|---|
| correspondence recomputation (`vollB_sound`, `ohneExtraB_sound`, `geordnet_sound`, `geordnetCertB_sound`, `geschlossenB_sound`, `geschlossen_immer`, `korrespondenz_aus_vieren`, `korrespondenz_sound`, `korrespondenz_leer`) | a valid certificate IMPLIES the four correspondence sentences; the empty run satisfies them | §6, lines 366-557 |
| alias discharge (`alias_leer`, `census_steht`) | the empty site list keeps the alias obligation; the census number stands as data (`ptrArithCensus = 491`) | §7, lines 559-580 |
| cost legs (`kosten_cerCo_gilt`, `kosten_produktion_frei`, `gemessen_produktion`, `gemessen_cerCo_frei`, `traeger_trennt`, `senkung_aus_schranke`, `kosten_satz_bauen`) | CerCo MAY claim preservation, production only measurement; the lowering bound holds from the measured bound | §8, lines 582-659 |
| debt, proved real (`tafel_nicht_geschlossen`, `vertrag_braucht_tafel`) | the table does not close today, and the contract does not hold today | §9, lines 661-691 |

Recompute: `lake build` (checks the file through the `Grammatik.lean`
import, line 61), then `lake env lean Grammatik/Erhaltung.lean`.

## C1 — the recomputer stays cut: SHAPE proved one way, OPEN the other

PROVEN: the valid-cert-implies-correspondence direction (§6 above). OPEN:
nothing PRODUCES a valid certificate — no definition in the file reads
`crates/`, and the only line mentioning `emit.rs` is the cut comment
itself (line 56). The second program with its own pattern, the one the
`checkfat.py` lesson demands, does not exist here.

Witness: the §6 theorems for the proved direction; for the open direction,
`grep -n "emit.rs" grammatik/Grammatik/Erhaltung.lean` returns line 56
alone (a comment, not a definition).

Recompute: `lake env lean Grammatik/Erhaltung.lean` for the proved half;
`grep -n "emit\.rs\|crates/" grammatik/Grammatik/Erhaltung.lean` for the
open half — a hit outside a comment would move this cut.

## C2 — what a C form means stays cut: PROVEN closure, OPEN meaning

PROVEN: every named shape IS tabled (`geschlossen_immer`, `ruledB_voll`;
§6). The census itself is counted, not asserted
(`instrumente/zaehle-c-formen.py`; `dokumente/BEWEIS.md` lines 776-841:
64 forms over 8001 lines of C, 30 undecided at count time).

SHAPE: a form's meaning rides on the hand-written table entry plus its
executable witness pair, and the common-mode failure (both tables from one
text) is named, not closed (`dokumente/SYNTAX.md` §21.1, §21.5).

Witnesses, measured 2026-09-11 in this worktree, all green:

| set | pairs | result |
|---|---|---|
| `messung/zeugen-c1/*.sh` (7: define, enum, include, index-on-ptr, ptr-arith, ternary, typedef) | Gabbro fragment, expected C, expected behaviour at `-O0`/`-O2`/`-Os` | 7 of 7 PASS |
| `messung/zeugen-c2/z01`–`z19` (void through static-assert) | same triple-level shape per form | 19 of 19 PASS |

Ruling state, as the tree holds it: 18 notes under `messung/CFORM-REGEL-*.md`
each read "admit with price, no emitter change"; the `tafel` in
`Erhaltung.lean` (lines 273-324) carries 8 `offen` rows
(`zeigerArithmetik`, `cInclude`, `cTypedef`, `cDefine`, `cEnum`, `voidTyp`,
`cAttribut`, `cSizeof`). The `?:` template is filled (fold table in
`BEWEIS.md` §1b, `bedingtEntscheid` decided in the table) while the
generator is unchanged (`emit.rs` lines 2110-2111 still write the ternary;
the `BEWEIS.md` fix checkbox stays open). The `__builtin_unreachable`
remainder is admitted with its proof-export price (`unerreichbarBuiltin`
row: one kept site under `D005` plus the tag invariant).

Two skews, booked, not smoothed. First, `dokumente/SYNTAX.md` §21.4 still
says 29 slots stand `offen`; the Lean table says 8. The prose is stale
against the table, and this ledger does not resolve it. Second, 7 table
rows cite `messung/CFORM-REGEL-SENKUNG-142.md`, `-SENKUNG-144.md`, and
`-ZULASSUNG-143.md` (`Erhaltung.lean` lines 308-318), and none of the
three notes exists at this base. The price text stands in the status
field; the cited note does not.

Recompute: `for f in messung/zeugen-c1/*.sh messung/zeugen-c2/*.sh; do
bash "$f" | tail -1; done` (26 lines, each naming its PASS/FAIL per level);
`./instrumente/zaehle-c-formen.py` for the census;
`./instrumente/pruefe-emission.sh` for the full emission gate (stage 9
compiles every emitting unit); `ls messung/CFORM-REGEL-SENKUNG-142.md
messung/CFORM-REGEL-SENKUNG-144.md messung/CFORM-REGEL-ZULASSUNG-143.md`
for the absent notes — it must fail until they land.

## C3 — `restrict` and `volatile` stay trust: SHAPE, nothing proved

No theorem touches either. Both are carried as data: `beschraenktPreis`
("exports the effects-promise into C UB rules; only where the benchmark
buys it") and `fluechtigPreis` ("axiom, named; seL4 excludes exactly
this") in `Erhaltung.lean` (lines 262-267), wired into the table rows
`.beschraenkt` and `.fluechtig` (lines 289-290). The UB inventory gives
the same prices outside Lean (`dokumente/BEWEIS.md` §2, rows 2/5/11/12;
row 11 is the `restrict` row).

Witness: the two price strings plus the inventory rows they mirror.
Adequacy of either price is unproved and stays unproved here.

Recompute: `grep -n "beschraenktPreis\|fluechtigPreis"
grammatik/Grammatik/Erhaltung.lean` — the shape is present exactly where
the table reads it.

## C6 — the rechecker stays an interface: SHAPE, no theorem

PROVEN: `nachpruefer` is a Boolean function over `NachprueferEingabe`
(lines 700-722): correspondence recomputed, alias list decided empty,
cost claim decided kept and measured, statement count decided under the
bound 17. Acceptance and rejection both close by decide.

SHAPE: `satz_nachpruefung_vertrauen` (lines 732-737) is a `def`, a Prop —
section 10 (lines 693-737) holds 0 `theorem`/`lemma` lines against 4
`def`/`structure` lines, measured. The bridges from the legs to the
sentences are not here, and the second program that reads the run
artefacts is not here either (same class as C1).

The bound 17 is the static count of `messung/ABSENKUNG-MESSUNG.md`
(maximum 17 at `traverse over descendants of`), recorded in
`messung/ABSENKUNG-ZAEHLUNG.md`; its lexer confirmation stays open, and
`senkung_aus_schranke` (§8) proves only the conditional.

Witness: the theorem count of section 10 (zero) beside the decidable
`nachpruefer` definition.

Recompute: `sed -n '693,737p' grammatik/Grammatik/Erhaltung.lean | grep -c
"^theorem\|^lemma"` must print 0 — the first theorem inside that span
moves this cut; `lake build` for the shape still checking.

## Recompute index

| cut | command | must show |
|---|---|---|
| C1 proved | `lake env lean Grammatik/Erhaltung.lean` (after `lake build`) | clean check |
| C1 open | `grep -n "emit\.rs\|crates/" grammatik/Grammatik/Erhaltung.lean` | line 56 alone |
| C2 witnesses | `for f in messung/zeugen-c1/*.sh messung/zeugen-c2/*.sh; do bash "$f" \| tail -1; done` | 26 PASS lines |
| C2 census | `./instrumente/zaehle-c-formen.py` | 64 forms, current undecided count |
| C2 gate | `./instrumente/pruefe-emission.sh` | green through stage 9 |
| C2 notes | `ls messung/CFORM-REGEL-SENKUNG-142.md messung/CFORM-REGEL-SENKUNG-144.md messung/CFORM-REGEL-ZULASSUNG-143.md` | must fail at this base |
| C3 | `grep -n "beschraenktPreis\|fluechtigPreis" grammatik/Grammatik/Erhaltung.lean` | the two price definitions |
| C6 shape | `sed -n '693,737p' grammatik/Grammatik/Erhaltung.lean \| grep -c "^theorem\|^lemma"` | 0 |
