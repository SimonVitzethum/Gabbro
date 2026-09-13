# MUSE-REPORT-129 — Translation stage, first cut (PLAN-ERWEITUNG §6 lane E5)

Lane 129, Rust + Lean. Branch `muse/129`. The checker runs the translator at
translation time and checks the payload; the emitter passes an accepted payload
as a `static const` table argument; the certificate is the payload's typing in
encoding N, checked by Lean with `decide`. The translator itself is NOT verified.

## What was built

**Checker** (`crates/gabbro-check/src/uebersetzung.rs`, new, no pass of its own --
verdicts fire through the name pass, the emitter reads the accepted sites):

- Region value, first cut: every raw token parses as an integer literal, token `i`
  fills row `i` of the payload table's single integer field. Anything else stays
  `N069` (captured, not interpreted, exactly as before).
- Runnable translator fragment: only `return <region>;` (identity). Everything else
  is refused by name (`N231`).
- The region fills the library function's LAST parameter, a pointer at the payload
  table. Ordinary arguments are checked against the shortened signature (`m1` trims
  through `fuell_index`, both positions).
- Codes, all owned by this one file: `N230` (integer count vs payload count, span at
  the homeless token / the region), `N231` (non-identity body, at the translator),
  `N232` (entry outside the field range, at the offending region token via the E7
  map), `N233` (three-clause shape rule: untranslatable payload table / no payload
  pointer / explicit payload argument), `N234` (contract names the payload parameter).
  Declaration defects fire once per library function, call defects once per call.
- `payload_certificate` prints the encoding-N certificate; `einsaetze` collects the
  accepted call sites for the emitter in deterministic tree order.

**Name pass** (`namen.rs`): `Uebersetzer` replaced by `uebersetzung::Diener`
(collected once for both readers, plus region parameter and body); `versuch` runs
before `N069` -- accept passes silently, `Abgelehnt` carries its code, `Still`
names an already-reported declaration defect, `NichtZustaendig` keeps `N069`.

**Types** (`m1.rs`, both library-call sites): shortened signature plus shortened
argument list, so the bypassed slot draws no second diagnostic; `requires` over the
filled parameter goes quiet there and is refused as `N234` instead.

**Emitter** (`emit.rs`): `Namen.nutzlast_einsaetze` filled before any body lowers
(bodies lower in the item gang -- filling it beside the tables was measured too
late and every accepted call fell at `C001`); one `static const` payload table per
call site after the tables, named by call span; calls lower to `f(args…,
&payload)`. Statement form discards explicitly (`(void)`, since the callee is
often `pure`); fallible callees have no statement form. `wert_ctyp` answers a
library call's declared result so `let` bindings resolve.

**Corpus**: `beispiele/106-summe-uebersetzt.gab` (region `{10 20 30 40}`, sum 100,
emission runs it), `beispiele/107-summe-zwei-rufe.gab` (two calls, both positions,
two payloads, answers 20); poison `beispiele/gift/905` (`N230` long), `906`
(`N231`), `907` (`N232` at `200`), `908` (`N233`, no payload parameter), `909`
(`N234`, `requires` over the payload).

**Lean** (`grammatik/Grammatik/Uebersetzung.lean`, imported by `Grammatik.lean`):
`nutzlastZert` (encoding-N predicate), `nutzlastZert_mem` (closed certificate
yields every entry's range; both premises used), `sumPayloadVals` /
`sumPayloadOk` / `sumPayload_zert` (`by decide`, the three lines standing
verbatim in the printer, held together by `tests/uebersetzung.rs`),
`nutzlastZert_mem_zeuge` (joint witness at entry 3). Axioms: `nutzlastZert_mem`
`[propext, Quot.sound]`, the certificate axiom-free. No premise quantifies over
program syntax, so rule 13 owes no program witness; the joint data witness is
provided anyway.

**Documents/registers**: `SYNTAX.md` §7.3 (first cut) plus §7 truthful updates;
`namen.bibliothek_ruf` reworded (no longer "every resolved call"), new sentence
`namen.ubersetzung_lauf`; `N230`-`N234` in the `korpus.rs` BENANNT list;
`zeugnis.rs` library-call entry re-booked with the lowering; emission `lauf`s
106/107 with drivers, poison seds and zeugnis lines; `MARKE_EMIT` 85→89;
census re-derived where re-derivable (README/DONE/TODO codes 335→358, examples
89, poison 618, tests 688, EBNF 176, terminals 239, instruments 65/66, blind
78/covered 170/no-cell 12, zeremonie 1548, `gabbro paesse` 144 sentences,
PASSREGISTER 144, vergabe marks 25→29/81→84 with notes).

**Tests**: 12 `translation_*` in `paesse.rs` (acceptance both positions, both
arities, range + span, N231, N069-fallback with M143, shortened-signature arg
checks, explicit bypass); 5 in `tests/uebersetzung.rs` (end-to-end lowering,
two payloads, cc-compile-and-run to 100, printer bytes, Lean mirror).

## Verification (last lines)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (688 tests total).
- `./lean-bau`: `== 0 error line(s) in the COMPLETE output`, `Build completed
  successfully (67 jobs).`
- `./emission-pruef`: `== exit 0 ... == EMISSION: ALL PASS -- 35 durchgestochen,
  230 von 230 uebersetzen, 2 umgekehrte Probe(n) ==` (106 answers 100, 107
  answers 20, all 8 stages each).
- Green: kennungen (ALL PASS, 358), saetze (exit 0, ratchet 55 unmoved),
  grammatiktafel (0/239), wortschatz (239/239), manifest, konstrukte, deckung,
  reichweite, widerruf, sondendeckung, unfalsifizierbar, ausnahmen, aufloesung
  delta zero (see below), vergabe (29/84 match the bumped marks), todo (my
  entries; 6 stale TODO-prose lines stay), englisch count back at baseline 7905
  (one `schon` of mine found and renamed to `done`).

## What remains open (CUTS territory)

Translator loops in Gabbro code, non-integer regions, tree/multi-field payloads,
contracts over the payload, the Lean program-logic channel (`CallStatement`),
and the appended-argument Lean shape (`Bibliothek.args_snoc` passes the payload
as its own argument; this lane's C passes it through the declared pointer
parameter -- two views, one per form). The `N233` three-clause shape waits for a
sixth code, which the 230-234 budget has no room for.

## Pre-existing reds (measured, not mine)

`pruefe-syntax.sh` (referenz snake-case warnings), englisch ratchets
(7881/1069/0), zitate (368), klauseln (`zucker`), aufloesung (4 m1 sites vs 3 --
my 4 moved to Fach 2 by computed-key naming, delta zero), zahlen (~20 drifted
entries incl. RUECKLAUFWERTE/Zeremonie-prose/Widerruf/Blicke/PLAN.md; the
fremde-Ruempfe/PLAN-precondition/blind deltas verified at zero contribution
from this lane), todo (6 TODO-prose lines). `pruefe-praemisse.py` needs ssh
(unavailable); both premises of `nutzlastZert_mem` are used by inspection.
Emission-mark note: the 85 stood two short before this lane (undeclared
emitting files); re-derived to 89.

## Merge resolution (reviewer, master-neu with lanes 89/113/117/121/128 + machine-G)

No code conflicts in lane files (`namen.rs`, `saetze.rs`, `paesse.rs` merged
clean); 8 files resolved -- README/TODO/DONE/PASSREGISTER took ours,
`Grammatik.lean` keeps every import of both sides (`Uebersetzung` +
`CSemantik` + `RufUmkehrRufG`), marks re-measured on the merged tree and
both deltas booked (vergabe 28+1=29 / 83+1=84, emission 87+2=89 with
`100`/`101` identified as lane 89's pair, zeremonie 1526+22=1548).
Merged-tree record: `./cargo-pruef` exit 0, `./lean-bau` 0 errors (69 jobs),
`./emission-pruef` ALL PASS (230/230), kennungen ALL PASS, saetze ratchet 55.

## Task critique (rule 9)

1. Item 2's "translator that walks a token table needs bounded loops, table
   reads, payload construction" presumes translation-time value-construction
   syntax that does not exist (`M140` nominal, `E010` under `pure`): a Gabbro
   translator between two tables has no checkable body today (SYNTAX.md §7.2
   books the same gap). The walk lives in the checker instead; the runnable
   fragment is honestly the identity.
2. "Examples 106-107" collide numerically with `gift/106`/`107` (different
   directories, but the same numbers name unrelated probes).
3. `N069`'s old sentence ("every resolved call refused") became false the day
   the first call translated -- reworded, not deleted.
