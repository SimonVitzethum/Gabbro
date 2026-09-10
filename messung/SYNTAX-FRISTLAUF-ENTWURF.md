# SYNTAX.md subsection draft: expiry shapes (`fristlauf`)

> Draft only, against `536e118`, written 2026-09-10. This file is the
> proposal; `dokumente/SYNTAX.md` itself is untouched. Sources, read first:
> `grammatik/Grammatik/Fristlauf.lean` (shapes, decision, composed outcome,
> speech probe) and `grammatik/Grammatik/Ziel.lean` (the `fristAlsAnnahme`
> mapping, section 3). The deadline clause it extends lives in `SYNTAX.md`
> section 6 and section 18 («SG-22»); the per-date linkage (falsifier,
> manifest, register) is booked in `messung/ZIEL-BEWERTUNG-2026-09-10.md`
> and `messung/SONDEN-ROWS-72.md`.

## Proposed placement

A new subsection at the end of section 18, after the `Maximal writability`
paragraph and before the `---` separator: section 18 stays the time split,
and this subsection gives the split its named expiry shapes. It extends the
`«SG-22» time split` row prose, not the section 6 clause table -- no
production changes, no new syntax, no checker rule.

## The subsection text (as it would stand in SYNTAX.md)

### Expiry shapes -- check at `t`, run at `t'`, expiry strictly between

A deadline names by when, in cycles on a named machine, with a probe that
can refute it. The Lean side (`grammatik/Grammatik/Fristlauf.lean`) gives
that statement named shapes: a check-use pair, a deadline, an explicit
expiry outcome, a decision over a deadline moment, and an answer that maps
expiry onto the hardware assumption. Time never enters as wall-clock --
a moment is a step index, and the probe that measures cycles is named,
never modelled.

| shape | reading | Lean |
|---|---|---|
| `Moment` | a logical moment: a step index into a run, never wall-clock; there is no `Time` type, and that absence is the statement | `Fristlauf.lean`, `abbrev Moment := Nat` |
| `PruefPaar` | check-at-`t` / run-at-`t'`: the check at `pruef`, the use at `lauf`, with the order `pruef < lauf` carried as a field; a use before its check is not writable | `Fristlauf.lean`, `structure PruefPaar` |
| `Frist` | a deadline: the named environment assumption (`annahme`) plus the probe that measures it (`sonde`, e.g. `sonde_tick`); the assumption is what expiry answers, the probe name is what measures it | `Fristlauf.lean`, `structure Frist` |
| `laeuftAb` | expiry-between: the deadline moment lies strictly between check and use, `pruef < d` and `d < lauf` | `Fristlauf.lean`, `def laeuftAb` |
| `FristOut` | the outcome of a deadline run: `ok` (quiet) or `abgelaufen` carrying the deadline whose assumption answers; there is no third | `Fristlauf.lean`, `inductive FristOut` |
| `fristlauf` | the decision: a deadline moment strictly between check and use expires the run under the deadline's name; no deadline moment, or one outside the open interval, is `ok` | `Fristlauf.lean`, `def fristlauf` |
| `fristErgebnis` | the answer: expiry answers `Hardware.fortschritt` with the deadline's assumption; `ok` answers nothing | `Fristlauf.lean`, `def fristErgebnis` |

The betweenness is strict, and the strictness is the rule: either endpoint
coincidence is `ok`, not expiry. A deadline AT the check or AT the use
does not expire the run -- the shape names the open interval, nothing
wider. The speech probe pins it with check at three and use at seven:

| case | deadline moment | outcome |
|---|---|---|
| strictly between | 5 | `abgelaufen` under the probe deadline |
| at the check | 3 | `ok` |
| at the use | 7 | `ok` |
| no deadline moment | none | `ok` |

The decision is exact both ways: the run expires under the deadline's
name exactly when the deadline lies strictly between check and use
(`fristlauf_some_abgelaufen`), and is `ok` exactly when it does not
(`fristlauf_some_ok`), endpoint coincidence included. Composed, the
answer is exact too: `fristErgebnis` over `fristlauf` answers
`fortschritt` with the deadline's assumption exactly on expiry
(`fristErgebnis_fristlauf_some`) and nothing exactly off it
(`fristErgebnis_fristlauf_ok`); with no deadline moment it answers
nothing (`fristErgebnis_fristlauf_none`), and every run is `ok` or
expiry -- no third outcome (`fristlauf_erschöpfend`).

The mapping from deadline to hardware outcome is one definition:

| mapping | reading | Lean |
|---|---|---|
| `fristAlsAnnahme` | the deadline assumption as a hardware outcome: `fortschritt a`, the same assumption that carries `forever` | `Ziel.lean`, `def fristAlsAnnahme` |

It is a definition, not a theorem: the existence sentence once stated
over it was withdrawn on 2026-09-10 as vacuous (an existence claim over
a total function, which every definition satisfies). `Fristlauf.lean`
mirrors the mapping by shape (`.fortschritt f.annahme`) without
importing it; what the shapes mean over a run -- which step counts as
the check, which as the use, what sets the deadline moment -- is cut,
not faked. Trusted and cut, in the file header's own booking: moments
are run order, not the clock, and the probe measures the deadline
without anything here reading it; there is no wiring into device runs
or `exec` fuel, no duration arithmetic (a deadline is a moment, not a
span), and the `Ziel.lean` mapping is cited by shape.

Each date carries the same fourfold linkage, one row per date:

| per-date item | content |
|---|---|
| deadline clause | `deadline <= n ops arch X falsifier p` at `fn` (section 6); structural checks `K011` (the number reads) and `K012` (the machine is declared, R16) |
| falsifier probe | the named probe `p`; when it resolves in-unit its shape is held by `N056`; an unresolved probe is a program next to the tree, and `unfalsifiable` stays legal and marked |
| manifest entry | `frist_<fn>_eingehalten` with the class |
| register row | one row per date naming the obligation and its probe; PROGRAM once the probe exists as a program |

The sample that makes the linkage concrete: `sonden/sonde_tick.c` for
`frist_zaehle_werte_eingehalten` (`beispiele/71`), sample currency
(R15/W10, locks excluded and said so), booked as register row 39
PROGRAM. A date is then named and run; the Lean side still proves
nothing about time -- time stays a hardware outcome, and the checker
verifies only its paperwork.

## What this draft does not move

No edit to `SYNTAX.md` (this file is the only change); no new
production and no `ebnf` block (the clause already exists in section
6); no new checker or emitter rule; no proof about time (the mapping
is cited, the measurement belongs to the probe). Merging it means
copying the subsection above into section 18 at the proposed place,
nothing else.
