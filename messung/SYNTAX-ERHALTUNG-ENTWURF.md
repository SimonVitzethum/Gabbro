# SYNTAX §19 draft — the producer contract (Erzeugervertrag)

*Design only, 2026-09-10, lane-37. This file is the DRAFT for a new
`dokumente/SYNTAX.md` section 19; it does NOT edit `SYNTAX.md`.
The Lean shapes it quotes live in `grammatik/Grammatik/Erhaltung.lean`
(self-check: `lake env lean Grammatik/Erhaltung.lean` in `grammatik/`).
No emitter verification happens in this lane -- the emitter stays the
trust base, and this draft specifies what it must uphold.*

## Proposed §19 text

### 19. The producer contract — what the emitter must uphold

§18 closed the C side as a list (`Ziel.lean` `CForm`: 19 named shapes).
A closed list is not a contract until somebody says what upholding it
takes, per run, in checkable form. That is this section. It claims no
verified emitter: every sentence below is specified in
`Grammatik/Erhaltung.lean` as a `Prop`-valued `def` -- the SHAPE of a
later proof, not the proof. The five later sentences are named
`satz_korrespondenz`, `satz_alias`, `satz_kosten`, `satz_tafel`, and
their conjunction `satz_erzeugervertrag`.

#### 19.1 Correspondence — one certificate per run (`BEWEIS.md` §4)

Each compilation run produces a coverage certificate: one row per
evaluation site, `CorrSite = gabbroSite × cSite × form`, collected in
`CorrCert`. The emitter earns trust when four shapes hold
(`satz_korrespondenz`):

1. **Completeness** (`corrComplete`) — every Gabbro evaluation site
   appears at least once.
2. **Order** (`corrOrdered`) — the C sites stand in the same order.
3. **Closure** (`corrClosed`) — every C form in the image is a decided
   row of the table in §19.4.
4. **No additional effect** (`corrNoExtra`) — no C site without a
   Gabbro preimage.

The recomputer is a second program with its own pattern, not the same
code called twice (`checkfat.py` lesson); what is accepted is the
mutation list, not the existence of the checker. A deliberately
displaced evaluation site must be noticed. The common-mode failure
(both tables from one text) is named, not closed; the witness pairs of
§19.5 are the only instrument against it.

#### 19.2 Alias — no address arithmetic in the image

§2 row 2 promised the emission generates no pointer arithmetic, and the
census measured 491 sites of it (`d->basis + 8`, `v->bytes + 4`).
The row is rewritten by this section: the obligation is
`AliasObligation`, the list of address-arithmetic site ids in the
image, fulfilled (`aliasKept`, `satz_alias`) exactly when the list is
empty. Until then every entry is a named site, and the census number
stands as data (`ptrArithCensus = 491`), not as residual risk "none".
The two declaration shapes behind the count are named in the spec
(`ArithSource`: `basisPlus` over `volatile uint8_t *`, `bytesPlus`
over `uint8_t *`). The sibling slot `zeigerIndex` (156 sites) is NOT
covered by ruling `index` as named: `p[i]` IS `*(p+i)` by C's own
definition, and the table must say whether it means that too.

#### 19.3 Cost — CerCo preserves, production is measured

The budget counts Gabbro-side steps (`costs`, `per_pass … ops`); what
happens to the number across lowering is a claim with a named carrier
(`CostCarrier`), and the carrier is data, not prose:

- `cerCo` — quantitative CompCert: the C count IS the Gabbro count
  (`costKept`). Preservation may be CLAIMED here, once the carrier stands.
- `produktion` — the production compiler: the count is MEASURED by
  witness pairs (`costMeasured`: `paare` pairs ran green; zero pairs is
  not a measurement), never proved.

The Gabbro-side leg is the bounded lowering (`senkungBegrenzt` over
`Absenkung`: one primitive becomes at most `proPrimitiv` C statements).
`satz_kosten` conjoins all three legs. Wall-clock and cycles never enter:
same boundary as `Ziel.lean` (§18 «SG-22») -- a deadline is
`hardware (fortschritt a)` with its probe, not a second budget.

#### 19.4 The ruling table — 19 named, 30 slots, one status field

Every row is an `EntscheidZiel`: either a named shape or a census slot,
each WITH a `RulingStatus` (`offen` | `aufListe preis` |
`ausErzeuger ersatz`). The status field is what makes 30 holes countable
instead of invisible; `entschieden` says when a row stopped being debt.

- The **19 named shapes** (`CForm`) stand admitted with the price of
  their semantics named. Two prices carry real trust and say so:
  `beschraenkt` exports the effects-promise into C's UB rules (priced
  option, never default), `fluechtig` is an axiom by name. These 19
  admissions are the TEMPLATE ruling, not 19 rulings (cut C5 below).
- The **30 census slots** (`OffeneForm`: 7 used-and-forbidden, 19
  unnamed-and-uncovered, 4 generously covered) stand `offen`, with two
  exceptions that show the two ways out: `bedingt` carries the filled
  template (`bedingtEntscheid`: the generator writes
  `if (v > z) { z = v; }` -- costs nothing at `-O0`/`-O2`/`-Os`,
  byte-identical at the top two), and the four generous readings plus
  the kept `unerreichbarBuiltin` site carry their admission price.
- `satz_tafel` (every row decided) is FALSE today -- 29 slots still
  `offen` -- and that is the point: the shape counts the debt. Ruling
  by taste is what produced a list with 30 holes; each of the 19
  unnamed forms is ruled one by one the way `?:` was, onto the list
  with the price of its semantics or out of the generator with the
  price of the change. Deciding `?:` alone does not close the class:
  `logUndOder` (23 sites) is the same conditional door, undecided,
  and the float row (`floatTyp`/`doubleTyp`, 26 sites) is a missing
  row, not a missing word.

#### 19.5 Witness pairs — the instrument the table was missing

Every table entry gets an executable witness pair: a Gabbro fragment,
the expected C, the expected behaviour -- run through the REAL C
compiler and compared. With that the entry's meaning is checkable
instead of hand-trusted, and an entry without a witness pair is
incomplete. `costMeasured` counts these pairs on the production leg.

#### 19.6 What this section does NOT move

- No verified emitter: the certificate is specified, the recomputer is
  a later program (cut C1).
- No formal C semantics: meaning lives in the table entry plus its
  witness pair (cut C2).
- `restrict` and `volatile` stay trust, priced and named (cut C3).
- The 19 admissions are template, each still owes its `?:`-style
  ruling (cut C5).

## Lean ↔ draft mapping

| draft | Lean (`Grammatik/Erhaltung.lean`) |
|---|---|
| §19.1 rows / certificate | `CorrSite`, `CorrCert`, `corrComplete`, `corrOrdered`, `corrClosed`, `corrNoExtra` |
| §19.2 alias obligation | `ptrArithCensus`, `ArithSource`, `AliasObligation`, `aliasKept` |
| §19.3 cost carriers | `CostCarrier`, `CostClaim`, `costKept`, `costMeasured`, `senkungBegrenzt` |
| §19.4 ruling table | `RulingStatus`, `OffeneForm` (30), `EntscheidZiel`, `tafel` (19+30), `bedingtEntscheid`, `entschieden` |
| later sentences (shapes) | `satz_korrespondenz`, `satz_alias`, `satz_kosten`, `satz_tafel`, `satz_erzeugervertrag` |

## Cuts carried over (not hidden)

C1–C5 stand in the Lean header and §19.6: emitter trust base, no
meaning model, `restrict`/`volatile` as trust, no index wiring (the
file is checked directly, never imported by `Grammatik.lean` in this
lane), template admissions.

## Acceptance

- `lake env lean Grammatik/Erhaltung.lean` in `grammatik/` prints only
  the three `#print axioms` lines (`propext`, no axioms beyond the
  standard ones, no `sorry`/`admit`/`axiom`, no `theorem`/`lemma`/`example`).
- `dokumente/SYNTAX.md` untouched (this file is the draft, §19 proposed).
- `crates/` untouched; `Grammatik.lean` index untouched.
