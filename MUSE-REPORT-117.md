# MUSE-REPORT-117 — lane E6 checker half: hardware profile in the checker

Lane 117, fifth wave. Task: `PLAN-ERWEITUNG.md` §0c lane E6 checker half (+ `SYNTAX.md`).
The Lean model exists (`grammatik/Grammatik/Profil.lean`, lane 66) — this lane builds the
language form: surface, checker, manifest, probes. No Lean changes; `./lean-bau` green,
last result line: `Build completed successfully (61 jobs).`

## What was built

**Surface (`SYNTAX.md` §12.2, `crates/gabbro-syntax`).**
The main program declares `profile { arch x86_64; rounding nearest; fp_contract off;
…; assume <name>; }`; a library declares `requires profile { <key> <value>;
assume <name>; }`. Keyed entries come from the fixed key set
(`arch` exists; new words `profile`, `rounding`, `fp_contract`, `memory_model`,
`interrupt_routing`, all `ctx`), values and referenced names are identifiers.
Three EBNF rules (`profiledecl`, `requiresprofile`, `profileentry`), reachable
from `program` via `item`; both blocks close with `;` (concurrentdecl precedent).

New AST (`crates/gabbro-syntax/src/ast.rs`): `ProfilSchluessel`
(`Arch`, `Rundung`, `FpKontraktion`, `SpeicherModell`, `InterruptRouting`, mirrors
Lean `ProfilSchluessel`), `ProfilEintrag` (`Modus { schluessel, wert, span }`,
`Annahme { name, span }`), `ProfilBlock { eintraege, span }`,
`ItemArt::Profil(ProfilBlock)`, `ItemArt::ProfilBedarf(ProfilBlock)`.
Reader (`parse.rs`): `profildecl`, `profilbedarf`, shared `profilblock`;
malformed entries reuse `P006`, a bare `requires` still falls as before.

**Checker (`crates/gabbro-check/src/namen.rs`, `profil_pruefen`, wired behind
`bibliothek_pruefen`).** New codes `N215`–`N219`, all issued from this one file:

| code | rule | probe |
|---|---|---|
| `N215` | two keyed entries, one key, different values (per block; same-value dups silent) | gift 890 |
| `N216` | same-named assumption with different content (a profile reference meeting two declarations under its name) | gift 891 |
| `N217` | linking: every library requirement stands in the program profile with identical content (key+value, or name+content à la `Profil.bindet`); unit-wide, no-profile-at-all falls per requirement | gift 892 |
| `N218` | profile against the platform: `fp_contract` other than `off` contradicts the float prelude binding `-ffp-contract=off` (`PLAN-BITS.md` §5); `arch` beside every declared machine (silent with no declared machines, R16 shape) | gift 893 |
| `N219` | structure, two arms one code (N065 precedent): second `profile` block; `assume` reference resolving nowhere | gift 894 (both arms) |

References resolve through `Umgebung::kandidaten_aufloesbar` (own module,
enclosing, root, `use` lines). `Umgebung` grew three owned fields for this
(`profile`, `bedarfe`, `annahmen`), stored raw like `nutzlasten`, read at the
use site. All five refusal texts classify as load-bearing (`tragend`) under
`pruefe-gruende.py`.

**Manifest (`manifest.rs`, `profil_und_bedarf`, flows into `gabbro annahmen`
and the emitted C header).** One line per keyed profile entry
(`profile.<key>`, art `profile`; the `fp_contract off` line carries the
`-ffp-contract=off` flag — the manifest flag the task requires), one line per
library requirement (name `lib#req`, art `requires`, with the library and the
relying `@lib` callers in the line; an `assume` requirement clones the
referenced assumption's class, so no new `Klasse::Falsifizierbar` site).
Requirement names carry the library, so a requirement never collides with the
assumption it references under `vereinige`. Emitter and certificate
(`emit.rs`, `zeugnis.rs` incl. two `EINORDNUNG` rows) carry the forms.

**Sentences (`saetze.rs`).** Five measured sentences
(`namen.profil_schluessel/-namensgleichheit/-bindung/-plattform/-gestalt`),
one code each; the `ohne Satz` ratchet stands unmoved at 55 over 335 codes.

**Probes and examples (assigned numbers only).** Gifts 890–894 (one code each:
conflict, same-name, missing requirement, `fp_contract fast`, second
profile + dangling reference). Clean examples 100 (profile + library
requiring a subset, with `assume plattform_takt_stabil`/`sonde_tick`) and 101
(remaining keys, keyed-only requirements). No `@lib` calls in clean files —
a resolved call still carries `N069`, so calls live in the poison corpus.
`paesse.rs` pins every code plus the positive direction (13 `profil_*`
tests); `tests/manifest.rs` pins profile lines, library+callers, class
cloning, and the no-collision property.

## Measurements (all on this machine)

- `./cargo-pruef`: exit 0, 0 failing tests (last full run after every change).
- `./lean-bau`: `Build completed successfully (61 jobs).` (Lean untouched.)
- `./emission-pruef`: stage 9 red — pre-existing, not mine: `MARKE_UMGEKEHRT`
  expects 4 biting `-- erwartet: cc` probes, 2 bite (`414`,
  `probe-eintritt-parameter`); `probe-eintritt-privat/-zwei` now fail at the
  checker (`N041` on `main`, the entry lane's repair) instead of at `cc`.
  The stale headers are that lane's to reclassify (as the N042 lane did for
  413/417/418). `NEUE WURZEL EMITTIERT` (stray `Claude outputs/`, `halde.gab`)
  is likewise pre-existing. My examples emit and compile under `cc -Werror`
  at `-O0`/`-O2` (229 emitting files, +2 mine, no other count mark moved).
- Guardians moved by earned growth (all green after): `pruefe-sondendeckung`
  (`19 of 52`, floor `1/8`; `MARK_QUOTE` 18/51 → 19/52, row 52 added with its
  program, elf set +`sonde_tick`, stress 94 → 101 — each with its ledger
  entry), `pruefe-unfalsifizierbar` (`MARK_RS_SITES` 4 → 5 for the one new
  `profilklasse` site), `zaehle-wortschatz` (`MARKE_WOERTER` 231 → 236, each
  word with its own reason block; 212/17 unmoved), `pruefe-wortschatz`
  (233/233 both readings), `pruefe-syntax.sh` (ALL PASS incl. warnings),
  `pruefe-grammatiktafel` (0 of 233 uncovered), `pruefe-saetze`
  (135 sentences, 280 claimed, 55 unmoved), `pruefe-kennungen` (335, ALL PASS),
  `pruefe-konstrukte` (27 read), `pruefe-todo` README table green.
- Guardians red before this lane, red after (verified; mine contributes
  nothing — details below): `pruefe-manifest` (E1 gate, booked red),
  `pruefe-englisch` (+24 German comment lines over the mark; my diff
  contributes 0, measured with the guardian's own classifier),
  `pruefe-zahlen` BEFUNDs on RUECKLAUFWERTE/Zeremonie/Widerruf/Blicke/
  Zeilenfortsetzungen/Mutationsanker-ZUSAGE/Absagetexte/Saetze-122
  (wave drift; my lane's lines — Sätze/Codes/Absagekennungen/Item-Arten/
  EBNF/PLAN-A/A_p/SONDENDECKUNG — all booked to actuals),
  `pruefe-vergabe` (24 candidates at baseline vs mark 20; +3 mine: `P006`,
  `N218`, `N219` — the price of two-arm codes, N065 precedent),
  `pruefe-klauseln` (`region`, `zucker` — lanes E1/BITS), `emission-pruef`
  (above). `pruefe-syntax.sh` without cargo on `PATH` aborts at the
  warnings stage (environmental; green with `PATH` set).

## What remains open

- E5 (translation stage with certificate) still refuses every resolved
  `@lib` call with `N069` — calls relying on profile requirements are
  therefore listed by the manifest but never linked in a passing build.
- Value sets are unchecked except `fp_contract = off`: any identifier passes
  as a `rounding`/`memory_model`/`interrupt_routing` value.
- `N217` is unit-wide (an unused module's requirements still link); carved
  deliberately — the unit IS the program — but a multi-unit build will want
  it per `use` edge.
- Profile blocks emit nothing; a `profile` in dead code is still the profile.

## What I believe is wrong in the task

- "The existing `arch` declaration … must be consistent with the profile"
  reads both ways, but only the refusal direction is specified (and only for
  `fp_contract` is the content pinned). I refused unknown-`arch` values and
  left the converse (declared machines missing from the profile) silent:
  a program for two machines with a one-machine profile passes. If the
  converse was meant, it needs its own code — the 215–219 band is spent.
- Gift 894 covers both `N219` arms in one file (one `-- erwartet` line can
  name one code). Arm-level precision lives in `paesse.rs`
  (`profil_zweites_profil_n219`, `profil_haengender_verweis_n219`); the same
  split E2 used for 824 (`N059` beside `N069`).
- Reusing `sonde_tick` for row 52 makes one probe cover two rows, which the
  floor tooth's "smallest breaking set" arithmetic did not foresee (a
  twelve-probe set — tick plus any eleven — now breaks where thirteen was
  booked). The tooth removes the thirteen newest and still passes; the
  wrinkle is carried in its comment, not hidden.

## Names of new items (Rust; no new Lean items)

`Kw::{Profile, Rounding, FpContract, MemoryModel, InterruptRouting}`,
`ProfilSchluessel::{Arch, Rundung, FpKontraktion, SpeicherModell,
InterruptRouting}` (+ `::text`), `ProfilEintrag::{Modus, Annahme}` (+ `::span`),
`ProfilBlock`, `ItemArt::{Profil, ProfilBedarf}`, `parse::{profildecl,
profilbedarf, profilblock}`, `Umgebung::{profile, bedarfe, annahmen}`,
`namen::profil_pruefen` (+ `inhalt`, `loese_auf`), `manifest::{profil_und_bedarf,
profilklasse, profil_grund, profil_aussage}`, saetze
`namen.profil_{schluessel, namensgleichheit, bindung, plattform, gestalt}`,
EBNF `profiledecl/requiresprofile/profileentry`, SYNTAX.md §12.2.
`CUTS:` nothing proved here is claimed beyond its probes — the Lean profile
theorems (`profil_modell`, `bindung_fuegt_nichts_hinzu`,
`widerspruch_abgelehnt`) are lane 66's, untouched; no `#print axioms` added
because no theorem was added.

## Merge with master-neu (reviewer, 2026-09-12)

Resolved per instruction: `kw.rs` + `zaehle-wortschatz.py` keep both sides
(E6 profile words beside E3 `translator`/`for`; mark 236 → 238 with both
ledger lines); `SYNTAX.md` keeps both productions and vocabulary rows with
re-measured counts (173 EBNF rules — lane 111's `constwert`/`arraylit` found
by the union diff, not assumed; 235 terminals both readings; heading 239);
`saetze.rs`/`paesse.rs` keep both lanes' sentences and tests;
README/TODO/DONE/PASSREGISTER taken `--ours`. `./cargo-pruef` green after
adding the now-mandatory `translator build for …` to examples 100/101
(master's `N200` refused translator-less `library fn`s). `./lean-bau`
green (64 jobs). Known aftermath, not mine: PASSREGISTER/TODO corpus
figures now underbook master's sentences/codes/examples (reviewer-accepted
`--ours`); `pruefe-syntax.sh` warnings stage names two snake-case test fns
from master's `referenz` test.
