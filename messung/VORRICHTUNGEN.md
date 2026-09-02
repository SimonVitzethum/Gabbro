# VORRICHTUNGEN — the fixtures the instruments carry, and how deep each was checked

*Measured 2026-09-02 over `master` at `a2cd217`. Derived with
`python3 instrumente/pruefe-waechter.py` for the population, and by reading all 63 files in
`instrumente/`.*

**Status: IN PROGRESS.** Rows are written as they are measured. A row that is here has been
measured; a row that is missing has not.

## The question

An instrument rests on a **fixture**: something hand-made and trusted that the measurement
cannot check for itself. The class this document measures:

> **A fixture is only as good as the deepest stage it was validated at, and this repo has
> been caught reading fixtures for more than they were checked for.**

The stages, in increasing depth:

| # | stage | what it proves |
|---|---|---|
| 1 | `gabbro check` | the source is accepted by the checker |
| 2 | `gabbro emit` | the source also reaches C |
| 3 | `cc` | the emitted C compiles |
| 4 | executed and compared | the compiled program runs and answers |

A fixture validated at stage 1 and read as good at stage 3 is the shape named `D1`
(`messung/ERZEUGERSWEEP.md` §3): *"A baseline is only good against the question it was
asked."*

The fixture kinds worth telling apart:

| kind | what it is |
|---|---|
| **baseline program** | a `.gab` or `.c` file treated as known-good |
| **template** | a source skeleton the tool fills or mutates |
| **golden output** | an expected diagnostic or stdout text compared literally |
| **known-good input** | an input the tool assumes the object accepts |
| **anchor** | a literal line of `crates/` source quoted inside the tool |
| **expected value** | a hand-written count, ratchet or mark |
| **name pattern** | a glob or regex that decides WHICH files are measured |

The last two are fixtures in the same sense as the first: **an expected value that nobody
re-derives, and a glob that quietly selects nothing, both make a tool green over nothing.**
That is how `pruefe-waechter.py` was green over 57 tools while the three that could redden
it were named outside its own glob.

## The layer, before the rows

**How far into the ladder the instrument layer reaches at all** — measured mechanically over
all 63 files (call sites for `gabbro check`/`emit`, for `cc`/`clang`, and for executing a
produced program):

| | tools |
|---:|---|
| touch **no** build stage — pure text over `.md`, `.rs`, `.gab` as TEXT | **39** of 63 |
| reach stage 1 or 2 (`check` / `emit`) | 24 of 63 |
| reach stage 3 (`cc` or `clang`) | 14 of 63 |
| reach stage 4 (**execute** the produced program) | **1** of 63 — `pruefe-sonden.sh` |

*The ladder's top rung is held by a single instrument.* Everything else that claims
something about a running program claims it from a compiler's return code at most. This is
not itself a defect — but it fixes the ceiling: **no instrument other than
`pruefe-sonden.sh` can validate a fixture deeper than "the C compiles".**

For the 39 pure-text tools, the ladder does not apply, and the corresponding question is a
different one with the same shape: **does a stale anchor or an empty population redden, or
does it go silently green?**

## Counts

**63 instruments. 61 carry a fixture. 45 of those check it. 40 check it deeply enough.**

| | |
|---:|---|
| **63** | instruments in `instrumente/` |
| **61** | carry a fixture (only `abschnitt.py` and `abschnitt.sh` do not — both are shared libraries, not measurements) |
| **45** | of the 61 subject their fixture to some check of their own |
| **40** | of those 45 check it at a depth the claim actually needs — **no mismatch** |
| **21** | read at least one fixture for more than it was checked for |

*Say the good half plainly, because it is the larger one:* **forty of sixty-one instruments
rest on a fixture that is validated at the depth their own verdict needs.** Repeatedly, a
tool was found to invent its own subject and run it through the real pipeline rather than
trust a constant — `abnahme.py` writes seven fake guardians and runs them; `zaehle-netz.py`
computes an RFC checksum a second, independent way and demands one altered byte change it;
`pruefe-lean-beweis.sh` requires `lean` to *fail* on a poison theorem; `pruefe-emission.sh`
makes every executed fixture prove itself by mutating it and demanding a different answer.
**`D1` is the exception in this layer, not the rule.**

### And the shape of the 21 is not the shape that was expected

The hunt was for the `D1` ladder — a fixture validated at `check` and read at `cc`.
**Measured, that is 2 of 63.** The other nineteen fail in three other ways, and the largest
family never touches the build ladder at all:

| family | what goes wrong | n |
|---|---|---:|
| **A — the population that can be empty** | a glob or a hand-written file list selects the subject, nothing checks it selected anything, and zero findings over zero files prints as a clean pass | **8** |
| **B — checked, printed, not gated** | the tool *computes* whether its fixture still holds, prints the answer, and the exit code ignores it | **3** |
| **C — the constant nobody re-derives** | a table, a mark or an address written by hand, consumed with full trust, never compared against the thing it transcribes | **8** |
| **D — one stage too shallow** (the literal `D1` shape) | validated at `check`, read at `cc`; or validated at the generated text, read as a claim about a proof | **2** |

**A** is the finding that generalises. Eight instruments can be handed an empty subject and
will answer *"nothing found"* rather than *"nothing measured"* — and the folder already knows
the difference and has the words for it: `zaehle-traversierungen.py` writes
`"ABBRUCH: der Lehrkorpus fehlt -- es wird NICHT null gemessen"` for one of its two corpora
**and not for the other.** `zaehle-lean.py` has no such guard while its own sibling over the
same corpus, `pruefe-lean-beweis.sh`, aborts on zero goals. *The guard is not missing from
the repo's vocabulary. It is missing from half the places that need it.*

**B** is the smallest family and the most alarming, because in `B` the instrument has
already done the work. `pruefe-luecken.py` owns the machinery to detect a dead anchor,
calls it for thirteen anchors and wires the result into its exit code — and for the two
`NULLMUTATION` anchors takes a branch that skips the call entirely. **One of those two
anchors is dead today** (below). `zaehle-bereichspflichten.py` prints, in its own words,
*"Dann misst dieser Lauf nichts (Vorab-Protokoll: ungueltig)"* and then returns `0`.

## The table

| instrument | fixture? | kind | validated at | property CLAIMED | mismatch |
|---|---|---|---|---|---|
| `abnahme.py` | yes | template: seven invented guardians (`pruefe-gruen.sh`, `-rot.sh`, `-halt.sh`, `-sturz.py`, `-halb.sh`, `-tief.sh`, `-flach.sh`) + golden marks | **executed and compared** — they run through the real `fahre()`/`urteil()` path, marks and codes asserted in both directions, and a failed self-test returns `2` before a real guardian is read | `ABNAHME GRUEN: N von N messenden Waechtern` | no |
| `abschnitt.py` | no (shared library, not a guardian) | — | its own truncation mechanism is validated by **executing** `fahre()` in five scenarios incl. a crash (`:151`, `:246`) | none over Gabbro | no |
| `abschnitt.sh` | no (shared shell library) | — | n/a — its speech test is run inside `pruefe-waechter.py` (`sprechprobe_schale()`), both directions, every run | none of its own | no |
| `erzeuge-mutationen.py` | yes | name pattern `crates/gabbro-check/src/*.rs`; expected value: the validity floor `gueltig < 30`; a fixed PRNG seed | **executed and compared** — each drawn mutation is applied to the real source, gated by `cargo build`, then by `cargo test` (`:102`) | `== N von M gueltigen erzeugten Mutationen gefangen ==` | no — an undersized population reddens (`:168`) instead of reporting a hollow pass |
| `fuzze-erzeuger.py` | yes | baseline + template (shared, read out of `fuzze-grenzen.py` by `grenzen_laden()` `:129`) + own `EIGENE_FORMEN`/`EIGENE_GUT`; golden C snippets; expected value `GEBUCHT` (`:323`) | **`cc`** — `eine_probe()` drives every case `check` → `emit` → `cc` (`:431-448`, `:458`). Stage 4 not reached, and **said so per run**: `:830` prints the count of cases *"lowered, compiled, and only SHAPE-checked … no oracle exists for them"* | `== N of M accepted cases kept the emitter's promise ==` | no — one stage deeper than the table's owner, and the blind spot is printed, not assumed |
| `fuzze-grenzen.py` | yes | baseline + template: `GUT` (`:195`) paired with `FORMEN` (`:280`), incl. `walk-levels: "4"` and `walk-knoten: "512"`; name pattern `REGEL` (`:244`) for the `--deckung` claim | **`gabbro check` only.** The file's one subprocess is `[binaer, "check", …]` (`:771`); the pre-sweep speech test (`:946`) uses it alone. `emit`, `cc` and `D1` do not occur anywhere in the file — **zero mentions, grepped** | `== N of M answered the same in both builds, without a panic ==` | **YES** — the two `walk` baselines lower to C that does not compile (`D1`, `gift/641`). That is recorded, but only in the SIBLING (`fuzze-erzeuger.py:330-331`, `65 + 65 = 130` cases). This file neither reaches `cc` nor names the stage it stopped at. |
| `miss-c-signaturen.py` | yes | expected value: the type tables `GLEICH` and `GLEICH_POSIX`; the `_cc` harness itself | `GLEICH` → **`cc`** (a real `_Static_assert` per pair, `:413`); the harness → **`cc`** (`sprechprobe` at `:117-118`, both directions, gates everything); `GLEICH_POSIX` → **not validated** | *"The equivalences are measured, not assumed"* + `Aequivalenzen geprueft: len(GLEICH)-1` | **YES** — `GLEICH_POSIX` (`:82`) feeds the same `BINDBAR` verdict at `:217` as the asserted table, but `aequivalenzen_pruefen()` iterates `GLEICH` only. Validated at *nothing*; read at `cc`. |
| `miss-erschoepfung.py` | yes | name pattern: the closed list `ENUMS` (`:81`) selecting which of `ast.rs`'s enums get probed; known-good: the injected variant `PROBE = "ZzSondeVariante"` | **executed and compared** for what it measures — the probe is really inserted, `gabbro-syntax` really repaired against `rustc`'s suggestions, real `E0004` diagnostics counted from a real `cargo check`, and the source restored byte for byte with an assertion (`:236-251`). `ENUMS` itself is never cross-checked against the full enum list | `== the sites the compiler FORCES, per AST enum (%s probe) ==`, and it prints its own blind spot: `:287` `-- NOT measured: whether an unforced pass sees the form.` | no — the house form, and the most self-aware file of the set. *Noted only: `ENUMS` covers 5 of the 34 `pub enum`s in `ast.rs`, and that scope limit lives in the docstring, not in the printed verdict.* |
| `mutiere-pruefer.py` | yes | anchor: ~340 literal `crates/` source lines in `Mutation(alt, neu, …)`; golden output: the Isabelle/Lean text asserted in `tests/rechenwerk.rs` for the 39 `flaeche="annotation"` mutations | anchors → **very deep**: uniqueness checked before every run (`:4108-4161`), a dead or ambiguous anchor aborts the whole run (`:4510`), and scoring is a real rebuild + `cargo test`, which for many `code` mutations runs `.gab → emit → cc → execute → compare`. The 39 `annotation` mutations → **generated-TEXT comparison only**: `proben_laufen()` (`:4086`) runs `cargo build --tests` + `cargo test` and nothing else — **no prover is ever invoked from this file** | `== N von M gueltigen Mutationen gefangen (P%) ==`; the catalogue's own reason (`:69-73`) is that a generator emitting silently weakened contracts *"liefert einen gruenen Beweis ueber eine schwaechere Aussage"* | **YES** (narrow) — the property named is about a **proof** going green; the fixture is validated at the string the emitter writes. Isabelle and Lean are only ever run by `pruefe-p6-beweis.sh` / `pruefe-lean-beweis.sh`, which this file never calls. |
| `pruefe-abstieg.py` | yes | name pattern: `PAESSE` (`:54`), a hardcoded list of 15 module names deciding which files the guard opens at all | statement kinds are derived live from `lib.rs` and speech-tested; **`PAESSE` itself is not validated** against the real set of files touching `StmtArt::` | `== ABSTIEG: ALL PASS -- jeder Pass erreicht jeden Unterblock ==` | **YES** — 8 files with block-bearing `StmtArt::` are absent from the list and never examined: `alias.rs`, `pflichten.rs`, `opsruf.rs`, `blindstellen.rs`, `domaene.rs`, `lean.rs`, `zeremonie.rs`, `gatter.rs`. *"Every pass"* is a claim about 15 of 23. |
| `pruefe-aufloesung.py` | yes | expected value `RATSCHE = 3` (`:95`); anchor `IST_UMGEBUNG` (`:103`) | pure text; validated by a 5-direction speech test on fabricated Rust covering every tray. Empty population reddens (`:190`, `return 2`); the ratchet is recomputed each run, both directions | `== Fach 1 -- bloss uebergebener Name auf qualifizierter Karte: N ==` | no |
| `pruefe-beweise.sh` | yes | golden output: a synthetic 30 s sleeper and a 0.1 s process built into `sprechprobe()` (`:78`) to validate the watchdog | **executed** — real processes spawned, killed or allowed to finish | `BEWEISE: ALL PASS -- N Theorien (D Dateien)` | no — and it defends this very class by name: `isabelle build` exits 0 over an EMPTY session selection, so a `NACHWEIS` is required or the run says `BEWEISE: OHNE NACHWEIS` (`:162`, exit 2) |
| `pruefe-emission.sh` | yes | baseline programs (`beispiele/12,14,16,19,20,21,23,24,26,27,34,52`, `messung/fragmente/F0N.gab`); golden outputs; known-bad `sed` gift transforms; name pattern (`find … -name '*.gab'`); expected values `MARKE_EMIT=65`, `MARKE_EMIT_M=53`, `MARKE_UMGEKEHRT=10` | **executed and compared** for the `lauf`/`lauf_kern` cases (`:270-491`): emit, byte-identical re-emit, `cc -Werror -O0`, execute+compare, `-O2` cross-check, UBSan, ASan, `zeugnis` cross-check, and a negative control per fixture (`:459-490`, the `sed` mutant must change the answer or the run says `UEBERSEHEN`). Stage 9 (~120 files) is **`cc` only** (`:2065`) | `== EMISSION: ALL PASS -- N durchgestochen, n_ok von n_nenner uebersetzen, … ==` | no — and this is the reference form: the shallower stage is stated **in the headline output itself**, `"Die Regel darueber ist schwaecher: sie fragt nur, ob der C-Uebersetzer die Ausgabe annimmt."` |
| `pruefe-englisch.py` | yes | name pattern (`DEUTSCH`, `STELLEN`, `QUELLEN`, `NAMENSMARKER`) + expected value (`MARKE_KOMMENTARE=7892`, `MARKE_PY=1069`, `MARKE_NAMEN=273`) | pure text. `DEUTSCH`/`STELLEN` and both seam detectors: **executed and compared** on invented sources (`:356`, `:388`, `:398`). `quellsprache()` (`:634`) and `NAMENSMARKER` (`:628`): **not validated** | `RATSCHE GEBROCHEN: {rs_d} deutsche Kommentarzeilen, gebucht sind {MARKE_KOMMENTARE}` | **YES** — the function that decides three of the file's ratchets is the one function here with no invented fixture under it. |
| `pruefe-grammatiktafel.py` | yes | golden output `GIFT_C`/`GUT_C`/`GIFT_GRUND` (`:528-542`); name pattern: the `absage` word set scraped out of `emit.rs` by `absageworte()` (`:264`) | `GIFT_C`/`GUT_C` → **`cc`**, both directions (`:599-604`). The `absage` word set → **not validated**: text mention only, never confirmed against a refusal that actually fires | `== GRAMMATIKTAFEL GRUEN: 0 von N Terminalen UNGEDECKT ==` | **YES, but self-disclosed** — `:38-40` names it: *the `abgesagt` state rests on the read word set, which changes nothing today (0 words) and could change something tomorrow.* Dormant, declared, not silent. |
| `pruefe-gruende.py` | yes | expected value: the closed word lists `ABSENKUNG` (`:41`) and `ZUSAGE` (`:52`) | pure text; **reddens on empty extraction** (`:134`, `return 2`), and the lists are checked against four historically known instances plus a window-boundary probe | `N verdaechtig · M tragend · K unklar` | no |
| `pruefe-kennungen.py` | yes | anchor: the two exclusions `"/tests/"` and `saetze.rs` (`:34`); known-good: an injected duplicate `K001` | pure text; the speech test runs unconditionally on every call, both directions (`:83`), and an empty harvest aborts (`:96`, `return 2`) | `== KENNUNGEN: ALL PASS -- jede Kennung gehoert genau einer Datei ==` | no — both historical holes (unfiltered `saetze.rs`, empty-population ALL PASS) are closed |
| `pruefe-klauseln.py` | yes | expected value: the hand-written classification table `ERWARTET` (`:90-194`) and the `HOMONYME` exception booking (`:207`); name pattern `TRAGEND_DATEIEN` | pure text — but re-derived from the live tree every run and diffed **in both directions**: a newly unread field is `neu` (exit 1), a field a pass now reads is `weg`, "the table is stale" (exit 1). The `HOMONYME` booking bites too: `selbsttest()` fails if a booked file no longer contains the access it is excused for (`:323`) | `== KLAUSELN: N gebucht, keine neue ==` / `== KLAUSELN: DIE TABELLE IST VERALTET ==` | no |
| `pruefe-konstrukte.py` | yes | expected value: `OHNE_PROBE` (`:61`); name pattern: `proben()` over `beispiele/gift/*.gab` | `gabbro check`-level text scan, validated in both directions (an invented word → 0 hits, `module` → >0); the ratchet reddens BOTH ways (`:188` new gap, `:189` a fixed gap still listed) | `== KONSTRUKTE: N ohne Probe gebucht, keine neue ==` | no |
| `pruefe-lean-beweis.sh` | yes | golden output: hand-written Lean theorem templates, a true one and a poison one, in `speech_test()` (`:96`) | **executed** — really run through `lean`, required to succeed on the true statement and FAIL on the poison one, in both body shapes; zero generated theorems is a hard abort (`:172`, exit 2) | `LEAN PROOF: N generated obligation(s) in M modules, LEAN GREEN` | no |
| `pruefe-lean-programm.sh` | yes | baseline `beispiel/lager.gab` + `betrieb.gab`; known-good/poison `Spec.lean` / `SpecGift.lean`; `sed` anchors over its own generated `GabbroProgram.lean` | **executed and compared** — really compiled and run by `lean`, one spec that must pass and one that must fail | `LEAN PROGRAM: N bodies from 2 files, M hand-written specifications, LEAN GREEN` | no — an empty place dictionary would fail the GOOD spec too, and the closing gate catches it (`:165`) |
| `pruefe-luecken.py` | yes | anchor: thirteen literal `crates/gabbro-check/src/*.rs` source lines (`:37-84`), **plus two `NULLMUTATION` entries of the same kind, deliberately excluded from scoring** | the thirteen real anchors are checked by `_mp.ankerstand()` and the result is **wired into the exit code** (`:249`, `weg += 1`, and `:300` `if offen or weg: SystemExit(1)`). The two `NULLMUTATION` anchors take the `if not echt:` path (`:226-231`), which `continue`s **without calling `ankerstand()` and without touching `weg`** | `== LUECKEN: ALL PASS -- und alle Quellen byteidentisch zurueck ==` | **YES — and it is LIVE today, not hypothetical.** The second null anchor quotes `let ecken = [a.min * b.min, …]` from `multipliziere()`; that function was rewritten to a `checked_mul` loop on 2026-08-20 and **the literal is not in `typen.rs` any more — grepped, zero hits.** A dead null anchor replaces nothing, so the run behaves exactly as a live one would, and `ALL PASS` stands over a fixture that no longer exists. |
| `pruefe-notation.py` | yes | template: eight minimal `LUECKEN` skeletons; expected value: six poison templates with required rejection codes (`P037`, `M107`, …) | `gabbro check`, run live, gated by a sign-of-life check (`:117`, exit 2) | `== N von M geschlossen ==` / `== Gegenprobe: N von M Formen abgesagt, wie entschieden ==` | no — a code that stops firing is named `STILL DURCHGELASSEN` and reddens (`:157`) |
| `pruefe-p6-beweis.sh` | yes | known-good/poison: hand-written true and false Isabelle lemma templates for a two-way speech test (`:69`); name pattern `beispiele/*.gab` + `messung/*/*.gab` | **executed and compared** — real `isabelle build` over theories generated from the real corpus, both directions | `P6-BEWEIS: N erzeugte Pflicht(en) in M Theorien, ISABELLE GRUEN` | no — an empty or vanished corpus drives `ZIELE` to 0 and the explicit guard reddens (`:122`, exit 2) instead of reporting an empty-but-green build |
| `pruefe-reichweite.py` | yes | name pattern `PAESSE` (`:44`), twelve hardcoded pass filenames; expected value `RUEMPFE` | pure text, speech-tested in ONE direction only; `PAESSE` is never checked against the real files — `quelle()` returns `""` for a missing one, in silence (`:68`) | `== N ungelesen, M von genau einem Pass gelesen ==` | **YES** — there is no mark on `ungelesen`/`duenn` at all, so a `pruefe-` tool can never redden on its own worst finding, and a pass renamed out of the list is invisible |
| `pruefe-saetze.py` | yes | expected value `MARKE = 51`; golden output `GIFT_REGISTER` (`:180`) used only to self-test the parser; baseline: the built binary with a freshness check | **executed and compared** — the real claim comes from running `gabbro paesse --je-satz` and parsing live output, not from the golden string. Binary staleness aborts (`:228`) rather than mixing an old binary's claims with a new tree | `== Zahn 2: N von M Kennungen ohne Satz ==` | no — the ratchet is checked in BOTH directions, including the good one (`:275`, *"die Marke gehoert nachgezogen"*) |
| `pruefe-schablonen.py` | yes | golden output `GIFT`/`SAUBER` (`:115`); expected value `MARKE = 6` | the regex is self-tested, then **cross-checked live** against `gabbro schablonen`'s own reported count — `gemeldet != len(luft)` aborts (`:151`), so format drift is caught the run it happens | `== Zahn 3: N Praemissen bewiesener Schablonen ohne Pass ==` | no |
| `pruefe-sonden.sh` | yes | known-good: three synthetic probes returning 0 / 1 / 77, built and run by `probe_bauen()` (`:80`); name pattern `sonden/sonde_*.c` | **executed and compared** — the only instrument in the folder that reaches stage 4; `DA -eq 0` aborts (`:133`) | `N von M Sonden gelaufen, K Sondenname(n) im Manifest benannt` | no for the verdict. *(`BENANNT`/`GESTRICHEN` come from `grep -o` over `gabbro annahmen` text and gate nothing — a format drift misreports a number without flipping the colour.)* |
| `pruefe-syntax.sh` | yes | anchor/name pattern: `VERBOTEN`, `ALTDEUTSCH`, the fixed `DOKUMENTE` list | pure text for the keyword half, each branch speech-tested in **both** directions (`:95`); a real `cargo build --tests` for the warnings half, and a build that never completes ABORTS rather than reporting "0 warnings, clean" (`:134`) | `SYNTAX: ALL PASS` | no |
| `pruefe-todo.py` | yes | expected value: `PLAN_ABWEICHUNG_GEBUCHT` (`:68`), a booked snapshot of `dokumente/PLAN.md`'s P0–P8 headings compared by literal equality | pure text. Nearly everything else reaches **executed and compared** in `sprechprobe()` (`:585`) — DE+EN gift/clean templates, a derived README template, a three-way `DONE.md` count. `plan_etiketten()` (`:83`) is **not validated**: `sprechprobe` never calls it | `{len(PLAN_ABWEICHUNG_GEBUCHT)} gebuchte Abweichungen, keine neue.` / `== TODO: ALL PASS ==` | **YES** — one hand-written snapshot inside a file that otherwise invents its own fixtures for every check. |
| `pruefe-uebersetzerfamilie.py` | yes | name pattern `quellen()` (`:125`); expected values `MARKE_FAMILIENUNTERSCHIED = 0`, `MARKE_BEIDE_ROT = 0`; anchor `-- erwartet: cc` | the ratchets are recomputed live each run; the population glob has **no emptiness guard** in `main()` | `== Die Ratsche: N Unterschiede, gebucht sind 0 ==` | **YES** — with zero `.gab` found, `0 == 0` and the run exits green reading exactly like a real full-corpus pass. *(Not repaired here — another lane owns this file.)* |
| `pruefe-umwandlungen.py` | yes | template: a fabricated crate `SPRECHPROBE_CRATE` with one truncating cast; expected value `MARKE = 33` | **compiles** — `sprechprobe()` runs real `cargo clippy` over the fabricated crate, plain and `#[allow]`-annotated, before any real number is trusted (`:172`); missing clippy aborts with `2` (`:211`) | `== Truncating casts in crates/*/src/: N sites + M suppressed = K ==` | no |
| `pruefe-vergabe.py` | yes | expected values `MARKE=20`, `MARKE_PROBEN=64`, similarity cutoff `SCHWELLE=0.45`; name pattern: the `VERGABE` regex deciding what counts as an issuance site (`:60`) | pure text. A total collapse of `VERGABE` is caught indirectly: `sprechprobe()` reconstructs the real 2026-08-21 `M120` double issuance through the *same* `erhebe()` path, so a dead regex fails the self-test closed (`:296`, `return 2`). No independent population floor | `Davon melden N UNAEHNLICH … Marke 20: sie darf fallen, nicht steigen.` | no — and its largest blind spot (codes issued outside a literal `Absage::` constructor) is measured and PRINTED as `unsichtbar` (`:337`), not hidden |
| `pruefe-waechter.py` | yes | name pattern: the glob in `waechter()` (`:583`) + `TRAEGT_URTEIL` (`:521`); expected value: the hand-typed figures in `GEGENSTAND` (`:202-238`) | glob → **executed and compared**: the hole is closed not by widening the glob (refused at `:609`) but by a parallel sweep `ausserhalb_der_besetzung()` (`:622`) that reddens on an unbooked violation outside it (`:1426`), itself speech-tested against fabricated files (`:630-658`). `GEGENSTAND` figures → **not validated** | `== Ausserhalb der Besetzung: N von M Werkzeugen in instrumente/ ==` | no for the known hole — **CLOSED**. (Aside: several `GEGENSTAND` rows are hand-typed and no code re-derives them; `abnahme.py` prints them unchecked.) |
| `pruefe-widerruf.py` | yes | golden output: a literal pattern per revoked sentence; known-bad: a bilingual specimen sentence per entry (`WIDERRUFE[*]["probe"]`); name pattern `DATEIEN` with a hand-listed `AUSGENOMMEN` | pure text, and the structural hole is guarded: a mandatory **two-language** speech test re-derives every pattern's own specimen and requires it to still fire; a silent pattern **aborts the run** (`:406`, `return 2`) rather than printing ALL PASS | `== WIDERRUF: ALL PASS -- kein widerrufener Satz steht lebend da ==` | no — a tool whose green *is* the empty result, with the empty result made impossible to reach silently |
| `pruefe-wortschatz.py` | yes | anchor: the literal row label `Struktur`/`Structure` (`:39`); name pattern: the EBNF terminal regex | pure text, and it is the strongest defence in the folder: an empty read aborts with `2` (`:132`), `--probe` injects a fake terminal and demands it be caught, and a *Gegenrichtung* run re-reads the file with every German label translated to English demanding the SAME two numbers (`:204`) | `Wortschatz: N EBNF-Terminale, M Tabellenwoerter` | no — anchor staleness under the German→English move is pre-empted by design |
| `pruefe-zahlen.py` | yes | name pattern: `BEWACHTE_DATEIEN` (`:923`) — a fixed FIVE-file list, not even a glob; the format it polices is `KENNZAHL` (`:931`), a bold number in a table cell | the cell machinery (`zellen()`, `ort_von()`, quote exclusion) is **executed and compared** (`:1238-1256`). The five-file list itself is **not validated**: nothing checks it is the full set of documents carrying that format | `== Reichweite: was dieses Register NICHT bewacht ==` — presented as the accounting of unguarded figures | **YES** — measured: `dokumente/PLAN-HARDWARE.md` 22 cells, `messung/GEGENRECHNUNG.md` 19, `DONE.md` 19, `dokumente/BEWEIS.md` 18, and ~40 more files carry the identical fixture format and are invisible to the register that claims to account for reach. |
| `pruefe-zitate.py` | yes | anchor: literal comment lines lifted from `mutiere-pruefer.py`'s `MUTATIONEN[i].alt`; expected value `MARKE = 342` | pure text. A stale anchor is inert and therefore *over*-counts — the safe direction for an upper-bound ratchet. But `ankerprobe()` computes the disjointness and **only prints it**: its `return True` is unconditional (`:416-419`) | `:135` *"the disjointness is now CHECKED rather than assumed, and it will speak up on the day it stops holding"* | **YES** — the disjointness is validated by a `print`. `MARKE` fires only on `>`, so an anchor that begins swallowing a real citation lowers the count and the run stays green. |
| `vergleiche-binaerprogramme.py` | yes | known-good: a differential probe — the same binary run as `check` and as `emit` must disagree; name pattern `rglob("*.gab")` | **executed** — the fixture is checked by really running both subcommands on the binaries under test | `== NICHTS BEWEGT ==` / `== BEWEGT: N ==` | no — the prior `/bin/true` vs `/bin/true` false-green is repaired: a binary that cannot be shown to answer its argument, an empty corpus, or two identical binaries all abort with `2` (`:108-142`) |
| `zaehle-absagen.py` | yes | golden output: the `KOPF` diagnostic-line regex (`:63`); baseline binary with an mtime staleness check; a synthetic poison source | `formen()` is speech-tested; `korpuslauf()` reaches **`gabbro emit`**. `KOPF` is **never exercised by the speech test** — only run live against real stderr, and a non-matching line is silently skipped (`:432-441`) | `== N Absagestellen, M verschiedene FORMEN ==`; `--korpus`: `== K FORMEN gemessen UNGEDECKT ==` | **YES** (latent) — checked against `crates/gabbro-syntax/src/diag.rs:92-98`, it matches today. A wording drift in `zeige()` collapses `codes` to empty for every file and `--korpus` reports `0 UNGEDECKT`, green, with no abort. |
| `zaehle-b3.py` | yes | name pattern: the whole regex vocabulary that classifies chain-walk / pointer-surgery / domain-iteration sites (`LINKFELDER` `:279`, `LINK` `:621`, `DOM_LINK_ABSTIEG` `:627`) | pure text over a foreign tree. **Not validated** — no speech test, no labelled example, no invented snippet anywhere in the file. Its only self-check is structural (unbalanced brackets → `ABGEBROCHEN`, `:840`), which is a check on PARSING, not on the vocabulary | `BERICHTET (+Nb2): N Ruempfe M Z P %`, downgraded to *"eine untere Schranke, keine Messung"* only on a bracket abort | **YES** — a hand-picked field-name vocabulary decides the reported percentage and nothing checks it catches a real chain-walk; an unlisted field name undercounts in silence. *(Also noted: three `def lauf` at `:353`, `:559`, `:709` — the first two are dead, superseded twice with no probe marking either switch.)* |
| `zaehle-bereichspflichten.py` | yes | baseline document `dokumente/FRAGMENTE.md`; anchor: the codes `M101`/`M104` and the sign-of-life string `Translation units` | an `emit`-like `gabbro fragmente` run. The sign-of-life guard reddens for a dead binary (`:65`) but **not** for a stale code anchor | `== N = M Fundstellen ==` | **YES, and it is the bluntest** — when the anchor stops firing (`sauber == ganz`) the tool PRINTS *"Dann misst dieser Lauf nichts (Vorab-Protokoll: ungueltig)"* and then **falls through to `return 0`** (`:154-166`). The finding is printed; the exit code is green. |
| `zaehle-bloecke.py` | yes | anchor: bilingual heading literals `KOPF` (`:53`), `STUFE`/`STAGE`, `⟨X⟩` marks | pure text; missing subject reddens (`return 2`); `sprechprobe()` runs every check twice, on invented German and invented English text, demanding identical results (`:143`) | `== BLOECKE: ALL PASS -- jede Ueberschrift traegt ihr Ziel ==` | no |
| `zaehle-c-formen.py` | yes | known-good/expected value: `KATALOG` (`:423-554`), a hand transcription of `dokumente/BEWEIS.md` §1's allow/never lists with quoted `quelle` strings; ratchets `MARKE_TABELLE=67`, `MARKE_UNERLAUBT=32` | the corpus half is **`gabbro emit`** per file (`korpus()` `:964`) and `cc` under `--uebersetzer`, with an honest `UNGEMESSEN` when the flag is absent (`:1263`). `KATALOG` → **not validated**: the file never opens `dokumente/BEWEIS.md` — grepped, only prose mentions | `== Die drei Mengen (Katalog: N Formen aus BEWEIS.md §1)` | **YES** — the headline asserts the catalogue *comes from* a document the tool never reads. Compared by hand today: they agree. Nothing turns red the day `BEWEIS.md` is edited alone. |
| `zaehle-empfindlichkeit.py` | yes (inherited) | none of its own — it reuses `pruefe-grammatiktafel.py`'s constants and functions by `importlib` (a deliberate W7 choice, one copy) | **`cc`** — requires `shutil.which("cc")` and treats a file that emits and then fails the compiler as uncovered | `== EMPFINDLICHKEIT GRUEN: N Woerter an je EINER Datei, Marke M ==` | no — every prerequisite (documents, check directory, `cc`, non-empty corpus) reddens with `return 2` before a number is trusted (`:84`, `:101`) |
| `zaehle-fallen.sh` | yes | baseline table `fallen-klassifikation.tsv` with an expected row count of 100 | pure text, but checked against the REAL data, not a stand-in: a row-count drift exits `1` (`:14`), and the class alphabet is read off the real column | `Sprechprobe: alle Klassen sind S/M/W/B.` | no |
| `zaehle-formate.py` | yes | anchor `^format NAME @version N`; name pattern `beispiele/**/*.gab` + `messung*/**/*.gab` | pure text; **reddens on empty population** (`:168`, `return 2`) and on a missing reference file; the regex is speech-tested in both directions | `== ROT: N Formate mit einer zweiten Fassung ==` | no |
| `zaehle-fragmente.py` | yes | baseline corpus `messung/fragmente/F*.gab` with a hardcoded size of 10; a synthetic broken probe | `check` and `emit` directly; the `AUSGEFUEHRT` figure now delegates to `zaehle-pflichten.absenkung()`, a real per-fragment run (**stage 4**) | `N von M sind DURCHGESTOCHEN` | no — the file documents its own retired source-line anchor and its repair (`:136`) |
| `zaehle-fremdpflichten.py` | yes | template: four hand-written `.gab` skeletons, one per claimed state (`:195-237`); anchor: literal parse patterns into the CLI's printed text (`:56-90`) | **executed and compared** — the templates are really run through `cargo run -p gabbro-cli -- zeugnis` and the classification asserted equal to the state each was built for (`:240-287`). The literal anchors get a second, independent register: every real run cross-checks the self-classified count against the binary's own `BEFUND` line and aborts on divergence (`:344`) | `== Die vier Zustaende einer fremden Pflicht ==` | no |
| `zaehle-fremdverengung.py` | yes | template: a `.gab` skeleton with `{lo}` swapped between 0 and 1 (`:128`) | **live against the real translator** — both variants are written and run through `cargo run -p gabbro-cli -- zeugnis` on every invocation, so certificate wording drift fails rather than passes; empty corpus aborts (`:77`) | `== N wirksame Fremdverengungen aus M ausgesprochenen Vertraegen, … ==` | no |
| `zaehle-gifttreffer.py` | yes | baseline: the built binary; anchor: the `KOPF` regex into `Absagen::zeige`'s format (`:68`); expected values `MARKE_SAUBER=271`, `MARKE_VERDECKT=7`, `MARKE_PROBEN=333`; name pattern `beispiele/gift/*.gab` | **`gabbro check` / `emit`** — each poison file is really run and its diagnostics parsed. The `-- erwartet: cc` half is explicitly NOT checked here and handed to `tests/beispiele.rs` (`:115-119`), so the tool does not overclaim depth | `== GIFTTREFFER: ALL PASS -- N von M treffen ALLEIN ==` | no — an anchor drift degenerates every probe to `treffer=[]`, which classifies as `FEHLT` and is loudly reported (`:279`), returning 1 |
| `zaehle-karten.py` | yes | anchor: the regex mirroring the literal `HashMap<` field syntax of `umgebung.rs` (`:90`); expected values `MARKE_DIREKT=40`, `MARKE_UNQUALIFIZIERT=36` | pure text. The speech test checks the regex **only against an invented line** (`:117`); there is no floor on the real match count | `== KARTEN: N direkte Blicke, M unqualifiziert -- keine neue ==` | **YES** — a format change in `umgebung.rs` collapses `stellen` to empty, `0 <= MARKE`, and the tool reports a record-best green |
| `zaehle-lean.py` | yes | name pattern: `beispiele/*.gab` + `messung/*/*.gab` (`:177`); expected value: the closed `GRUENDE`/`ARTEN` tables | the tables are **live**: an unknown refusal reason aborts with `2`. The glob is **not guarded**: there is no `if not dateien` anywhere in the file | `== BODY CHANNEL: N obligations, M goals, K refused ==`, `return 0` | **YES** — with zero matching files the tool prints `0 obligations, 0 goals, 0 refused` and exits green, indistinguishable from a real all-clear. Its own sibling over the same corpus, `pruefe-lean-beweis.sh`, guards exactly this (`GOALS -eq 0` → exit 2). |
| `zaehle-narrow.py` | yes | known-good: `SPRECHPROBEN` (`:30`), three literal `(file, marker)` pairs in a foreign tree the classifier must locate | pure heuristic over a foreign Rust tree. The self-check verifies only that the three markers are FOUND, never that the classification is right — which is exactly the scope of the claim | the K/V1/V2/V3/F/N distribution, printed with its own disclaimer `:4-8` *"KEIN MESSGERAET … liegt in 3 von 5 handgeprueften N-Stellen falsch"* | no — the check matches the narrowly scoped claim |
| `zaehle-netz.py` | yes | known-good: published RFC 791 / RFC 1071 vectors (`:57`) + a second, independently written checksum `rfc1071()` (`:49`) as oracle | **executed and compared** — `emit` → `cc -Werror` → run the binary → compare against the independent computation; a speech test first proves the oracle reproduces the published vector AND that one altered byte changes the answer (`:129`, `:137`) | `== N von N Proben gruen ==` | no |
| `zaehle-p6.py` | yes | name pattern `beispiele/*.gab` + `messung/*/*.gab` (`:101`); anchor: the `REASONS` list mirroring `refinement.rs` | the `REASONS` anchor reddens on an unrecognised reason (`return 1`). The glob has **no emptiness guard** | `== P6: N Pflichten, M Ziele, K abgesagt (… D Dateien angesehen) ==` | **YES** — with `files == []` both balance checks are vacuously satisfied and the run reaches `return 0`, printing `0 Dateien angesehen` as a clean pass |
| `zaehle-pflichten.py` | yes | name pattern: the `# «F0»` marker and a hardcoded block count of 10; golden outputs read out of `pruefe-emission.sh`'s real run | **executed and compared** — `_messe_absenkung()` really runs `pruefe-emission.sh --absenkung` and cross-checks every `lauf "fragmentN"` line against a returned verdict, aborting on any gap (`:285-297`); missing markers abort loudly (`:150`) | the `H` total, explicitly disclaimed as not a claim about Gabbro overall | no — the file names its own prior defect (reading the source line instead of the run) and now validates at the deepest stage |
| `zaehle-probenzweige.py` | yes | template: seven invented instruments; expected value `MARKE=14`, `MARKE_ZEILEN=195`; name pattern `PROBENNAME` (`:93`) | **executed and compared** — each invented instrument runs under the real `sys.settrace` tracer in a real subprocess and its JSON is asserted across 8 directions (`:557-566`) | `PROBENZWEIGE: N Instrumente / M Zeilen -- auf der Marke`; both ratchet directions fall (`:712-723`) | no — the tool that measures this very class turns the lens on itself |
| `zaehle-theorien.py` | yes | expected values `MARKE_EINGEFROREN=31`, `MARKE_OHNE_REGISTER=2`; name pattern `beweise/*.thy` + the fixed `REGISTER` path; known-good/bad theory snippets | pure text over `.thy` and `schablonen.rs`. Both populations are guarded: an empty `beweise/` aborts (`:209`, *"es wurde NICHTS gemessen"*, exit 2), a missing register aborts the register half specifically (`:254`, return 1) | `== N Theorien, M Zeilen, K Saetze, L Beweisschritte ==` | no — and the coarsening is disclosed: `ohne_register()` calls its own figure a LOWER bound |
| `zaehle-traversierungen.py` | yes | name pattern: two corpus globs, `LEHRKORPUS` and `ECHTKORPUS` (`:70-74`); known-good/bad: five hand-written `.gab` snippets in `sprechprobe()` | pure regex over `.gab` text. **Asymmetric**: `LEHRKORPUS` emptiness aborts with `2` (`:361`, *"es wird NICHT null gemessen"*); `ECHTKORPUS` emptiness has **no such guard** before `:368` | `== Die Zahl, die Entscheidung 10 vor dem Bau braucht ==` — a claim about duplication in real code *and* the teaching corpus | **YES** — if `messung/treiber`, `messung/caprock` or `messung/netz` were renamed or emptied, the report prints `0 Traversierungsruempfe … 0 dupliziert` for real code and is read as *no duplication found*, not as *no real code was measured*. The guard the tool already wrote for the other corpus is simply not on this one. |
| `zaehle-verdrahtung.py` | yes | golden output: `pruefe-klauseln.py`'s stdout parsed by literal patterns (`:212`); name pattern `TRAGEND`; known-good: `EICHUNG`, six hand-found real bugs | V1/V2/V5 speech-tested in both directions. V4's golden-string dependency is only partly guarded (`:385`, `getragen is None` alone) — a partial wording drift raises `TypeError` rather than aborting cleanly | `== VERDRAHTUNGSZAHL: N ==`, disclaimed as *"eine SUMME VON FORMEN, keine Anzahl von Fehlern"* | no — the one gap fails LOUD, not green, and `EICHUNG` prints the 3 of 6 known bugs it misses, by name |
| `zaehle-wortschatz.py` | yes | expected values `MARKE_WOERTER=221`, `MARKE_OHNE_GRUND=208` (speech-tested); plus `ABSENKUNGSSAETZE = 1` and `ABSENKUNG_ADRESSE` (`:104-116`) — a hardcoded assertion about an external Isabelle theorem's pass/fail state | the ratchets: pure text, speech-tested. `ABSENKUNG_ADRESSE`: **not validated at all** — no `isabelle build`, no existence check on the `.thy`, no check the theorem still fails | `== Die Beweisschuld: N Absenkungssatz auf M Woerter ==`, with the address printed as a standing fact | **YES** — a claim about a proof, carried as a Python string constant. Fixed, renamed or moved, and the line goes silently wrong. |
| `zaehle-zeremonie.py` | yes | known-good: a deliberately over-triggering `.gab` probe `PROBE` (`:62`) fed through the real binary; the rule table read live from `gabbro zeremonie --tafel` | **executed** against the built binary (`:168`) | `STUMM: … -- eine Regel ohne Treffer misst nichts`, red when any rule is silent | no — a rule nothing triggers is named and reddens rather than vanishing into a green zero |

## The one that is dead TODAY

Every other row above is a risk. This one is a present-tense fact.

`instrumente/pruefe-luecken.py:57-59` carries a `NULLMUTATION` anchor quoting a literal line
out of `crates/gabbro-check/src/typen.rs`:

```
    let ecken = [a.min * b.min, a.min * b.max, a.max * b.min, a.max * b.max];
    let min = ecken.iter().copied().min().unwrap_or(0);
```

`multipliziere()` was rewritten to a `checked_mul` loop on 2026-08-20 — the comment
recording that decision is still in the function. **The quoted line is not in `typen.rs`
any more; grepped, zero hits.**

The thirteen real anchors in the same list are checked for exactly this:

```python
if (warum := _mp.ankerstand(t, alt)) is not None:
    weg += 1
```

and `weg` is in the exit gate (`if offen or weg: raise SystemExit(1)`). The two
`NULLMUTATION` entries take the branch above it, `if not echt:`, which `continue`s **without
ever calling `ankerstand()`**.

***And here is why it could sit there:*** a null mutation whose anchor is dead replaces
nothing, so the build stays green, so the entry reports the same thing a live null mutation
reports. **The fixture answers identically whether it is alive or dead** — which is the whole
class in one sentence, and the reason none of this is visible from a return code.

## Method, so the numbers can be re-derived

The population is the 63 files of `instrumente/` (the same denominator
`pruefe-waechter.py` prints: `6 von 63 Werkzeugen` outside its own cast). Each file was read
in full or near-full and answered for five things: does it carry a fixture, of what kind, at
which stage that fixture is checked, what the tool's own printed verdict asserts, and whether
the second is shallower than the fourth needs.

The stage ceiling was measured mechanically rather than assumed: call sites for
`gabbro check`/`emit`, for `cc`/`clang`, and for executing a produced program, over all 63
files. **39 touch no build stage; 24 reach `check` or `emit`; 14 reach `cc`; exactly one —
`pruefe-sonden.sh` — runs a produced program and compares.** For the 39 pure-text tools the
ladder does not apply and the equivalent question was asked instead: *does a stale anchor or
an empty population redden, or does it go silently green?*
