# PRUEFER — the Gabbro checker

*Consolidated 2026-10-17 from `PLAN.md`, the retired `PFLICHTEN`, `SONDENDECKUNG` and `UNFALSIFIZIERBAR` registers,
several older checker documents and about twenty `messung/` reports. Claims were checked against the
tree on that day (source, `gabbro paesse`, the corpus, the guardians) except where the text says
"not re-measured" or "booked". Dated diary entries and lane numbers are not kept — git has them.
Rule and diagnostic codes, `OFFEN Oxx` ids and example/gift numbers are stable and stay.*

**What this document is:** the reference for `crates/gabbro-check` (the Rust checker, the passes
and their rules), for the places where its verdict is mirrored in Lean, and for the apparatus that
measures it. **What it is not:** the language (`SPRACHE.md`, `SYNTAX.md`), the goal theorem
(`BEWEIS.md`), the backends (`LLVM-BACKEND.md`, `C-SPEICHERMODELL.md`).

---

## 0. Status and what may be said

* **The checker is built and running.** `gabbro pruefe` runs 31 pass functions plus the `H022` cycle check in a fixed
  order (§4.1) over a source tree; the register of passes has twelve numbered passes, of which three
  are fully built and nine are *carried* — what each can say it says, and the rest stands beside it
  with a named address (§4.1, §8). Nothing is "open" in the sense of "silently unchecked".
* **A green run is the absence of the findings the built passes can see — not a proof.** The
  sentences the passes owe are written down (216 of them, §8); **none is proved** in the sense of
  a Lean theorem about the Rust rule. 208 are *measured* (a poison probe falls, or a mutation is
  caught), 2 are *argued*, 6 *conjectured*.
* **The Lean side proves something else:** the goal theorem `gabbro_ziel` is stated over a Lean
  Bool `Akzeptiert` (§12), not over the Rust checker. The seam between the two is witnessed per
  routine, not proved (§12.4). "Gabbro is verified" may **not** be said; "the goal theorem is
  proved over the model, with witnesses" may (`AGENTS.md` §1).
* **The design thesis in one paragraph** (the part of the old `PLAN.md` that is still the point):
  a Gabbro user proves *only their own logic*. Everything that mentions only the machine — index,
  overflow, alias, frame, lock, race, termination bound, contract at a call — must fall by
  construction in a pass; what mentions the subject (`ensures`, an invariant, a `requires` that
  the caller cannot show) is the person's. The metric that used to be written as a ratio
  (hand-written proof : specification, "0,5 : 1") is a diagnostic, not a gate: every hand-proved
  item above the floor is a *nameable* thing the checker does not yet carry (§9). The ceiling of
  what a language can take away was measured on 100 recorded traps: 72 % (language 36 %,
  measurement discipline 36 %), the other 28 % (tooling, wrong meaning) no language removes —
  the classification is `messung/fallen-klassifikation.tsv`, derived by the retired `zaehle-fallen` (2026-10-17, see git history);
  `BEWEIS.md` carries the argument.

Counts that move (examples, gifts, codes, sentences) are given with the command that re-measures
them (§13). Figures marked *booked* are historical results of the retired counters and the retired
`KENNZAHLEN` register (2026-10-17, see git history); they are not guarded today.

---

## 1. Architecture

| Crate | Role |
|---|---|
| `crates/gabbro-syntax` | lexer (`lex.rs`: `L001`–`L004`, `P060`–`P063` source-trust rules), parser (`parse.rs`, hand-written, no generator, `P0xx`), the AST (`ast.rs`), the diagnostics type (`diag.rs`: `Absage`, `Absagen`, `Stufe`, `Fix`), the keyword table (`kw.rs`) |
| `crates/gabbro-check` | the passes (`lib.rs::pruefe`), the pass register (`saetze.rs`), the shared maps (`umgebung.rs`, `aufrufgraph.rs`), the exporters and certificates (`lean.rs`, `lean_g.rs`, `corrlean.rs`, `certstmt.rs`, `zeugnis.rs`), the C emitter (`emit.rs`, deprecated) and the LLVM emitter (`llvm.rs`, current) — emitters run **after** the checker and are untrusted |
| `crates/gabbro-cli` | the `gabbro` binary (`main.rs`), the build system (`bau.rs`, `BAUSYSTEM.md`), the generated drivers (`treiber.rs`) |

The checker is about 136,000 lines in `crates/gabbro-check/src/*.rs`; the large files are
`emit.rs` (19.6k), `m1.rs` (11.0k), `llvm.rs` (9.3k), `namen.rs` (7.4k), `saetze.rs` (7.0k).
Each pass is a module with a `pass(baum, absagen)` entry; passes read the tree and the shared
maps and do not consume each other's refusals — a rule is one pass or a named part of one (the register is
the specification: `SPRACHE.md` part III §6, `lib.rs` head).

**Shared maps.** `Umgebung::sammle(baum)` builds the name maps (keyed *qualified*: `a::b::f`; a
bare-name lookup inside a `module` block returns `None` every time and looks like a rule that
does not fire — the retired `pruefe-aufloesung` guarded the class; not guarded today), `aufrufgraph.rs` builds the call hull
(a **lower** bound where an edge is unknown; checks that only demand more from the caller are
sound over an incomplete hull, checks that need completeness refuse or say "undecidable" — `E009`, `V003`, `W003`,
`H021`), `ableitung.rs` is the fixpoint over *bodies* as against the hull over *declarations*.
*Not built:* sharing one `Umgebung`/call graph across passes («Z0» of the old plan): every pass
still takes only `(baum, absagen)` and rebuilds what it needs. The old measurement (2026-08-19,
synthetic 120k-line unit, 899 ms, 610 ms of it the rebuild of those two structures) is not
re-measured; `GABBRO_ZEIT=1` prints per-pass times. A per-unit result cache («Z1») is not built;
the build system is incremental by content (`BAUSYSTEM.md`).

---

## 2. Running it

```bash
gabbro pruefe|check [--with L.gabi]… [--unit] [--passes] [--fix] <file.gab>…
gabbro paesse|passes [--je-satz]       # pass list + the register of sentences
gabbro pflichten|obligations [--isabelle|--lean|--g] <file.gab>…   # what a human still owes (§9)
gabbro abgeleitet|derived  <file.gab>… # the derived effects/costs per routine (§10)
gabbro fmt --explicit|--elide <file.gab>…
gabbro zeremonie|ceremony [--per-site|--table] <file.gab>…
gabbro blindstellen|blindspots <clean>… -- <poison>…   # FORM × POSITION, empty cells (§11)
gabbro kontexte|contexts, alias, k-bedingung, costs|kosten, annahmen|assumptions,
gabbro schablonen|templates [--gate], zeugnis|certificate, abi, link|verbinde
gabbro lean | lean-g | gegenbeispiel|counterexample | prove|beweise | gabbrov pruefe
```

* `pruefe` prints one line per finding (`error:`/`hint:`, the code in brackets, `file:line:col`,
  the site, then `= rule` notes) and a summary: *items, errors, hints*, and **M1's coverage line**
  (`M1 saw N expressions, 0 of them without a type (100 % coverage)` — "nothing found" and
  "nothing looked at" are different, and the line says which).
* The *"Not checked in this run"* block lists the carried passes. **It is a property of the
  binary, not of the file**: it prints a count per state and a fingerprint of the register;
  `--passes` or `gabbro paesse` print it in full. Printing 1,100 words of caveat beside 20 words
  of finding on every run is a disclosure nobody reads.
* `--unit` checks the named files as **one** unit (what checks as a unit is translated as one).
  Without it every file is its own unit; `--fix` and `--unit` are not combined (a fix span names
  bytes of one file). `gabbro lean` glues several files into one program text (see §11, "unit
  view").
* **Hints are not refusals.** The call sites that issue a hint (`Absage::hinweis`) are `D023`,
  `E003`, `E009`, `E249`, `H004`, `H008`, `M114`, `N026`, `N297`, `R015`, `S007`, `V003`. Every
  sentence in the register is weaker by exactly the functions on which a hint says "undecidable".
* **`--fix`** applies the machine-applicable repairs a refusal carries (`fix: …` lines; the
  `Fix` is `Some` only where the edit is unique — the missing entry the hull names, the bound
  below the computed one, the expected token — never a fix that weakens a contract, deletes a
  check or silences a refusal) and re-checks.
* `gabbro pruefe` writes findings to **stdout**, `gabbro emit` to stderr (as measured 2026-08-31). A
  measuring script that reads only stderr books every refusal as "0 errors" — this was paid for twice; the corpus
  tools read both streams.

---

## 3. Diagnostics

### 3.1 Code families

A code is a letter family plus three digits. The family tells the pass; the register (§8) says
what each rule promises. Counts are distinct code-shaped literals in the three crates (about 500;
443 of them are claimed by a register sentence — the rest are parser/lexer shapes, emitter and
exporter refusals, certificate refusals).

| Family | Owner | Meaning |
|---|---|---|
| `L001`–`L004`, `P0xx` | lexer, parser | token, grammar, `pub` placement (`P041`), library fn shape (`P043`/`P044`), source-trust (`P060`–`P063`: bidi controls, charset, mixed scripts, invisible characters) |
| `N` (about 200) | names, declarations, boundaries, arenas, strings, concurrency footprints | the large family; see §4.2, §4.13–§4.15, §6 |
| `D` | D1/D2, `ops` tables, quantifier domains, `owner` | §4.3 |
| `M` | M1: ranges, shapes, reasons, function pointers, bit intrinsics | §4.4 |
| `F` | floating point (`F001`–`F006`) | §4.4 |
| `R` | M3: pointer rights, address spaces, device registers, alias | §4.5, §5 |
| `L101`–`L109` | M2: linearity | §4.6 |
| `O` | phases, boot theorem | §4.6 |
| `S` | loops, progress, `-> never` | §4.7 |
| `V` | publish/await pairing | §4.8 |
| `E` | effects | §4.9 |
| `H` | locks, RCU, contexts, derivation edges | §4.10 |
| `U` | groups | §4.11 |
| `K` | costs; `K19x` compile-time constants | §4.12, §4.4 |
| `W` | declared concurrency | §4.10 |
| `A`, `G` | assumptions/`asm`, build gate | §4.2, §7 |
| `C` (`C001`, `C18x`), `T001` | C emitter and its refusals (deprecated backend) | §4.13 |
| `Y101`–`Y106` | LLVM emitter refusals (current backend) | `LLVM-BACKEND.md` |
| `LG001`–`LG007` | the G exporter (`lean_g.rs`) | §12.3 |
| `CS001`–`CS005` | statement certificates (`certstmt.rs`) | §12 |

`L` is used twice (lexer `L001`–`L004`, linearity `L101`–`L109`); the `1xx` block keeps them apart.

### 3.2 Rules for issuing a code

1. **One code, one rule, one file.** A code may appear on many lines but in one file
   (held by stage 3 of `instrumente/pruefe-pruefer.py`, `teile/kennungen.py`), and a code names one rule (retired `pruefe-vergabe`; `M120` was once issued
   for two rules in one file and the first guardian was blind to it; the register also lists `M139`
   under two sentences, `m1.bereich` and `m1.gestalt`). *Measured on 2026-10-17 by that stage (booked with its reason there):* 3 multiply-issued codes — `N004`/`N005` (`namen.rs` and
   `zielbindung.rs`, the same rule "names no declared assumption", re-applied to every `target`
   binding) and `Y103` (`llvm.rs`, `llvm/memory.rs`). The first pair is deliberate re-use of one
   rule, which that guardian counted as a violation (see §15).
2. **Every new refusal ships its sentence** in `saetze.rs` in the same commit (`gabbro paesse` lists
   the sentences; stage 2 of `instrumente/pruefe-pruefer.py`, `teile/saetze.py`, holds the ratchet "codes without a sentence") **and a poison probe** — a program in `beispiele/gift/`
   whose first line is `// erwartet: CODE`. A code with a sentence and no probe is a promise
   nothing measures.
3. **A refusal is never turned into a warning, and never widened to fit a corpus file.** A check
   that fires on a legitimate program is repaired by making the program's intent expressible, not
   by weakening the rule (`dokumente/PRUEFER.md` §2, now §10).
4. **A refusal that names a rule must say why** (measured by the retired `pruefe-gruende`: a rule built for the
   obvious reason does not cover the load-bearing one — `N011` caught ghosts in memory because
   they have no size, not because they cannot be stored). Diagnostic text is English.
5. **A note that claims a check its rule does not perform is a defect** (measured by the retired `pruefe-zitate`;
   `R003` once *said* "`class w` on a register means the same" and no line did it, so
   `return d.NUR_W.A;` passed — fixed by `R005`/`R006`).

**Next free codes** (`AGENTS.md` §7): `N587`. The gift and example counters in that table are
behind the tree: `beispiele/gift/1444-…` and `beispiele/1161`–`1163` already exist, so the next
free numbers are gift 1445 and example 1164 (measured 2026-10-17, see §15).

---

## 4. The passes

### 4.1 Run order, and the register's order

`lib.rs::pruefe` runs, in this order (verified from the source): names (`namen`) → binding surface
(`bindung`, `N038`/`N039`) → build gate (`gatter`, `G001`–`G003`) → K condition (`kbedingung`,
`D001`–`D013`) → `syscall` declarations → frame length (`rahmenlaenge`) → entry code
(`eintrittscode`) → NUL paths (`nulpfad`) → clone handoff (`clone`) → arenas (`arena`) → constants
(`konstanten`) → **M1** → strings (`zeichenfolge`) → loops (`schleifen`) → effects (`wirkungen`)
→ locks (`geteilt`) → lock invariants (`sperrinv`) → release refusal (`freigabe_pruef`) →
footprints (`fusswache2`) → contexts (`kontexte`) → declared concurrency (`nebeneinander`) →
arena × threads (`arena_faden`) → thread starts (`fadenstart`) → start exclusivity
(`startexklusiv`) → derivation edges (`ableitung`, `H021`) and bare cycles (`H022`) → **M3** →
**M2** → phases → pairing → groups → **costs**.

The **register** (`passliste()`) numbers twelve passes in a different order, the order of the
language specification: 1 Names, 2 D1/D2, 3 M1 + V1–V3, 4 M3, 5 M2, 6 M4/loops, 7 pairing,
8 effects, 9 costs, plus three that were found in use and booked afterwards (10 groups,
11 phases, 12 locks — numbered at the end so no reference in the specification moved). The run
order is not the register order (the numbers 10–12 were appended); costs run last. *A rule belongs to one pass of the register;
helper modules (`kontexte`, `fusswache2`, `arena`, `clone`, …) are "a rule of the X column", not
a pass of their own.*

Pass states (`Zustand`): **built**, **partly built** (something passes that should fall; the text
names it), **carried** (what a pass can say it says, and where the rest lies stands beside it
with an address — axiom layer, template, decision), **open** (not built; says what is
therefore unchecked). `gabbro paesse`, measured today: *3 of 12 built* (Names, M1 + V1–V3,
loops), *9 carried*, 0 partly built, 0 open. "Carried" is not a promotion: it is an address for a
remainder that is not pass work (the memory model, a template, a decision).

| # | Pass | State | The named remainder |
|---|---|---|---|
| 1 | Names | built | |
| 2 | D1/D2 | carried | `opaque` has zero bite on today's corpus (all twelve declarations are used in their own module); the residue is a corpus statement |
| 3 | M1 + V1–V3 | built | V2/V3 (relational and variant narrowing) are *conjectured* — no probe can isolate them (§4.4) |
| 4 | M3 | carried | the barrier a `dma` access demands is memory-model (axiom layer); alias, see §5 |
| 5 | M2 | carried | ghost erasure sits in the emitter, not in this pass |
| 6 | M4 / loops | built | |
| 7 | Pairing | carried | that `release`/`acquire` establish the visibility the pairing claims is axiom layer A10 |
| 8 | effects | carried | `E010` speaks only about known world state (`static`, `atomic`, `table`, `device`, `state`) |
| 9 | costs | carried | a call counts the callee's *declared* cost; a recursive function's `costs` is an assumption backed by `decreases` (`K008`/`K009`), not a result |
| 10 | groups | carried | *preservation* of a group invariant is the prover's, not the pass's |
| 11 | phases | carried | the softer reading (a set of stages) is a decision: from the strict reading one can loosen, never the other way (K11.1 (b)) |
| 12 | locks | carried | the finer half (`masks IRQ`, `per cpu`, `nested never` exempt only under `assume ein_kern`); alias |

### 4.2 Pass 1 — names, declarations, boundaries

Question: *is every declaration complete in exactly one place, and does every clause that names
something name something this unit declares, in the form the clause requires?*

| Rule | Codes |
|---|---|
| no name declared twice in a scope (items, construct bodies, parameter lists, every block); `reason` numbers unique; register fields on distinct bits; no `preserves`∩`clobbers` | `N001`–`N003`, `N009`, `N010`, `N017`, `N055` |
| bit positions inside their word, no overlap; offsets/strides/banks cannot alias or wrap the emitted `unsigned`/`uintptr_t` arithmetic | `N007`, `N008`, `N013`, `N047`–`N051` |
| no ghost/linear type in memory; no by-value self-containing record; no unlowerable float width | `N011`, `N019`, `F006` |
| a reference across a module boundary reaches a `pub` item | `N025` |
| every clause that names something (`entrust`, `offset_into`, `per cpu`, `requires Has`, `dispatch`, `gates`, `measures`, `mirrors`, a probe obligation, `observed by`, `format … where`, `step`, nominal types at `let`/`return`/argument, a `syscall`'s assumption) resolves, in the right form | `N004`–`N006`, `N012`, `N014`, `N016`, `N018`, `N020`–`N024`, `N026`–`N033`, `N040` |
| `or R` has a producer and a `let … else` consumer | `N028`, `N029`, `N034` |
| `asm` bodies declare `arch`, `effects`, `costs`, name real parameters; `-> never` with `asm` names no `out` | `A001`–`A004`, `N321` |
| an assumption's machine is one this unit declares | `A005` |
| a `falsifier` names something that *can* go red (`-> bool`, or a `-> never` watchdog at an `on_exceeded`) | `N056` |
| `section` only on a `static` | `N320` |
| names C has taken, or the generator forms twice, are refused at the declaration | `N041`, `N042`, `N046`, `N052` |
| `can_fail` yields a verdict on every path | `N044`, `N045` |
| device promises and carriers: a `depends` names carriers; a reader of such a register holds a lock on every written carrier | `N053`, `N255`–`N258` |
| function-pointer types carry `effects` and `costs`, and only call-carryable effect words | `N035`, `N036` |
| an immutable pointer starting at `0` is null forever | `N260` |
| a parameter list on a type only on a `linear ghost` witness | `N582` |
| `check … measures` resolves; `check` writes nothing it measures | `N021`, `N043` |

Details worth knowing:

* **`N041`/`N042` — the names C has already taken, and the generator's collisions.** The emitter
  writes Gabbro names into C unchanged. A table `cnamen.rs` holds what C owns; a table
  `erzeugernamen.rs` holds what the generator forms from a user name (`{Format}_gueltig`,
  `{Tabelle}_NONE`, `{Walk}_knoten`, …). Two declarations that get one C name are
  refused at the second. This matters because `cc` is *not* an oracle for it: whether `cc`
  complains depends on type compatibility, on whether at most one side defines, and on **textual
  order** (`static int f(void); int f(void);` compiles, the reverse does not). *A tool whose
  answer depends on line order is not the check for this question.* Measured on 2026-08-31 over
  the emitted forms: nearly every collision is silent in `cc`; the ones that are not fall
  for reasons unrelated to the class. `N042` is complete over the enumerated patterns; whether
  the enumeration is complete is open (`OFFEN O40`, half closed: `N042` also refuses two function
  bodies of one name in two modules with a private side).
* **Modules and `use`.** The resolver (`umgebung.rs::kandidaten`) walks the module chain inside
  out, then the `use` lines on the way; it is module-aware and `use`-aware. Without `--unit`,
  `gabbro pruefe` gives each file its own `Umgebung`; see §11.
* **Vocabulary.** The word list is closed (`kw.rs`, `SYNTAX.md` vocabulary table, guarded by
  retired `pruefe-wortschatz`). A closed list collides with names in foreign code at a measurable
  rate (K3, below, §11); since then keywords are *contextual* — `node`, `index`, `next`,
  `old`, `release`, … are accepted as identifiers where the grammar expects an identifier
  (re-measured 2026-10-17 with a probe: a `let node = …; let index = …; let next = …;` body
  parses).
* **Build gate (`G001`–`G003`).** `when TESTBUILD` is the only condition; a gated item must not
  be called by an ungated one, so the shipping call graph closes without the gated items.
* **Binding surface.** `pub` and `extern` names bind by their C name; no two exported
  declarations may share one in a build (`N039`); an export's visible part must not name a
  private item (`N038`) — see §4.15.
* **Quirk of the key map:** the key asymmetry in `N028`/`N029` (the map is filled under the short
  name, calls are looked up under the full path, so `m::f()` was never matched) is recorded in
  the sentence's reservation (`namen.klauselbindung`) and is not closed there.

### 4.3 Pass 2 — D1/D2 and the K condition

*D1/D2: opaque newtypes, complete layouts, exhaustive enumeration. The K condition: an
invariant a template establishes is not broken by hand.*

| Rule | Codes |
|---|---|
| `opaque type`: outside its module no carrier arithmetic and no implicit conversion in either direction | `D003`, `D004` |
| `match` on a `tagged type` names every variant, **no catch-all** — the one form that states a closed case distinction | `D005` |
| `table … tree` names real fields, each `option index into Self`, none pointing into a foreign table | `D006`–`D008` |
| `table … ops`: names an occupancy `bool` field; no hand write into an `ops` table or a `by ops` field; `breaking` is refused on such carriers | `D001`, `D002`, `D009`–`D011` |
| a call to a generated operation stands under the premises the template charges the caller (slot fresh for `insert`, parent reachable, leaf for `remove`, not on its own chain for `relabel`) | `D012` |
| `breaking I { … }` names a declared invariant (table, group, walk, `spec fn`), rests at least one carrier, and calls no maintainer of `I` | `D013`, `N531`, `N532` |
| `owner m`: names a `linear` type; exactly one minter (a bodiless signature), executed once outside every loop; every access holds the mark | `D026` (an `owner` table whose mark has no complete producer story — registered minter, exactly one mint call, a function that touches the table with it — is refused), `D265`–`D268` |
| a `requires`/`ensures` of a shared-side function that reads a table carrier calls a declared invariant by name, does not restate it | `D027` |
| an online `table`/`group` invariant is named by some function's `maintains` or its table has `ops`; a writer of a carrier of an invariant names it | `N583`, `N496` |

**The quantifier domains** (`domaene.rs`; nine domains: `slots of`, `chain(a, b) in`,
`descendants of`, `ancestors of`, `queue`, `fields of`, `elems of`, `threads`, `mappings of`).
A domain names a place; every name in a predicate must resolve to something. The checker held
that for `ensures` only until the measurements of 2026-08-31/09-02 (below). Today:

| Question | Code |
|---|---|
| the base name of the place resolves, in **every** predicate position (`requires`, `invariant` of table/walk/group, `spec fn` body, loop `invariant`/`until`, `floor`, `down`/`leaf` of a walk, axiom `requires`, …) | `D017` (domain place), `D021` (any predicate place), `M109` (`ensures`) |
| the place is of the kind the domain needs (table for `slots of`, record for `queue`, array field for `elems of`, `walk` for `mappings of`, a slot for the three tree walkers) | `D018` |
| the field names in the suffix resolve | `D019` |
| the fields of a bound mapping resolve (`mappings of` binds a record) | `D020` |
| the two field names of `chain(a, b)` name real, option-typed, own-table fields | `D014`–`D016` |
| the binder is *used* as the domain says (an index of the named table, …) and the body mentions it | `D022`, `D023` (hint) |
| `threads` binds a variable over no declared set, so a statement about its elements states nothing | `D024` |
| `count` over a domain needs a domain with a length | `D025` |
| `Held(L)`/`Held(L, shared)` is the whole guard form; `Held(L[i])`, `Held(f(x))`, `Held()` are refused where they are written | `N390` |
| a literal index in a predicate is inside the declared length | `M141` |

What the measurements found, so the shape of the rules is understood:

* **Predicate positions** (`PREDICATE-NAMES`): 19 positions × 20 kinds of name, a phantom name
  accepted in 266 of 380 cells before the repair and in 131 after; positions that resolve a name
  at all went 3 of 19 → 17 of 19. The reason it is a *proof-object* defect and not a missing
  finding: a predicate leaves the checker as an assumption (`gabbro lean` writes a `requires`
  into `<fn>_pre`), so a conjunct over a name that exists nowhere is a wrong proof object that is
  visible in no channel at all. *A rule that only fires over an otherwise empty clause
  (`N022` under `floor`, `U007` under `group`) answers "is this clause about anything", not
  "does this name exist".*
* **Quantifier placements** (`DOMAENENSTELLUNGEN`): of 72 corpus quantifier sites 19 were
  in `ensures` (read by `M109`) and 53 elsewhere — there not even the base name was read; the
  falsification of each of the 53 found two reports, both from `D012` for an unrelated reason.
  The rules `D017`–`D021` close the base-name and kind half; `D018` covers the *type* of the place.
  **Still named, not closed:** `fields of`'s path base (not read by `D017`), the `member` form of
  the domain, and the *typed* extent a place must have (the sentence `d.domaenenort` carries the
  gaps). (Counts are from the measurement day; the corpus has moved.)
* **Nine domains, which names does anyone check** (`DOMAENENNAMEN`): the table was
  *base name only in `ensures`; type nowhere; extra name — for `chain`'s two field names —
  nowhere*, and closed by `D014`–`D016` (`chain` was the one domain that names its edge at the
  walk instead of at the declaration, and the one whose edge nobody read), `D017`–`D021`, `D025`.
  `queue` says nothing in an annotation that `elems of` does not (the emitted C is
  byte-identical); `threads` hangs on no declaration.
* **`K003` and the domain bound.** A `traverse` costs body × the domain's cardinality bound, read
  from the declaration (a table's `count`, the one field array of a record for `queue`, the
  array length for `elems of`, the `count` of the table behind an `index into T`, and
  `node length ^ levels` for `mappings of`); where none follows, `K003` refuses instead of
  guessing. The calculus is *sharp* — `F09`'s `512⁴ = 2³⁶` is the page count of a 256-TiB
  address space — and *coarse in the safe direction*. Five domains' cardinality sources were
  cross-checked with off-by-one mutations of the bound (`K001-DOMAENENSCHRANKE` §8).

### 4.4 Pass 3 — M1: ranges, shapes, constants, strings, floats

*For every arithmetic operation, assignment, argument, return and index the checker computes an
interval from declared ranges and flow facts, and the interval fits its destination. Where
neither carries, the pass refuses instead of assuming.*

| Rule | Codes |
|---|---|
| the destination range holds the value (`M101`); no denominator range contains zero (`M102`); index inside the bound (`M103`); no result leaves the declared width — an overflow is a compile error, not a wrap (`M104`) | `M101`–`M107`, `M110`–`M119`, `M139`, `M140` |
| `narrow x to R else { … }` — the `else` must return or diverge; a checked comparison narrows the *branch*, and the fact **survives a call** unless the callee's declared `effects` can write the place (V1) | `M105` (the `v1.bereichsverengung` sentence also claims `M108`, `M109`) |
| no mixing `bool`/numbers; same *shape* and name at a slot (aggregate, pointer, array) | `M135`, `M139`, `M142` |
| `~` only over a width-bearing operand; `x << y & z` grouped differently in Gabbro and in C must be parenthesised | `M136`–`M138` |
| arity at a direct call (the precondition of every rule behind it) | `M143` |
| function pointers: only `&f` of a declared function; the **contract is subsumed** (effects ⊆, costs ≤, arity), the **signature is equal** (`M141`: types compare exactly); a call through the pointer is held against the type's `requires` | `M127`–`M129`, `M141`, `N295`–`N297` |
| overflow operators: wrapping (`+% -% *% <<%`) only on an exact unsigned range, saturating (`+\|`) on one shared range; unary minus checks `-INT_MIN`; `%` traps at the smallest value over `-1` | `M150`, `M152`–`M154` |
| bit intrinsics (`clz ctz log2_floor popcount rotl rotr bswap`): typed at the call, results exact; their names cannot be declared | `M157`–`M160`, `N058` |
| `refines g`: `g` a declared `spec fn`, same arity, at an `impl fn` | `M130`–`M132` |
| reasons: a returned/matched reason is a case of the channel the signature declares; matches complete or the reason says `exhaustive` | `M120`–`M126` |
| integer `match`: every value M1 knows the scrutinee can hold is named, each in exactly one arm; no arm outside the storage type | `N411`–`N414` |
| a loop `invariant` names something; a `.field` access is held against the known type | `M133`, `M134` |
| a stale-named local does not decide a branch (taint from carrier reads, expired by writes, loops, calls) | `M147` |
| `return v` only in a function that declares a result | `M148` |
| the ends of a declared range are integers (`type T = u32 in 0.5 .. 1.5` was accepted with 0 errors and lowered to the full word until `M146`) | `M146` |
| whole-array store: copy only between same-shape arrays whose source element range fits the target; else refused | `N579`, `N287` |
| tagged construction `Case(p)`, `Case()`, bare `Case`; arity, labels, ambiguity | `N280`–`N284` |
| empty answer types (a range with no value, a reason with no cases, a `fn(..)` no runtime function has, an empty sum/record) are refused where an axiom *answers* one — a false axiom makes everything after it vacuous | `N310`–`N314`, `N316` |
| bare store to an `atomic` has no form; index/element of an atomic array carries a shown bound | `N270`, `N271`, `N380` |
| index through a pointer lies inside what the pointer reaches: the extent is what the function's `requires` says about `lenof(p)` | `N571` |
| `reset X at i count n` names a static array; `aligned N` is a constant power of two ≤ 65536 | `N569`, `N570` |

* **Wide context rule.** An integer `+ - *` standing as the whole value in a declared non-wrapping
  context `T` of greater-or-equal width and same signedness class computes in `T`'s width (the
  rewrite a user would write by hand); `M104` stays silent where the result fits `T`.
* **V1–V3.** V1 (range narrowing under a checked condition) is measured; **V2** (relational
  facts `a >= b` → `a - b : 0 ..`) and **V3** (variant narrowing under a `match`) are
  *conjectured* — they have no code of their own (they *widen* what passes, so no direct poison
  probe isolates them); V2's one attempt to build such a pair found instead a
  non-determinism of the checker (the report `messung/DETERMINISMUS.md`, removed in `014b4d93`; V2 stays conjectured).
  V2's restrictions: comparison facts only, between directly checked places; a fact dies at every
  write to a place it mentions; a write through a pointer kills every non-local fact.
* **Constants.** A `const` initializer or const-table element outside the total effect-free
  fragment (`K190`), a count mismatch or an element outside its range (`K191`, `K194`), a
  non-`pure` function in a const's call hull or a reference cycle through a `const` (`K192`,
  `K193`), ragged nested tables (`N285`, `N286`). Const tables are element-wise: nothing is
  filled in.
* **Bounded strings** (`zeichenfolge.rs`). Lengths add; an index is held against the *length*
  not the max; strings are their own sort (flow only into a fitting `string max N` slot);
  they live only in parameters, results and `let` annotations; a string cell is read/written
  whole; `max` is in `1 ..= 65535`: `N453`–`N455`, `N465`, `N486`, `N581`. NUL-terminated paths
  built by the program carry their terminator: `N507`.
* **Floats.** The float prelude binds `-ffp-contract=off`; a finiteness fact is required
  where an operation needs one (`F001`, `F002`, `F004`, `F005`; fact from a declaration,
  `narrow … to finite`, or a literal). `GLEITKOMMA.md` carries the IEEE model; the old plan's
  stages F0–F8 are built through the checker/model parts named there.

### 4.5 Pass 4 — M3: pointers, address spaces, device registers

| Rule | Codes |
|---|---|
| writes go through a parameter whose right includes `w`, reads `r` (`own` satisfies both) — *only* parameters, *only* the base name | `R002`, `R003` |
| a pointer argument that is a bare parameter reaches a parameter of the *same* address space (`mmio` ≠ `normal`) and rights *narrow* at a call, never widen | `R008`, `R013` |
| a register field is read only if its class allows reading and written only if it allows writing — a class per **field** (a mixed register like `FSTS` carries both) | `R005`, `R006` |
| a class may differ per phase (`class rw in setup, r in live`) over a declared `order` | `R009` |
| a `requires … else R::case` at a register makes the read fallible; a plain read of it must be a `let … else` | `R010`, `R011` |
| no read-modify-write of one bit of a word whose read or write has a side effect (`w1c`, `rc`) — the rule is over the **word** | `R012` |
| no `ops` carrier on a `ptr<dma, …>` | `R001` |
| syntactic alias, root alias, boundary | `R004`, `R007`, `R014`, `R015` — §5 |

**Named remainder:** *the barrier a `dma` access demands* is memory-model (conjectured sentence
`m3.barriere`, no code, no probe, and there cannot be one until the memory model is written).
Address-space and rights checks speak about parameters only; a `let p = …`, a global, a field
or a return value carries no declared right.

### 4.6 Passes 5 and 11 — M2 linearity and phases

* **M2.** A linear value that is a *parameter* or bound by `let x = f()` from a direct call is
  consumed **exactly once** on every path: branches are walked on copies and reconciled; a value
  living before a loop may not be consumed in its body; neither a leak nor a second use passes.
  `L101`–`L105`, `L107`–`L109` (a value arising in the body: `L107`; inside a loop body: `L108`;
  arising in a branch, never consumed in it: `L109`). `leaves` names parameters of linear type
  that *survive* a loop and does not consume (`L106`). Real linearity is the one mechanism
  no existing tool supplies (Verus `tracked` and Rust are affine). Tracked sources are
  parameters and direct-call `let`s only; consumption matches on the **base name** (so
  `wecken(p.feld)` consumes `p`), a call statement does not descend into nested arguments, the
  `match` object is not checked.
* **Phases (pass 11).** M2 sees that a token is handed on exactly once, not in which *order*
  (six boot steps type-check in all 720 orders). `order { … }` + `advances a -> b`: stages exist
  and go forward (`O001`, `O002`); a step meets a token on its source stage (`O003`); the body
  reaches the stage it promises (`O004`); branches join on one stage (`O006`); a step is not
  inside a loop; boot steps chain (`O007`). The **boot theorem** layers: a `raw fn` demands a
  `linear ghost` token and no pointer is made to one (`O008`, `O009`); the token is retired by
  *one* event — retiring clause and `effects` name the same token, a postcondition over
  `mappings of` says what is gone, and the retirement's assumption is falsifiable
  (`O010`–`O013`). *Decision, not gap:* the strict one-stage reading.

### 4.7 Pass 6 — M4: loops and divergence

`leave`/`next` name an enclosing label (`S001`); the `else` of `let … else` diverges or returns
(`S002`); `progress X` names a declared **falsifiable** assumption (`S003`, `S004`); a `decreases`
measure names the traversal variable or a name the body writes (`S005`); `on_exceeded` names a
function that returns (`S006`, a hint `S007` if it names nothing declared); `by consuming` names
a `consumes` in its `touches` (`S008`); a `-> never` routine does not return — no `return`, no
fall-off (`S009`, the half that was missing: a declaration nobody holds against its body is a
promise). *Necessary, not sufficient*: that a measure *falls* is the prover's business.
The binder of a `traverse` is the label of its body (`leave i;`/`next i;`) except over a
`by consuming` walk (`N580`). Loop invariants are one grammar position across the three loop
forms (`traverse`, `retry`, `forever`, directly before the body) — the decision (2026-08-28) was
"reuse the word `invariant`, no second word for an existing concept"; `M133` refuses
`invariant true` and the obligation is counted (kind `S`, §9).

### 4.8 Pass 7 — publish/await pairing

`V001`/`V002` no orphan half (`publishes`/`awaits` on one atomic); `V004`/`V005` the ordering is
strong enough for a payload; `V008` the payload is in the declared superset; `V006`/`V007` the
payload is not written after its `publishes`, not read before its `awaits`; `V009` an atomic
without payload that gates a branch over a foreign shared place is a *missing* pairing;
`V010` the payload is written by the publisher's own hull; `V011`/`V012` an awaited value used
after a publish/hand-off without revalidation. **Coarse in the safe direction:** the pairing
runs over the unit's global set, not the transitive one — "somewhere in this translation unit
there is a counterpart"; the index is erased.

### 4.9 Pass 8 — effects

`effects` is mandatory on a function with a body **unless derivable**: since lane 191 an omitted
clause is derived from the body where the fixpoint settles; `E001` stays for functions without a
body, `N305` refuses the omission where nothing settles. `pure` stands alone (`E002`). The body
writes no non-local place that no write effect covers (`E005`), reads no *known* world state
no `reads`/`publishes` covers (`E010`), takes locks only declared (`E006`, `E007`); the declared
effects are closed over the call hull (`E008` — sound under an incomplete hull because the hull
is a lower bound; `E009` hint for the rest). A `can_fail` body is `pure` by construction
(`E008`). `traverse … touches` touches no more than named, callees included (`E011`).
Contracts are part of the frame: a known carrier read by `requires`/`ensures` is covered by a
`reads`/`writes` (`E220`, `E221`).

**Footprint guards of the goal theorem** (in this column, `wirkungen.fusswache`/`fusswache2`):
every carrier of a function footprint (its `requires` and `ensures` carriers, its body reads,
the contract carriers of direct callees, indirect calls) is guarded by a lock the function holds
by signature, protected by a lock invariant, thread-local, or written by no function
(`E245`–`E249`, `N290`–`N294`; `N294` a lock floor the ranks do not honour). The race component
(`N300`–`N304`): a carrier one declared start may write is neither written nor footprint-read by a
different start unless a lock guards it or it is atomic; a start has no reason channel, holds no
lock by signature, and a routine started twice is *pool-safe* only if it holds no lock, declares
no reason, and writes no unguarded carrier. A contract may not read a *shared atomic* (`N484`).

### 4.10 Pass 12 — locks, execution contexts, thread starts

* **Rank discipline** (`H006`, `H012`, `H014`, `H016`): every lock name is explained by a
  declaration; every lock has a constant `rank`; on every path a lock is taken only while a
  strictly smaller rank is held, **through calls too** (since 2026-08-19). Equal rank falls
  (two holders can take two locks in two directions). By the classical argument a wait cycle
  would give `r(L1) < … < r(Ln) < r(L1)` (**argued**: the argument is in the sentence `sperren.rangordnung`; the report `messung/H006.md` it cites was removed in the clean-up commit `014b4d93` and lives in the repository history). Outside it: a wait
  that is not a declared `lock` (a hardware handshake, a foreign body's internal lock), a path
  through an `extern fn` (incomplete hull, R16), and (`H022`) bare mutual calls without
  `decreases`.
* **Shared vs exclusive** (`H001`–`H005`): shared means read, not write; no exclusive take inside
  a shared one; `shared held <= N ops` declared; a shared block may call `requires Held(L,
  shared)` but not `Held(L)`.
* **`protects` bites** (`H007`–`H011`, `H017`, `H020`): every access to a protected place stands
  under its lock (a *declared* `locks` effect is not enough: `H020`; and a lock that is never taken
  shows up: `H008`, `H011`); RCU places: reads inside `observes` (`H009`), writes additionally
  under a real lock (`H010`), every domain name explained by an `rcu` declaration (`H017`),
  reclamation names its grace-period assumption (`H015`).
* **Driver handoff** (`H018`): a function that writes a DMA-visible buffer and rings the doorbell
  does both under one guard.
* **Contexts** (`H013`, `H101`, `H102`, `H222`): an `entry … dispatch` names an execution context;
  a place written through it that nothing declares shared falls; naming `masks IRQ` in an effect
  list says a function masks, not that it *runs* masked — an entry that reaches such a carrier
  must declare `nested masked`; an entry that **hardware throws** (a `via` path) takes no lock
  that fails to declare `masks irqs`; own state is written by at most one thread.
  `H102`'s trigger is any `via` word, not only `idt`.
* **Lock invariants** (`N275`–`N277`, `N511`): a `lock L protects { … } invariant I` — the
  predicate reads only protected carriers, is pure, names only carriers/constants (decidable
  shape, **decided, never proved**); at **every exit** of a `locks L { … }` section the invariant
  must follow from the acquire frame, the section's writes and the callees' *promises*
  (`ensures`, never their bodies); what cannot be shown falls (`N511`).
* **Own lock primitives** (`N323`, `N481`–`N483`): a bodied `L_nimm`/`L_gib` reads/writes a
  declared atomic, stores no program memory, takes no lock, and acquire/release actually
  synchronise. Foreign primitives are assumed (`OFFEN O26`, remainder).
* **Declared concurrency** (`W001`–`W003`, `N240`): the bodies of one `concurrent { f, g }` set
  write no common place (over transitive hulls; locks in both hulls, a `publishes` pairing, or an
  `atomic` clear a pair — the exemption is pair-level, not site-level); two context roots whose
  hulls overlap in writes must share a set (non-declared pairs are not concurrent); only complete
  hulls are compared (`W003`); distinct thread starts hold no signature lock in common.
* **Hosted `start { f, g };`** (`N458`–`N462`): roots are plain `impl fn`s, named once, not
  already started by the runtime, the starter holds nothing across the join, a started root
  touches no unguarded written carrier. A **`child` path** is a thread of its own from its first
  statement (`N456`, `N457`).
* **Arena × threads** (`N521`, `N522`, OFFEN `O20`): no `reset` beside a concurrent use of the
  same arena; no two concurrent routines touch one cursor without a guarding lock.

### 4.11 Pass 10 — groups

A `group` names at least two declared carriers (`U001`, `U004`), each under some lock (`U002`),
no two under different locks of the same rank (`U005`), every group invariant names at least two
carriers (`U007`); a function writing two or more carriers of a group holds the full lock
imprint at every write site, and no `return`/`leave`/`let … else` stands between the first and
last carrier write (`U003`, `U006` — a lock imprint is a statement about a *moment*). Preservation
of the invariant is the prover's (conjectured sentence `gruppe.invariante`).

### 4.12 Pass 9 — costs

`costs` counts operations (1 op = one Gabbro primitive: assignment, arithmetic, load, store; a
call counts the callee's *declared* costs; a `traverse` counts body × domain bound; branches
count the maximum plus their condition; what follows an `if` that always leaves is counted once).

* `K001` the body costs more than the function promises; `K002` a `locks` block more than its
  lock's `held`; `K003` an unknown callee/domain inside a body that promises; `K005` a promise of
  a shape the pass cannot read (refused, never dropped); `K006`/`K007` a `retry … bounded` and a
  `forever … per_pass` hold their bound; `K008`/`K009` a self-reaching function declares
  `decreases` naming a parameter; `K010` bounds are constant; `K011`/`K012` a `deadline` dates
  with a number and names a declared machine; `N421` a `locks` block that scans a full domain
  gets the chunking remedy (windows, each fitting `held`); `N322` a `syscall` carries a countable
  `costs`.
* **Parametric promises** (`costs <= 4 + 12 * lenof(m) ops`): a sum of a constant and multiples of
  non-negative quantities; the comparison is against the **smallest** assignment (all symbols
  zero) — `costs <= 40 * n` is zero at `n = 0`. Non-negativity is a premise and is checked;
  a product of two symbols is a refusal.
* The sentence `kosten.summation` is **argued** (the argument was written in `messung/K001.md`, removed in `014b4d93`, summary in the sentence; writing it
  found an *under*-count — an `else if` chain counted only its own condition per arm). A
  recursive function's `costs` is an assumption; a body with *symbolic* cost is not compared.
  `costs` on an `extern fn` is trusted like `effects`.
* **Costs are static counts, not a clock.** Latency statements rest on the `deadline` clause
  (a dated number, probe-falsified) and on the hardware assumptions, never on this pass alone.

### 4.13 Foreign boundary and system calls

* **`syscall` declarations** (`N063`–`N068`, `A006`, `N322`): in-registers distinct, no out
  register clobbered, every parameter bound once, registers are general registers of the declared
  machine (`x86_64`, `aarch64`), the `errors` map answers every listed errno once and every target
  is a case of the `or R` channel. A call counts `1 + fa` plus arguments. Raw call number,
  register map, errno decoding are *user logic*: nothing in the checker knows an operating system.
* **Target binding** (`N561`–`N568`): a gate written `via V` calls the kernel the *active*
  target binds `V` to; every `target` block binds every variable a gate uses; one active target;
  an `entry` binds exactly the signature of its dispatch; two linked units call one kernel.
* **Frame length** (`N463`, `N464`, `N506`): a transfer through a pointer is bounded by what the
  pointer reaches — a `syscall`/`extern fn` byte buffer carries `requires x <= lenof(p)`, and
  at every call each clause is *decided* (a passed array's length, a literal-derived bound).
  A foreign body takes no function-pointer parameter (`N574`); code reaches foreign code only as
  an `entry fn` a generated driver wrote (`N575`–`N577`); `...` only on an `extern fn`, ints and
  pointers behind it (`N573`).
* **Clone handoff** (`N446`–`N452`, `N456`, `N457`, `N572`, `N578`, `C185`): the `stack`
  clause names a register kept out of `clobbers` and `regs out`, claimed once, bound to a plain
  integer type; the `child` path never leaves into the caller's frame, never falls through, runs
  behind a `-> never` gate, reads no caller temporary or parameter the gate never handed.
* **Emitter-side refusals** (`C180`–`C187`, `T001`, `absenkung.rs` bound 18): the C emitter's
  stub-template rules. The C backend is **deprecated** (2026-10-15): these stay where they
  stand, untouched; `tearing.rs` (`T001`) and `absenkung.rs` are pure check modules that were
  never wired into `emit.rs` (sentence `emitter.reissstelle` *conjectured*).

### 4.14 Memory: arenas, release, regions

A heap is allowed, **but never one that grows without bound**: every allocation region carries
a bound. (This is the old "Simon's rule" of `dokumente/PRUEFER.md` §3; the forms, §6.5.) Built:

* **`arena A capacity lo .. hi`** (`N210`–`N214`, `arena.rs`): both bounds are translation-time
  constants; every `alloc` past the reservation owes its `else` (`N212`, counted like `costs`);
  indices are used only in the generation they were obtained in (`N211`: a `reset`, even
  transitively through calls/starts, consumes the generation of every index held across it).
  `N214` (in `m1.rs`): a place over an arena is exactly `A[i]`.
* **Growth with commit** (`N426`, `N466`): `grow A by n else { … }` commits a constant slot
  count and the whole run's commits stay below the ceiling; every `alloc` out of a dynamic arena
  names a slot below the path's committed prefix.
* **Pressure sampling** (`N584`, `N585`, unbounded arenas): the probe names exactly one nullary
  gate/function, answers an integer, has no error channel; the threshold is a translation-time
  byte constant. *(These two diagnostics are currently German text; see §15.)*
* **Slot release** (`N586`): `free A[i]` kills the name statically — a later read or second
  `free` falls; only a bare name bound by `alloc` to the current generation can die; a parameter
  index is borrowed. Open: `free` across function boundaries, aliases outside the tracked
  ownership discipline (`TODO.md` §1).
* **Static ranges back** (`N569`, `N570`): `reset X at i count n;` on a static array,
  `aligned N`.
* **Concurrency of arenas** (`N521`, `N522`, `O20`).
* **Lean side:** `ArenaDyn.lean` (the dynamic arena form), `FreiZustand` with four preservation
  theorems; the G exporter refuses release by name (`LG005`, `OFFEN O14`'s third form).

### 4.15 The library boundary: `.gabi`, export hull, linking

* `gabbro abi` writes a `.gabi`: the `pub` declarations without bodies. **It is valid Gabbro
  source** (head `// @gabi 1  lib bib`): the same parser reads it, the same passes check it, and
  there is no second format that can drift. `abi --compare` compares the computed effect hull with
  the written one. Without a bridge a cost promise across a file boundary fell *loudly*
  (`E009`, `K003`), so the bridge has a toll: what a `.gabi` carries and what it deliberately does not is a decision (next bullets).
* Hardware assumptions do **not** travel in a `.gabi` (a library that ships its `assume` lines
  forces its machine on every importer; an `override` at import is a proof obligation, not a
  replacement). **Lock ranks do travel** (leaving them out made the lock order unenforceable at
  the boundary: a ring across two libraries passed with 0 errors) — and absolute rank numbers
  do not *compose*: the union is ordered by whichever integers two authors picked, which can
  refuse a legitimate mixing (the narrower remaining problem). Representations of a type across
  two libraries, templates with proof state, and `arch` mismatches are the other items the old
  `«ABI»` plan names; the status of each beyond what is in the sentences is **not re-measured**.
* `N038`: the export set is **closed** — an exported declaration names no private item in the
  part that travels. `N039`: one C binding name per exported declaration in a build.
* **Linking** (`gabbro link`; `N501`–`N505`, `N516`, `N568`; Lean `GabbroZielVerbund`):
  separately compiled units are each checked alone, then every `extern fn` head a unit relies on
  is held against the other's body — signature (`N501`), contract as a *tree* (`N502`), effects
  (`N503`), costs (`N504`) — all units name the same hardware assumptions (`N505`), the linked
  program is checked whole, and a module in two units is refused (`N516`). `OFFEN O28`'s
  remainder: no semantic equivalence/refinement of contracts (only normal-form trees), no
  certificate for linked programs.

---

## 5. Ownership and aliasing (`own`, `R004`, `R007`, `R014`, `R015`)

*The long form is [`A1-OWN-PAPER.md`](A1-OWN-PAPER.md); this section is the checker's view of it.*

**The problem.** M3 and the lock pass cannot tell two names for one object apart: a lock that
protects `T` does not protect a second name for `T`; a write through one pointer changes what the
callee reads through another. For years this was the one remainder of the *race* class that
nothing carried (`gabbro alias` counts how large the surface is in five strata, "no refusal").
The real defect that motivated the rule: `messung/netz/udp-echo.gab::echo_beantworten(e, k, w, …)`
read a stale checksum with 0 errors, because `k : rw IpKopf` and `w : r Kopfworte` were two views
of one header.

**Decision (A1, paper gate, 2026-10-17).** No lifetimes, no regions of validity, no general borrow
checker — if a fragment ever needs one, that is the "fifth mechanism" finding, not something to
smuggle in. Instead: `own` is a **loan** (`ptr<…, own> T` means "`T` is `owner m` and the callee
`consumes m … allocs m`": the mark is borrowed for the call and comes back), and a **re-view**
(`fn(ptr A) -> ptr B`) **borrows**: the answer has the root of its argument.

| Rule | What it refuses | State |
|---|---|---|
| `R004` | the same syntactic place at two `own` parameters of one call | built |
| `R007` | the same syntactic place at two writable parameters of one call | built |
| **`R014`** | two pointer arguments of one call with the **same root**, one parameter writable or `own`. The root of a pointer is the parameter it came from; a re-view keeps its argument's root; **a pointer this pass cannot trace (a field, an index, an indirect call, an argument that is no bare name) is UNKNOWN and equals every root** | built; probe `beispiele/gift/1444-alias-sicht-und-quelle.gab` (re-run 2026-10-17: falls with `R014`), positive twin `beispiele/1163-sicht-neben-eigener-quelle.gab`; booked as 0 `R014` over every tracked `.gab` (not re-measured) |
| **`R015`** (hint) | a `pub` or uncalled function that assumes two of its pointer parameters distinct (one writable/`own`): the distinctness is a **named assumption about a caller outside the unit** — said at the function so it is read, not inherited in silence | built (a hint, not a refusal: refusing would tighten every exported function with a pointer pair); `messung/netz/udp-echo.gab::echo_beantworten` now carries it |
| `noalias` | the LLVM backend puts `noalias` on a writable pointer parameter **only** where the checker has the whole call in view: function not `pub`, has a body, is called from a body of the unit, its address is nowhere taken, no entry/`boot`/`concurrent` names it, and its declared `effects` name only its own pointer parameters. A unit with a function value outside a function body gets no extension. It rests on the `R015` assumption for `pub` callers | built (`llvm.rs::noalias_innen`, `tests/noalias.rs`) |

**Under-approximations, stated** (in the sentence `m3.zeiger_wurzel`): the walk over `let`s is
flat (no scoping; a name bound twice carries the union of its roots); two *different plain
parameters* pass (the callee's inherited precondition — S-2 in the paper); aliasing through table
indices (`slots[a]`, `slots[b]`, `a == b`) is **not** covered by roots and remains the M1
index-distinctness question. An earlier reading skipped any pair in which one side had no root;
the Lean slice 2b proved that reading unsound (`ObjektWurzel.rust_lesart_luecke`) and the rule
was closed on 2026-10-17 (an untraceable pointer equals every root).

**Lean (slices 2 and 2b, `grammatik/Grammatik/Logik/Vertraege/Getrennt.lean`, `Objekte.lean`,
`ObjektRahmen.lean`, `ObjektWurzel.lean`, `*Zeuge.lean`; SATZKARTE §74, §75).** `ParamGetrennt`
(at the granularity of a carrier/table), `ObjGetrennt` (finer: an object is one slot — the pair
of the capability `ptr n rw` and an index); `objGetrennt_ein_obj_iff` (with one object per
carrier it *is* `ParamGetrennt`), `rufAt_obj`/`obj_ruf_rahmen` (under `ObjGetrennt` every run
leaves every field of every read-only parameter's object), the bridge `r014_objGetrennt` from
`R014`-clean to `ObjGetrennt` under **four named hypotheses** — `ParamVerschieden` (the `R015`
boundary assumption, never discharged), `FrischNeu` (fresh answers are new objects; proved for
the model's allocator), `RechteOk`, `HerkunftTreu` (the checker's walk over `let`s names what
its provenance denotes; the walk is **not** formalised in Lean) — and non-degenerate witnesses.
Standard axioms only.

**Open** (the paper's §6/§7 and `TODO.md`): (1) objects are single slots — a record laid
over a byte buffer (a `format`, n slots) is not one object, so the cross-type re-view of
`udp-echo` (`kopfworte_von : ptr IpKopf -> ptr Kopfworte`) still has no model statement
(`LG005`, `LG001` refuse it in the exporter); (2) the discipline is a `Prop`, not yet a Bool the
exporter could compute; (3) whether the `R015` boundary should grow into an explicit `own` at the
boundary is *recorded, not decided* — `TODO.md` §3 still lists "Alias (decision pending)", which
the built slices have overtaken in part; (4) `free` across function boundaries (§4.14).

---

## 6. Library syntax, the translation stage, hardware profiles, bounded memory

*(Formerly `dokumente/PRUEFER.md`. Its section numbers are cited from code comments; §6.1–§6.7
below carry them: old §0 → 6.1, §0b → 6.2, §0c → 6.3, §1/§2 → 6.4, §3 → 6.5, §4 → 6.6,
§5/§6 → 6.7.)*

### 6.1 The idea, and why it fits

A library may bring its own syntax, invoked as `@<library>#<name> ( args ) { region }`
(for example to write GPU kernels). The load-bearing observation: **an expander never needs to
be verified, only its output checked.** If a region turns into a payload that the ordinary
checker then judges, the library is not part of the trusted base — a wrong library produces a
term the checker refuses. Gabbro can enforce what Rust procedural macros cannot: a translator
is a Gabbro function with `effects { pure }` and `decreases` (`N202`, `N203`) — a total,
effect-free map; determinism and termination are a signature, not a convention.

### 6.2 Run time versus translation time (old §0b)

`@lib#f ( args ) { region }` is a **run-time call** of `f` in `lib`; the region is read and
checked **at translation time**. The library's declared *translator* turns the region into a
**payload** (a value of a payload type the library declares: a table or tree type); the checker
checks the payload is a well-typed value of that type. At run time the call is an ordinary
library call with a contract. **Gabbro code is always compiled at translation time, never at run
time**: no Gabbro source, region or AST is compiled, generated or interpreted while the program
runs; what the program does at run time is unrestricted within that rule (TCP, files, launching
GPU work) provided the code doing it was fixed at translation time. A portable intermediate format
(SPIR-V, PTX) is therefore *admitted*; the driver lowering it is a **named assumption** of the
hardware profile.

### 6.3 A library is safe Gabbro with no contradicting assumption (old §0c)

Contradictory assumptions make every proof over the combined program vacuous — the defect class
the early review waves kept finding (premises no ordinary program can satisfy), here at the level
of hardware. Consistency is therefore enforced **by structure**, never by comparing prose:

1. **Safe Gabbro only.** A function reachable through `@lib#f` is checked by the same checker;
   no foreign body (`extern`, `raw`, `prim`, `asm`) anywhere in its call hull (`N059`).
2. **One hardware profile per program** (`N219`): a `profile` block; a library *requires* profile
   entries by reference to the declared assumption, never by a copy of its text; linking refuses
   a library whose requirements are not in the profile (`N217`) — consistency becomes a subset
   check against one set.
3. **Keyed assumptions for modes and resources** (rounding mode, FP contraction, memory-model
   mode, interrupt routing, arch): two entries with one key and different values are refused
   (`N215`); a same-named assumption with a different statement is refused (`N216`); the profile
   is held against the platform — `fp_contract` other than `off` contradicts the float prelude,
   an `arch` the unit never declares contradicts the declared machines (`N218`).
4. **Exclusivity by linearity:** device/register access reaches a library only as a linear
   capability (`owner` mark, `eigner_nie_erzeugt`).
5. **In Lean** the program theorem takes ONE assumption set; a library's set is a subset; for
   keyed mode assumptions with pairwise distinct keys a theorem constructs a model, so the
   profile is *satisfiable by construction*, not merely unrefuted.

### 6.4 Extension slots, not free mixfix; hygiene (old §1, §2)

A library region is a **delimited region** (up to the matching brace; the surrounding grammar is
unchanged — the Racket `#lang` principle). Free operator definition in open text is excluded: it
makes the grammar depend on load order, fatal for a language whose claim is "the grammar is the
type system". What an expander works on is mostly present: trees as tables (`table … tree`,
`reaches`, `descendants`, `ancestors`); binding structure in the AST *type* (typed de Bruijn
indices in the Lean model — hygienic by construction); guardians moving to the core term after
expansion; and **error mapping** back to the line in the extension syntax (the span map,
`regionkarte.rs`, built: every diagnostic about region content reports through it).

### 6.5 Bounded memory — the three forms (old §3)

Rule: a heap is allowed, never one that grows without bound. The forms differ in proof load:

| Form | Release | Fragmentation | Allocation can fail | In Gabbro |
|---|---|---|---|---|
| arena, monotone, reset as a whole | only all at once | no | only beyond the upper bound | built (§4.14) |
| pool with fixed element size | per element | no | only when full | exists: every `table T count N` with generated `insert`/`remove` |
| general bounded heap | per element, any order | yes | also below the upper bound | not built unless a concrete case forces it |

The arena is a **linear mark**; its reset consumes it and allocates a fresh one; an index into a
reset arena is not expressible; *use after free falls out grammatically, without lifetimes*. The
lower bound is a **reservation**: allocations statically within the reserved share need no
`or R`, only the share between lower and upper bound owes the error branch. **Dynamic structures
are in scope** (decision 2026-09-28): heap regions with a declared ceiling and refuse-on-full;
**planned, not required**: an explicit region without a ceiling (every allocation may fail and
must be handled; the static whole-program memory bound is lost for such a program). A heap
without a ceiling stays refused by default; the sampled unbounded arena of §4.14 is the opt-in
that exists (`TODO.md` §1).

### 6.6 GPU kernels — where the real boundary is (old §4)

Keep two things apart: (a) *syntax that expands into core Gabbro* — cheap, the checker stays the
last instance; (b) *a library as a second emitter* (SPIR-V, PTX) — after it nothing checks any
more, so it stays inside Gabbro's promise only if the library **exports its hardware
assumptions** (named, in the manifest, composable). Direct SPIR-V emission, not through OpenCL C
(measured in the design phase: a complete G1 kernel `out[gid] = in[gid] * 3 + 1` with its bounds
guard is 29 distinct opcodes, 760 bytes, accepted by `spirv-val --target-env vulkan1.1`; not
re-run). Stages: **G1** map kernels (race-free by construction, under two structural conditions —
the own cell is a *form* `out.mine`, not an index; input and output buffers are disjoint), **G2**
fixed patterns (reduction, scan, histogram proved once), **G3** free kernels with workgroup
memory and barriers (research grade, **not planned**). **No GPU backend, translator, or SPIR-V
emitter exists in the tree** (grep 2026-10-17: the word occurs only in comments and test text);
nothing comes before the verification core closes.

### 6.7 What is built (old §5, §6)

| Lane | Deliverable | State |
|---|---|---|
| E1 | call syntax `@lib#f(args){region}`; region captured as a brace-balanced token tree | built: `N057` (resolves nowhere), `N069` (resolved, region not interpreted outside the first cut) |
| E2 | library function declaration: `library fn` with `payload <table>` and a Gabbro body | built: `P043`, `P044`, `N059`–`N061` |
| E3 | translator declaration: `effects { pure }` + `decreases`, answers the payload table; exactly one per library fn | built: `N200`–`N204` |
| E4 | `arena A capacity lo .. hi` | built: §4.14 |
| E5 | translation stage: run the translator at translation time, check the payload | **first cut only**: exact-length integer regions fill a single-integer-field table row by row through the identity translator (`N230`–`N234`); the emitter passes the payload as a `static const` table. General translators wait for translation-time value evaluation |
| E6 | hardware profile + library requirements | built: `N215`–`N219` |
| E7 | error mapping through the span map | built: `regionkarte.rs` |

The order the old plan fixed for the rest stands: (1) total effect-free compile-time evaluation
returning values (tables, trees), (2) the compile-time arena, (3) the AST as a Gabbro data type
with binding structure, (4) expansion into the core with a certificate and error mapping,
(5) only then an execution model and a second emitter with exported assumptions.

---

## 7. The assumption layer, probes, and the bar for `unfalsifiable`

*(Formerly the `SONDENDECKUNG` and `UNFALSIFIZIERBAR` registers, retired 2026-10-17 with their guardians; see git history.)*

### 7.1 The model

A hardware or environment dependency enters the program as `assume`, `axiom` or `retires` (a
`syscall`'s contract is an assumption too). Each takes **either** `falsifier <probe>` **or**
`unfalsifiable "<reason>"`; the absence of both is a translation error (the grammar forces the
tail, so the *count* measures the grammar, not care). `gabbro annahmen` is the manifest of what a
program rests on; `gabbro zeugnis` adds templates with proof state, foreign bodies and `asm`
lines. A falsifier names an **external** program (`instrumente/sonden/*.c`; contract: return
**0** = not refuted in this run, **1** = refuted or the probe proved itself blind, **77** = not
runnable here). A name resolving to a unit function must be able to go red (`N056`).

An assumption is in exactly one of three states:

| State | Watched by (today: nobody) | Ratchet |
|---|---|---|
| **unfalsifiable**, under a criterion | the retired `pruefe-unfalsifizierbar` | down |
| **falsifiable, probe stands as a program** | the retired `pruefe-sondendeckung` | up (`A_p`) |
| **falsifiable, probe MISSING** | nobody, until the quota existed | — |

### 7.2 The bar for `unfalsifiable` (written before any row was classified)

Two admitting criteria, four rejecting rules; a criterion that admits everything classifies
nothing, so each carries a test that can say no.

* **`U1` — the observation IS the violation.** No refuting observation can be arranged without
  performing, as part of the arrangement, an instance of exactly what the assumption denies.
  *Test:* write the probe's setup step by step; if a step is itself an instance of the denied
  event, `U1` holds; a passive reader (snapshot and compare, a counter, a fault handler) fails
  `U1`. A probe that is merely dangerous, privileged or slow does not pass `U1`.
* **`U2` — the negation has no finite witness** (an unbounded liveness claim such as "an IPI is
  eventually delivered"). *Rider:* `U2` admits the sentence as written, not that it had to be
  written that way — a row admitted under `U2` carries a standing repair (write the bound and it
  leaves the register).
* **`R1`** a green-direction reason is not a reason (an argument about why no run could ever
  *establish* the assumption; falsifiability is the *red* direction — name one observation that
  would kill it); **`R2`** a reason about the bench ("qemu64 has no x2APIC") belongs to return
  code 77, not here; **`R3`** the subject is not the environment (a sentence about the toolchain
  or the program's own text has no external probe by construction — it is misfiled, a pass or
  poison probe refutes it); **`R4`** if no observation could distinguish truth from falsity,
  nothing rests on it.
* *Live state* (measured by the retired `pruefe-unfalsifizierbar`, run 2026-10-17): **8 clauses in the tree, 8 rows, 1
  ADMITTED** (`ipi_kommt_an`, under `U2`), the rest refused under `R1`–`R4`; 6 construction sites
  of `Klasse::NichtFalsifizierbar` in `manifest.rs`; ALL PASS (line numbers of three rows are
  stale by one or two lines: a notice, not a failure). Three teeth: row set equals corpus both
  ways, two ratchets down (population, admitted), every row's rule is one defined above; an empty
  table is a refusal.

### 7.3 `A_p` — the probe quota

The old gate "`A = 19` assumptions" was a prediction of a delta, not a bar over the trust surface:
under it the cheapest way to pass is to write fewer programs and the second cheapest is to write
`unfalsifiable` twenty-five times. It was replaced by a **proportion**:
**`A_p` = falsifiable assumptions whose named probe stands as a program in `sonden/`, divided by
falsifiable assumptions** (corpus = `beispiele/` plus the entries the checker generates:
`sonde_mxcsr_rne`, `sonde_keine_ueberbreite`, and the `retires` names). "Stands as a program"
means `sonden/<probe>.c` exists, nothing about whether it runs green.

* **Floor `A_p ≥ 1/8`**, chosen so the tree **failed it on the day it was written** (1 of 38) —
  *a bound the tree already meets is a decoration*; the price (four probes with positive controls
  that were made to fall: MXCSR rounding mode, no x87 overwidth, TSC monotonicity, `rdtscp`) was
  paid on 2026-09-04. The floor may be raised, never lowered. The probe classes (`P1` ring 0,
  `P2` device, `P3` multi-core/timing, `P4` userland) say what a probe would need to exist; only
  `P4` can be written without new hardware.
* **Ratchet** on the proportion; **orphans** (a built program no `falsifier` names) ≤ 1
  (`sonde_release_sichtbarkeit`: refuted under `R1`, its probe already exists with a control that
  fell 3,079 times in 1.5 million rounds — the sharpest single fact of the register).
* **Teeth:** rows == corpus both ways; no assumption twice; the row names the probe the corpus
  declares; the class is defined; the program column agrees with `sonden/`; the ratchet; the
  floor; the floor stays *reachable*; orphans; `SONDEN_MIT_PROGRAMM` equals `sonden/*.c` (coverage
  claimed in the checker with no program behind it would raise `A_p` with no program written);
  plus four teeth over the reader (so a blind scanner is not green: `W17`).
* *Booked state* (last full run of the retired guardian; **not reproducible today**,
  see next bullet): 18 of 51 falsifiable assumptions carry a probe that stands as a program; the
  floor was met on 2026-09-04 at 6 of 39 = 0.154; the register has since grown to 55 rows, 79
  distinct probe names stand across the non-poison corpus, 26 of them outside the register.
* **`A_p` is not guarded today:** `pruefe-sondendeckung` (which measured it) was retired on 2026-10-17
  (see git history); the figures above are its last measurements.
* **What no tooth does:** whether a probe would actually refute its assumption; that is nobody's
  script. A declared dependency can also be omitted from the declarations altogether.

---

## 8. The pass register: sentences, states, ratchets

*(Formerly `PLAN.md` PL and the retired `PASSREGISTER` register; code: `saetze.rs`.)*

### 8.1 Sentences, states, ratchets

**Why it exists.** `struct Pass` had no field for a sentence: twelve passes decided about every
program, hundreds of refusal codes — and *zero sentences*. Without the sentences "formally
verified" is not even formulable, because nobody would know what there was to prove. Each pass now
owes **sentences**: what is *true of a program that passed without a refusal*. A sentence has a
name (`m1.bereich`), the codes it claims, the statement (`aussage`), the reservation
(`vorbehalt`: what the pass does not do), the state, how it is measured (`gemessen_an`: the poison
probes, mutation anchors), and where it lives (`fundstelle`).

**States.** *measured* (a poison probe falls, or a mutation of the rule is caught), *argued* (a
correctness argument is written and human-reviewed, not machine-checked: `sperren.rangordnung`
→ `messung/H006.md`, `kosten.summation` → `messung/K001.md`; both reports were removed in the clean-up `014b4d93`, the summaries stand in the sentences), *conjectured* (nothing measures it),
*proved* (a Lean theorem that the Rust rule implements the sentence; none today).

| Figure | Value (measured 2026-10-17, `gabbro paesse`) | Re-measure |
|---|---:|---|
| sentences | **216** over 12 of 12 passes | `gabbro paesse` |
| measured / argued / conjectured / proved | **208 / 2 / 6 / 0** | same |
| diagnostic codes claimed by a sentence | **443** | same |
| codes without a sentence — the ratchet | **55 booked** (ratchet held by `instrumente/pruefe-pruefer.py` stage 2, `teile/saetze.py`) | `./instrumente/pruefe-pruefer.py` |

The six *conjectured* sentences are `v2.relationale-verengung`, `v3.variantenverengung`,
`m3.barriere`, `m2.geisterloeschung`, `emitter.reissstelle`, `gruppe.invariante` — each
named "so the hole has an address". The two *argued* ones are the lock order and the cost sum.
*What a "measured" sentence says:* the **implementation** on checked cases — never the rule and
never all cases. *"0 of 216 have been to a prover" is the number the old plan PL.2 is about.*

**The "55 without a sentence" are a drawn line, not an oversight.** Some codes establish a
premise a proved theorem needs (`N047`–`N049` establish `getrennt r s` for
`Device_Konstruktor.thy`; `N050`/`N051` keep the *conclusion* true of the lowering) — a theorem
apiece would be a fourth statement of the same fact ("a pass whose premise nothing needs has
moved the trust base, not shrunk it"). The ratchet may only fall; a new code arrives *with* its
sentence in the same commit.

**The three steps of the register** (old PL.1–PL.3):

1. **PL.1 — the register** (`gabbro paesse`), (its second tooth, the ratchet "no code without a
   sentence", is stage 2 of `instrumente/pruefe-pruefer.py`).
2. **PL.2 — the first sentences that matter** were selected and a first batch of rule models
   proved (§12.1).
3. **PL.3 — the bridge between the model and the Rust**, in three candidate ways; the one taken
   is **(c)**: per-case evidence — the poison probes and mutation anchors that the register
   names, not a proof about the implementation. A sentence's `gemessen_an` therefore points at
   files; `gabbro schablonen --gate` (tooth 3) falls while a *proved* template has a premise no
   pass establishes (the retired `pruefe-schablonen` ran this tooth; `gabbro schablonen --gate` still does).

Reservations in the sentences that are worth reading *before* trusting a green run (full text:
`gabbro paesse --je-satz`):

* `d.handmutation`: passing does **not** mean the K condition holds — `breaking` blocks are
  collected and reported but the K-condition report is not itself a refusal; a mutation *through
  a call* is not a write site; `D002` is name-based and too wide.
* `m2.linear-genau-einmal`: only two sources are tracked (parameters, direct-call `let`s);
  consumption matches the base name.
* `paarung.keine-waise`: global set, erased index.
* `wirkungen.abschluss`: the check continues over an incomplete hull, `E009` stays a hint.
* `phasen.fluss`: `O004` fires only if the body takes a step at all — an attempt to refuse the
  empty body was withdrawn (the corpus refuted it in one run: a driver function that does its work
  through a helper and hands the token back).
* `sperren.schutz`: `H007` counts a *declared* `locks` effect as held; `H011`/`H020` close that
  from the other side.
* **Some reservations predate later work** (for example `v2.relationale-verengung` says "there is
  no alias analysis anywhere in this checker"; `R014` is a root analysis since 2026-10-17). The
  sentences are the register; when the code moves, the sentence moves in the same commit
  (see §15 for the places known to lag).

### 8.2 Named classes of defect (cited from code under the old `PLAN.md`)

* **The fifth class — declared, exported, never read.** A clause stands there and no pass reads
  it: *nobody knows something.* Found by hand three times in two weeks (`rank` declared and in
  the certificate but held against no lock order; `opaque` declared as a prohibition that bit at
  no computation; `ensures` counted in the certificate and held against no body) before it got a
  tool, the retired `pruefe-klauseln` (2026-10-17; not guarded today), which held every `pub` field of every AST struct against the set of
  fields some pass accesses, with the readers split in two camps — *checked* under
  `gabbro-check/src`, merely *lowered and reported* in `emit.rs`/`zeugnis.rs`/`gabbro-cli` — and
  the separation is the statement. One level up, the retired `pruefe-konstrukte`: a *construct* with no
  generator.
* **The sixth class — proved, and established by nothing.** A sentence is **proved** and its
  premise is established by no pass: *one knows something false.* `device.konstruktor` stood as
  proved while its main theorem assumed `getrennt r s` and nothing computed it (the offset was only
  lowered). Whoever reads "proved" in the certificate concludes non-overlap, and the proof covers
  the gap instead of showing it. **Tooth 3** (`gabbro schablonen --gate`):
  every proved template binds its premises, and `durch` has three strengths — *a pass* (covers every
  program the translator ever sees), *a mutation probe* (covers the generator, once — the bridge of
  PL.3), *none* (the sentence hangs in the air). Measured when introduced: 17 premises of 9 proved
  templates, 8 without a producer. The ratchet on `L` (proved templates that are live but uncovered) was written as
  **code** rather than a comment after an audit found it reached 4 on a single day with only an
  equality pinned to the day's value standing against it (`schablonen.rs`). Today
  (`gabbro schablonen`): 41 entries, 48 admissible — "every further one costs a proof".
* **Translation validation (the path chosen in K100.4: way (b)).** Two ways to refine a lowering:
  (a) a verified generator (`emit.rs` itself in a prover — what CompCert did) or
  (b) **a machine-checked certificate per translation** that *this* C preserves *this* Gabbro.
  The differential tests are already the weak form of (b): one result instead of all. The first
  stage built is `gabbro zeugnis <file>` — five sections per file (assumptions, templates, direct
  lowering, deleted, **foreign**); its classification is a *second reading*, independent of the
  emitter's `match` cascade, and a form the emitter lowers that no classification knows is
  `UNZUGEORDNET` ("the emitter grew and told nobody"). *A certificate for this translation is not
  a statement about all inputs: it says what the translation rests on, not that it holds.* The
  active target is now direct machine bytes (`PLAN-UEBERSETZUNGSVALIDIERUNG.md`); the C
  certificate chain is legacy evidence.
* **`comptime`: the line.** `const fn` computes *values* — it costs no template; comptime that
  *generates code* would cost a template that must be proved. A `const fn` is in the total,
  effect-free fragment (`K190`–`K194`, §4.4); there is no code-generating comptime.
* **An empty run looks like a pass.** A report is a gate only if it prints the *count* beside it:
  `gabbro kontexte` prints the number of touched places (on the corpus it was empty because all
  four `dispatch` targets are `extern fn` — "and exactly that is what one should see"); M1 prints
  its coverage line; the `Not checked in this run` block names the carried passes.
* **Races were once declared "not buildable"** (2026-08-16): "whoever runs concurrently, Gabbro
  does not say" — and then `entry … dispatch f` **was** the enumeration of contexts. The sentence
  was overtaken by its own construct and nobody noticed; `H013` is the rule that closed it (§4.10).
* **Floating-point interval propagation must round outward** (`m1.rs`, F3 of the float plan):
  `[a,b] + [c,d]` is `[RD(a+c), RU(b+d)]`; computing the bounds with host doubles in round-to-nearest
  would make them up to one ulp too *tight* — unsound in the direction that reports nothing.
  Floats lower with `-ffp-contract=off`; `GLEITKOMMA.md` carries the IEEE model.

---

## 9. Obligations: what a human still owes

*(Formerly the retired `PFLICHTEN` register and the `H`/K100 plans.)*

`gabbro pflichten <file.gab>` — *"what a HUMAN still owes here. Counted, not discharged."* The
register is the checker's honest answer to "what did you not prove for me": every duty a clause
creates that no pass can close, in the form a prover reads (`--isabelle`, `--lean`, `--g`, with
the header `goals + refused = total`). Kinds (single letters in the output):

| Letter | Kind | Arises from |
|---|---|---|
| `E` | preservation | a `table`/`group` invariant × each function that maintains it |
| `N` | postcondition | each `ensures` conjunct |
| `F` | foreign duty | an `ensures`/`maintains` on a bodiless declaration |
| `V` | precondition at the call site | each `requires` conjunct of a callee, inherited by every call (the price of the *weak* reading of `M115`: refuses only where the argument's range *excludes* the condition; the count undercounts and says so) |
| `R` | refinement | `impl fn f … refines g` |
| `D` | device promise | `reg … requires …` (counted, never a fact: a hostile device may report anything) |
| `S` | loop invariant | `traverse/retry/forever … invariant P` |
| `W` | invariant owed by no function | a `walk`, or a `table`/`group` no `maintains` names |
| `L` | lock invariant | `lock … invariant I` at each release (recorded beside `N511`) |
| `C` | contract implication | higher-order refinement at a function-pointer slot |

Sample (measured 2026-10-17 on `beispiele/01-tabelle.gab`): `15 obligations: 0 refinement,
3 preservation, 4 postcondition, 0 foreign, 5 precondition, 0 device, 1 loop invariant,
2 unowned invariant, 0 lock invariant, 0 contract refinement`. *The K/A/W classification is a
judgement and deliberately does not stand in the output — the tipping rules demand one sentence of
reasoning per obligation.* A `maintains` is matched against an invariant by name; a name that is
no invariant is refused (`M112`), while a rename onto another declared invariant legitimately
changes the books.

**The criterion that decides plumbing versus logic** (`BEWEIS.md`): an obligation that *mentions
only the machine* is **plumbing (K)** and must fall in a pass; one that *mentions the subject* is
**logic (L)** and is the person's. A gap in a K row is a breach of the thesis at that site. The
criterion was applied by hand to the ten frozen fragments of the kernel code Gabbro was designed
for (`messung/fragmente/F01`–`F10`, one `.gab` each: cap space, VT-d, IPC fastpath, a virtio
driver, a service loop, a test scaffold, a loader, a scheduler, an MMU walker, a DTB parser).
The retired `zaehle-pflichten` read the table rows of the retired `PFLICHTEN` register: **239 obligations, 173 K
and 66 L** (last run 2026-10-17; not guarded today). **`H` — the plumbing duties still hanging — is 1** (the lowering of
`F3` has no differential test; same retired counter: Notation 0, Absenkung 1; the
other nine fragments' lowerings were measured by execution in the retired `pruefe-emission`, a legacy C check). *Do not read
`H = 0` as "the lowering is right": it would mean no obligation is open, and the lowering proof is
a different layer.* Nor as a statement about Gabbro: the ten fragments were chosen for
difficulty by people looking at the language, and a corpus nobody saw while building is what
would resolve that (the first such measurement, K3, §11).

Rows from the fragment tables that rules cite:

* **`F10` (DTB parser) — the format reader.** `format … where` and `offset_into` are what justify
  that **after a `format` access no further length check is needed**: the reader never delivers a
  structure that violates them. The emitter writes the `where` clauses as one function
  (`F_gueltig`) so the caller states them once; `N032` holds the names in a `where` clause
  (a field of the format or a constant) because the clause is a promise other rules build on
  (cited from `emit.rs`, `namen.rs`).
* **`F1` (cap space), `delete_leaf`** — the calibration set for the breakdown: eleven of its rows
  are the published K/L breakdown; `revoke`'s declared `costs <= 200 ops` was caught by `K001`
  five orders of magnitude short of the true bound (16,452,480).
* A booking that *points at a rule that looks elsewhere* is worse than an open line: it looks
  closed. The register-class rows were booked as discharged by `R002`/`R003` (pointer rights) for
  weeks; `R005`/`R006` (per-field register classes) are the rule that actually does it.

---

## 10. Simplicity without losing a guarantee

*(Formerly `dokumente/PRUEFER.md`; its measure is §0 there.)* **Measure:** a simplification is
accepted when **the ceremony count goes down** (`gabbro zeremonie`: the burden per rule with its
reason; calibration in `--table`) **and the pass register stays constant** (§8: every guarantee,
with the code that enforces it). Both numbers are booked before and after each step; a step that
lowers the first and moves the second is refused whatever it saves. **What cannot be made
lighter:** deriving `ensures` (what a function *should* do cannot be inferred — a tool that
guesses the postcondition guesses the specification and the proof then proves nothing); turning
refusals into warnings (gives up a class); uncounted exits.

| Lever | What | State (verified 2026-10-17) |
|---|---|---|
| 1 | **Derive instead of demand, and turn the meaning of the clause around.** `effects`/`costs` were about 767 of ~980 clause sites. An omitted clause is *derived* (the hull the checker computes, `kosten.rs`) and checked exactly like a written one; a **written bound is ENFORCED, tighter than the computed one** | built (lane 191): a probe function with no clause checks clean; `gabbro abgeleitet` prints `effects { pure } [derived]`, `costs <= 3 ops [derived]`; `(written)` marks written lines, `(lower bound)` an omission nothing settles, with the refusing code (`N305`) |
| 2 | **Defaults with a named escape** (after Rust's lifetime elision): a small, fixed, documented set of rules for the rank order, the phase, `pure` on spec functions; every rule has a sentence | **not built** (nothing found in the tree) |
| 3 | **Explicitness as a view**: `gabbro fmt --explicit` writes every settled derived clause out, `--elide` removes every clause equal to what would be derived; same checker, same program — no second language | built (lane 197) |
| 4 | **Refusals that ship the fix**: a machine-applicable edit (like `rustc --fix`) | built (`--fix`, `Fix` in `diag.rs`, lane 187) |
| 5 | **Contextual keywords**: 212 of 221 vocabulary words could serve as no identifier anywhere — pure grammar friction; a word is a keyword only where the grammar expects one | built: `node`, `index`, `next` are identifiers in a probe; the K3 collisions (§11) no longer occur there |
| 6 | **Lean side: better handed-over goals, more tactics** (`gabbro_simp`, `gabbro_wf`); every tactic produces a kernel-checked proof | not re-measured here |

Ceremony (booked, *not re-measured*): `111 von 1559` sites may fall as of 2026-09-13; the count is
corpus-dependent and every lane re-books it "measured, not added up" (measured by the retired `zaehle-zeremonie`; not guarded today; `gabbro zeremonie --table` prints the sites).

---

## 11. Completeness, blind spots, and what a foreign corpus showed

*(Formerly `dokumente/PRUEFER.md` and the `messung/` reports `GRAMMATIK-VOLLSTAENDIG`,
`K3-BEFUND`, `RUMPFKANAL-LUECKEN`, `AUSSETZUNG`, `VIER-LUECKEN`, `EINHEITENSICHT`,
`TORREICHWEITE`.)*

**The question** "can one write any Gabbro program and have it lower to C/LLVM with no plumbing
left for the user?" falls into two: **V** (completeness: does the *generator* know every form the
checker accepts?) and **K** (plumbing: after lowering, is a duty left on the person that is not
their logic? = `H`, §9). V can be complete while K is open (a generator that knows every form
and has proved none has met V and not K); not the other way round.

**Why a corpus count does not answer V.** The corpus was written by people with the language
documents beside them, so "N of M corpus programs lower" measures the selection. The instruments
that replace it:

| Instrument (the `retired` rows are not guarded today) | What it counts |
|---|---|
| `gabbro blindstellen <clean>… -- <poison>…` | **FORM × POSITION** over a corpus and the *empty* cells; a cell with 0 sites is *unreachable*, not "checked"; a cell only the poison corpus occupies is booked separately |
| retired `pruefe-grammatiktafel` | **FORM × RESPONSIBILITY** from the **grammar** (not a corpus); `UNGEDECKT` had to be empty. "Lowered" is a statement about the word, not about every position the grammar allows it in (a *quantifier* domain lowers; the same word as a *traversal* domain is refused by name — four measured refusals would have vanished behind one green cell) |
| retired `pruefe-reichweite` | the second class of zero: a body no pass **reads** |
| retired `pruefe-abstieg` | does every pass descend into every statement kind that carries a sub-block ("touching is not checking", `W13`) |
| retired `pruefe-konstrukte`, retired `pruefe-klauseln` | a construct without a generator; a clause *declared, carried, never read* — 48 sites found where four were expected |
| retired `zaehle-absagen` | the **emitter's** refusal forms (`C001` has ONE site, `fn weigere`; what counts is its callers) and per form its state |

**The generator side (2026-08-30; not re-measured):** of the valid corpus programs (checker: 0
errors) all but two lowered; the refusals were named. Of the programs with checker errors nearly
all were *intentional* (probes) and three were real code — and none of the three turned out to be
a checker defect (`F01`: a fallible call not in `let … else`, the price of "no `?`"; `F03`:
undeclared names of an excerpt; `F09`: the sharp `Rumpf × Knotenlänge^Ebenen` calculus whose
*promise* was wrong, blocked three times by the **generator**, not the checker).

**The foreign-code measurement (K3, 2026-09-04): "0 of 8".** Eight fragments cut from Linux
7.2.0-rc7 by a rule written *before* the cut and frozen in a commit before any was run, from an
author line the project never touched: Gabbro handled 0 of 8, against 9 of 10 of the corpus the
project chose. *The ten were measuring our selection.* What it found, and what became of it:

| Finding | What it was | Status |
|---|---|---|
| the vocabulary collides with the kernel: `node`, `old`, `next`, `progress`, `release`, `stack`, `index` are kernel identifiers; `P002` fired in 6 of 8 | a *rate* the tree had no estimate of; and a reader refusal stops the body from parsing, so a body that never parsed declares no names (renaming the seven *raised* the error counts, 4→16 in one file: a measurement that stopped at the first token) | fixed by **contextual keywords** (§10 lever 5); re-measured 2026-10-17 with a probe |
| `u64(x)` was refused although the grammar says it is the conversion | `pathseg` was widened to admit `u8 … u64` for `u64::max`, the call head was not | fixed; re-measured: `return u64(a);` checks clean |
| a user-defined address space was unequal to itself (`ptr<user, r>` gave `R008`) | `Raum::Benannt(Ident)` derives `PartialEq` over `{text, span}` | fixed; re-measured: the probe checks clean |
| 0 of 8 for foreign C | measures *portability*, not fitness: intrusive lists, `void *`, `container_of` are refused on purpose | recorded; a corpus written for Gabbro is the other question |

**Language gaps found by real code** are carried in `FRAGMENTE.md`. What the completeness work
closed or named:

* **Forms that mean nothing** (`GRAMMATIK-VOLLSTAENDIG`): the quantifier domain was decoration
  (closed: `D017`–`D025`, §4.3); a fractional bound on an integer type (`M146`, closed at
  nineteen positions); `divergent … -> never` that returns (`S009`, closed). The binder of a
  quantifier now has a type in the four domains that bind a slot index (closed 2026-09-08; payoff
  in the corpus: zero sites — "a gap can be real, be closed, and move no number"). `threads` as a
  domain is closed *as a question*: the obvious surface would be a synonym (a quantifier domain
  in the model **is** an integer), so only the checker half was built (`D024`).
* **`leave`/`next` versus `breaking`** (`AUSSETZUNG`): *a suspension is not an exit* — `leave`
  changes WHICH statements run, `breaking` changes WHICH DUTY holds in between. The Lean body
  channel carries `breaking` as its body and refuses a body with a real `leave`; the name stays in
  the datum so an invariant channel can find where the suspension lay. «B10» (a loop form that
  yields a *value*) is booked, not built.
* **`result` in `ensures`** (`VIER-LUECKEN`): `result` is a *name* bound to the returned value,
  not a new form of `Expr` — what was missing was the binding, and the theorem became stricter
  (a body that falls off the end has no result and the theorem fails on `⊢ False`). `old(x)`
  (a predicate over two states) stays refused in the body channel: measured need was zero.
* **Loop invariants** (`SCHLEIFENINVARIANTE`): reuse `invariant`, one position across the three
  loop forms; counted (kind `S`, §9); `M133` forbids the empty one. It makes an invariant
  *possible*, not *proved*.
* **The unit view** (`EINHEITENSICHT`): `gabbro lean` *concatenated text* into one parse tree (measured 2026-08-31), so
  names resolve across files because both `module` blocks stand in one tree; `gabbro pruefe`
  looped and built one tree per file, so the other file is never in the same `Umgebung` — the
  resolver itself is complete and `use`-aware. `--unit` and `gabbro build` give the checker the
  unit view.
* **What a `check` names, and who reads it** (`TORREICHWEITE`): `measures` names a carrier and the
  measured path must not write it; the 18 gate-probe files that produced C that did not compile
  were repaired, not exempted; `N044`/`N045` hold the verdict and `M135` says a `bool` is no number.
* **Body-channel rules were unguarded** (`RUMPFKANAL-LUECKEN`): three rules of the Lean body
  channel had no probe or mutation: one rule on two arms with a probe on one; a probe that
  carried its name and not its subject; and *an invalid mutation is a shrunk population* (a quota
  over a shrinking denominator reads like coverage).
* **A foreign body's promise is a fact** (the retired `FREMDVERENGUNG` register): an `ensures result <op> number/place`
  on a bodiless `extern fn` narrows the caller's type (`fremdverengung.rs`). Measured on
  2026-08-21: of 109 foreign bodies in the corpus 12 state their duty and **1** narrowed anything
  at the caller (most name no `result`, two already stood in the declared type). The certificate
  counts the *effective* narrowing, not the present clause (measured by the retired `zaehle-fremdverengung`).
* **The checker does in Rust what `M104` forbids**: an `as` that wraps in silence cost two real
  bugs on 2026-09-01; the retired `pruefe-umwandlungen` guarded the class; not guarded today.

---

## 12. The Lean mirror

The checker's verdict is mirrored in Lean in four places that are easy to confuse.

### 12.1 `passlogik/` — the rules as mathematics (written from the specification)

Seven files (`Bereich`, `Kosten`, `Linear`, `Phasen`, `Rang`, `Terminierung`, `Wirkung`), about
3,000 lines, **137 theorems, 0 own `axiom`**, 65 with `#print axioms` in place and 54 "does not
prove" notes (counts from the folder's README; the theorem count re-adds to 137 by `grep`).
**Written from `SPRACHE.md`, not from `crates/`** — the whole value is that the model can
*contradict* the Rust; copying it destroys that. Two reservations: (1) the seam between the model
and `gabbro-check` is checked by nobody; (2) the **statement descent** (what a body does,
statement by statement) stands in none of the seven files and is booked as an assumption in four.
"137 theorems over a model whose load-bearing assumption is unmodelled" — which is why §12.2
exists.

### 12.2 The safety theorem over the sequential core (`programmlogik/Gabbro/Sicherheit*`)

*The question:* does the grammar cover every error except the person's logic? *The answer:* not
as stated — a context-free grammar decides no range, rank or linearity; the checker carries it,
and for the checker there was a classification (`Coverage.lean`) and theorems about its *rules*
but **no theorem about runs**. Now there is one, over the sequential core of `Body.lean`:

```
theorem exec_sicher … :
    pruefeBlock P erg Δ b = some Δ' →      -- the checker (here: its Lean twin) accepts the body
    Welt P.D Γ s.world → WFU Δ s.local' →  -- the state lies in its declarations
    exec ρ b s = .stuck → LogikB ρ b s     -- stuck ⇒ at the person's own clause
```

`LogikB` has two ground constructors — one `requires` at four call shapes, and an `invariant`
failing on entry — and a third source of "logic" cannot be added silently (`logik_grundfaelle`).
Files (current counts): `Sicherheit/Ausdruck.lean` (1,307 lines, 29 theorems; `schluss_sicher`
for expressions: `M102` denominators, `M137`/`M104` bit operators, `M103` indices, `M104` ranges
through `+ − ×`), `Sicherheit/Anweisung.lean` (1,797 lines, 40 theorems; `pruefe_sicher` and the
block form; every store held against the declared shape, every `match` names every case, every
call fits its signature and carries a boolean `requires`, a `let … else` else-block ends in an
exit), `Sicherheit.lean` (the sentence, eight `by decide` speech tests, `#print axioms`).
**Premises are visible at the theorem, never an axiom** (`Deklariert D Γ`, well-formed `via`
fields; the two premises `UmgebungOK`/`SchleifenOK` are **discharged** by
`KompositionBeweis.lean`: `umgebung_ok_of_runs`, `schleifen_ok_of_runsloop`, over a program with a
body table, cycles through `decreases`).

*Six findings the construction produced* (each a place where the specification or the model gave
way): index out of range and width overflow were **not faults of the model** (`World := Place →
Value` is total — "a program that indexes outside does not get stuck in this model, it reads"; the
two classes were carried only as properties of the checker); `Shape.opt` carries no range; the
`let … else` else block must end and the model did not demand it; a `reason` has no `Shape`;
division/remainder/bit results come out as `.int` without a range while `typen.rs` computes
bounds; and **the seam**: `schluss`/`pruefe` are a checker this file wrote from the specification,
not `gabbro-check`. S3 (make the two silent classes faults) is *threaded* in
`grammatik/Grammatik/Kern/Syntax/Fehler.lean` (`evalF`, fault outcome through parallel
execution); the `Body.lean` side stays coordinated with `OFFEN O1`.

**Outside the theorem and not reachable by proving harder:** alias (places are `DecidableEq`:
"that IS the alias freedom" — see §5), memory model, termination (necessary conditions only), the
axiom layer, foreign bodies, the emitter and the C, the checker implementation, liveness. The
sentence a finished proof would carry reads: *plumbing-safe by `exec_sicher` under the named
premises; memory-safe under the assumptions; alias: for a pointer pair at a call `R014`/`R015`
(§5), otherwise not carried; race-free under the memory-model assumptions; terminating: necessary
conditions; functionally open on the person's obligations.* The retired guardian
`pruefe-sicherheit` (2026-10-17) checked (eight speech tests present, no `sorry` *term*, build green,
`#print axioms` ⊆ `propext, Classical.choice, Quot.sound`, a finding ratchet that may fall).

### 12.3 The G exporter and the goal Bool

`gabbro lean-g` (`lean_g.rs`) exports a checked unit as a `Programm D` term (declaration, bodies,
contracts, the two decidable checks as `by decide`); a form with no G counterpart is **refused by
name** (`LG001`–`LG007`), never dropped. `gabbro obligations --g` adds the flagship's
per-function duties (`KoerperGutS`, `InvGutS` over the lock-invariant family). The decidable
component Bools of the goal theorem's checker are in
`grammatik/Grammatik/Zielsatz/Kern/Akzeptiert.lean` (`Akzeptiert`, proved to *decide exactly*
`AkzeptiertSpec`, `akzeptiert_iff`): `frag`, `abg`, `fuss`, `stufen`, `sperrOrte`, `wurzeln`,
`einzeln`, `renn`, `antworten`, `masken` — each the Lean twin of a rule named in §4 (`fuss` ↔
`N290`–`N294`, `renn` ↔ `N300`–`N304`/`H013`, `masken` ↔ `H102`, `antworten` ↔ `N310`–`N314`,
`wurzeln` ↔ `N302`/`N303`, `einzeln` ↔ pool safety). The atomic rely is carried by
`AkzeptiertSpecX` (the footprint rule admits a shared atomic in no contract: `N484`). **The goal
statement is `theorem gabbro_ziel`** (`Zielsatz/BeweisAtomar.lean`; `Zielsatz/Kern/Beweis.lean`
proves `gabbro_ziel_sc`); `#print axioms` must be exactly `propext`, `Classical.choice`,
`Quot.sound`. What the goal theorem claims is documented in `BEWEIS.md` and `SATZKARTE.md`; this
document owns only the rule ↔ Bool correspondence above.

### 12.4 The seam: witness pairs, not a proof

`lean::witness` (and `crates/gabbro-check/tests/seam.rs`) writes the unit's seam module: one
`theorem checker_agrees_<routine>` per carried routine, `pruefeBlock P erg [] ⟨body⟩` checked by
`decide`, filled from the declarations. A unit the Rust checker accepts and the Lean twin refuses
(or the reverse) then fails loudly at `lake build`. It measures that the two checkers *agree on
the corpus*, not that they are the same function. The first run (2026-09-10) found ten findings —
the largest: `schluss` index needs `IntIn` while `index into` parameters carry `.int` (34
instances); no flow-sensitive narrowing in the Lean twin (11); one reverse finding, an `M101` gap
found through a poison program. Of 189 routines, 119 were witnessed: 53 both-accept, 66
Rust-only, 0 Lean-only. *(Counts are of that day.)*

### 12.5 The four named exceptions of GabbroV

GabbroV (`programmlogik/gabbrov`, `GABBROV.md`) decides the obligations it treats as *passed* or
*refuted* instead of *undecided*; the claim is "all of them, except the **structurally**
undecidable — and those stand by name, not as a percentage". Structural means a property of the
semantics or of the statement, not of the solver or the day ("the solver does not get through" is
*undecided*, a per-run outcome). The list:

| # | Obligation | Why structural |
|---|---|---|
| 1 | **L24** — `caller` and `reply_owner` written in one step | quantifies over a state **between** pre and post; `Body.lean`'s `exec` is big-step and has no intermediate state |
| 2 | **L34** — the invariant does *not* hold between the two assignments | the same object from the opposite side: it says one exists and what fails in it |
| 3 | **L50** — `Flush` completed **before** the reply | an ordering between two effects of one big step |
| 4 | **L52** — `Stop`: the reply still goes **before** the service ends | same as L50 (`flush ∧ reply` would read right, be strictly weaker, and carry the name) |

*Four rows, one cause — one missing means seen four times* (a small-step or trace semantics would
close it, a much larger decision than widening a fragment). A row says "GabbroV's fragment cannot
decide it", **not** "no semantics of Gabbro can state it": the goal theorem's machine G is
small-step with a per-thread call log, and there L50/L52 are the leg `folge`, L24's observational
content the legs `invSicht`/`sperrSicht`/`sperrWechsel`, L34 an existence statement with a witness
(`OFFEN O1`). The rows are the *centre* of the case for GabbroV: `D013` checks only that the
invariant exists, not that the block restores it, and the statement that site needs is L34. The
count is unguarded: the guardian `pruefe-ausnahmen` named in the old text never existed (§15).

---

## 13. Evidence apparatus and how to re-measure

### 13.1 What a claim about the checker rests on

| Evidence | Where | What it says |
|---|---|---|
| **clean corpus** | `beispiele/*.gab` (170 programs, numbered; real, checked, most also emitted and run) | each must pass the checker with 0 errors (`jedes_beispiel_geht_sauber_durch`) |
| **poison corpus** | `beispiele/gift/*.gab` (898 files) — the first line is `// erwartet: CODE` | each must fall **with that code** (`jedes_gift_faellt_mit_seinem_code`). The test asks `contains`, not `==`: a probe is green once its code stands *anywhere* in the list. the retired `zaehle-gifttreffer` asked the stricter question — does the expected code fall **alone** (not guarded today) |
| **both directions** | `der_korpus_hat_beide_richtungen`; `keine_zwei_korpusdateien_teilen_eine_nummer` | a rule has a positive and a poison side; example/gift numbers are unique |
| **frozen excerpts and probes** | `messung/fragmente/F01`–`F10`, `messung/k3-fragmente/`, `messung/proben/`, `messung/einheit-proben/`, `messung/*-proben/` (265 `.gab` under `messung/`) | the kernel fragments the language was designed against; the K3 foreign fragments; one-purpose probes cited by sentences |
| **unit tests** | `crates/gabbro-check/tests/*.rs` (about 60 files; with `gabbro-cli/tests` ~1,250 `#[test]`), `crates/gabbro-cli/tests/*.rs`, in-source tests (~260) | `rechenwerk.rs` (arithmetic and range cases), `paesse.rs` (per-pass cases), `beispiele.rs`, `seam.rs`, `noalias.rs`, `wurzeln.rs`, … (`grep -c '#\[test\]'`, 2026-10-17) |
| **mutations** | measured by the retired `mutiere-pruefer` (2026-10-17, see git history; **not guarded today**; historical: **388** mutations, ~13 min 20 s locally) | a poison probe measures that a rule *fires*; a mutation measures that a rule *is the thing that fires*: each mutation edits the checker's source and the test suite must catch it. The booked catch rate is 375 of 376 valid mutations; the one survivor fell at the retired `pruefe-emission` stage 9 (legacy C check) instead — "375 of 376 is a statement about `cargo test`, not about the tree" |
| **sentences** | §8 | the register says which of the above measures which rule |
| **the register's blind-spot instruments** | §11 | what *nobody wrote* and what *no pass reads* |

*Last run of the retired mutation guardian, 2026-10-17 (in a worktree, not on a clean tree):* its
anchor mode reported 34 mutations that "measure NOTHING" (anchors missing or ambiguous, e.g.
`let-else-ueber-place-verliert-den-typ`, `bau-glaubt-das-erzeugnis`); the booked figure was 386 of
413 anchors at 2026-09-14. Not re-measured; the guardian is retired and mutation testing of the
checker is **not guarded today**.

### 13.2 Commands

```bash
# the checker itself
gabbro pruefe <file.gab>…            gabbro paesse [--je-satz]          gabbro pflichten <file.gab>
gabbro abgeleitet <file.gab>…        gabbro zeremonie --table           gabbro blindstellen <clean>… -- <poison>…
gabbro kontexte|alias|k-bedingung|annahmen|schablonen [--gate]|zeugnis <file>…

# the four guardians (since 2026-10-17 the whole set), each prints its numbers and its own speech test
./instrumente/pruefe-pruefer.py           # the checker: cargo test --workspace (poison corpus, clean corpus, tables),
                                          #   sentence ratchet (teile/saetze.py), one code one place (teile/kennungen.py)
./instrumente/pruefe-lean.py              # the Lean model: lake build, gabbro_ziel axioms, no sorry/axiom, layout
./instrumente/pruefe-llvm.py              # the LLVM compiler: cargo test --test llvm, model coverage, end to end on x86_64 and aarch64
./instrumente/pruefe-gabbrov.py           # GabbroV: lake build programmlogik, no sorry, gabbro prove over the proof units
./instrumente/abnahme.py                  # all four together
cargo test --no-fail-fast                                        # one run at a time; free -g beside it
```

`abnahme.py` runs the four guardians and names a verdict per guardian. *A guardian that aborts
reads like one that passed — look for the numbers it no longer prints.* The roughly eighty
further guardians, counters, ratchets and the mutation run (`mutiere-pruefer`, 388 mutations)
were retired on 2026-10-17 (see git history, `git show 414feafc:instrumente/<name>`); what they
measured is **not guarded today** unless a `gabbro` subcommand or `cargo test` covers it.

### 13.3 Rules of measuring (the ones that recur in code comments)

* **A figure names the command that recomputes it** (`W7`); the retired `pruefe-zahlen` held each booked
  figure against its command (2026-10-17; not guarded today). A figure carried forward without re-measuring is a forgotten one:
  recompute, do not increment.
* **Run the unchanged checker on the template before building** (`W24`): a sweep over templates
  that do not parse measures the parse error, not the question.
* **Put the counter-probe in front of the first measurement line** (the same apparatus, over cases
  where the answer is known), so an apparatus that finds nothing is not mistaken for a result;
  read **both** streams.
* **A measurement that stops at the first hit measures the wrong question** — count, do not
  abort (`cargo test --no-fail-fast`; `panic!` instrumentation hides every later hit — use
  `eprintln!`).
* **A number proves its denominator, not its label** (`W25`): "no refusal about the name" was
  booked on a code that fires for an unrelated reason.
* **A scanner gone blind prints the same ALL PASS as a clean tree** (`W17`): every guardian carries
  a speech test in both directions, and an empty subject is a refusal, never a pass.
* **Touching is not checking** (`W13`): a pass that mentions a statement kind does not necessarily
  descend into it.
* **Two tools in one tree measure a mixture** (`W16`): `cargo test` and the Lean corpus run must
  not run in one tree at once; a mutation run and a `rsync` into it collide; a mixture of old and
  new files under `cargo` (mtime) misleads.
* **An incomplete call hull never produces a refusal that needs completeness** (`R16`); checks
  that only demand more from the caller stay sound over a lower bound.
* **No construct without measured need** (Regel A): a language addition is bought by a count of
  sites in real code, or by a refusal that would otherwise be silent.

### 13.4 Machine-read documents (retired)

Until 2026-10-17 several guardians parsed prose and tables in the documents this one replaces
(the `SONDENDECKUNG`, `UNFALSIFIZIERBAR` and `PFLICHTEN` register tables, `PLAN.md` table cells).
Those guardians and registers were retired (see git history); **no guardian reads these documents
any more**, and a document may change without retargeting a pattern. What the four guardians
(`instrumente/pruefe-pruefer.py`, `-lean.py`, `-llvm.py`, `-gabbrov.py`, run by `abnahme.py`) read
is stated in their own docstrings.

---

## 14. State, and what is open

### 14.1 State (2026-10-17)

| Fact | Value | Command |
|---|---|---|
| passes in the register | 12 (3 built, 9 carried, 0 partly built, 0 open) | `gabbro paesse` |
| sentences | 216 (208 measured, 2 argued, 6 conjectured, 0 proved) | `gabbro paesse` |
| codes claimed by a sentence | 443 (about 500 code-shaped literals in the crates) | `gabbro paesse` |
| next free diagnostic code | `N587` | `grep -rhoE '\bN[0-9]{3}\b' crates \| sort -u \| tail` |
| clean examples / gift probes | 170 / 898 (highest numbers: example 1163, gift 1444) | `ls beispiele beispiele/gift` |
| `unfalsifiable` clauses | 8, 1 admitted (measured 2026-10-17 by the retired `pruefe-unfalsifizierbar`; not guarded today) | `grep -rn unfalsifiable beispiele` |
| hanging plumbing duties `H` | 1 (`F3` lowering without a differential test; measured by the retired `zaehle-pflichten`, 2026-10-17; not guarded today) | — |
| obligations over the ten fragments | 239 = 173 K + 66 L (historical: retired `zaehle-pflichten`, booked 2026-09) | `gabbro pflichten <file.gab>` per file |
| the goal theorem | proved over the model; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` (booked, not re-run here: no Lean build was run for this document) | `BEWEIS.md`, `SATZKARTE.md` |
| the checker as a *proved* artefact | not: the Rust checker is related to the Lean Bool by witnesses (§12.4), not by theorem | — |

### 14.2 Open items of the checker and its mirror

IDs are the stable `OFFEN Oxx` ids; the text they refer to is `TODO.md`. **Status words are the
state in the tree on 2026-10-17, where it differs from `TODO.md`, the difference is named.**

| Id | What | Where |
|---|---|---|
| **O1** (rest) | the *name* of `breaking` in the G remainder, the block-restoration duty in the goal's leg (b), axiom/register events in the call log, path-sensitive end | goal theorem; §12.5 |
| **O4, O5, O6** | `cdt_wohlgeformt` at a free slot waits on sibling consistency (indexing *through* an option); the unsat direction of the rank witness | Lean obligations |
| **O11** | an invariant that no function maintains. **Partly built since the entry was written:** an *online* `table`/`group` invariant must be named by some `maintains` or its table must have `ops` (`N583`); an *offline* one is audit-time and exempt. Offline invariants are exempt by design (audit-time) | `kbedingung.rs`; `TODO.md` says "booked by NOTHING" (stale) |
| **O14** | arena chains: two statement shapes have no G form (`free`) | §4.14, `LG005` |
| **O19** (rest) | handlers and cores: `Einheit` names no handler, G has no cores (`kern`, `H`, call graphs and the mask discipline are hypotheses of the leg); re-entry and handler-on-handler are outside. **`H102` fires on any `via` word since the widening**, not only on `via idt` as `TODO.md` still says | §4.10 |
| **O20** | arenas under concurrency: generations and the commit ceiling assume one control thread and once-entered roots | `N521`, `N522` |
| **O21** | `child` has no model: its code between the gate call and the region is unchecked *for the child* | §4.13 |
| **O23** | gate preconditions (NUL path, frame length) are named, not modelled | `N463`, `N464`, `N506`, `N507` |
| **O24** | strings are checked, not represented (NUL, `max` ceiling, aggregates) | §4.4 |
| **O25** | closed in `TODO.md`'s appendix (the rely *is* the goal); the LLVM section still lists "`publish` with payload (11 sites), `OFFEN O25`" — an inconsistency inside `TODO.md` | goal theorem |
| **O26** (rest) | foreign lock primitives are assumed (own ones are checked: `N481`–`N483`) | §4.10 |
| **O27** | source forms without a complete G export: float, byte-pointer/string, dynamic-arena forms; coverage is the Lean constructor/field register (`instrumente/teile/llvm-modelldeckung.py`, run by `pruefe-llvm.py`), **not counts of examples** | `lean_g.rs`; `dokumente/LLVM-BACKEND.md` |
| **O28** (rest) | link: no independent review of the spec diff, no semantic equivalence of contracts, no certificate for linked programs | §4.15 |
| **O37** | regions in G: no byte pointers in the model; nothing releases a region; Gabbro bodies do not pass an extent on | §4.13 |
| **O40** (rest) | emitter names: the checker half is built (`N042`); module-qualified names are missing in both emitters | §4.2 |
| **Alias** | decision pending in `TODO.md`; `R014`/`R015`/`noalias` are built, the explicit-`own`-at-the-boundary question is recorded, not decided | §5 |

**Closed or retired** (appendix of `TODO.md`): O2 (withdrawn), O3, O7, O8, O9, O13, O18, O25, O31,
O34–O36, O38 built; O12 single program; O15/O16 priced and **rejected** (no corpus use);
O29 out of scope; O30 superseded (Rust backend + Lean validator, not self-hosting); O10, O32,
O33, O39 not checker subjects.

**Open, checker-internal** (not carrying an `Oxx`):

* **Passes share no `Umgebung`/call graph** (§1): the old measurement put 610 of 672 ms of
  pass time into rebuilding two structures; not re-measured.
* **V2, V3** conjectured (§4.4); **`m3.barriere`**, **`m2.geisterloeschung`**, **`gruppe.invariante`**,
  **`emitter.reissstelle`** conjectured (§8); the two *argued* sentences are arguments, not
  theorems.
* **Quantifier domains:** the path base of `fields of`, the `member` form, the *typed* extent of a
  place (`d.domaenenort`); `queue` and `elems of` emit byte-identical C; `threads` binds a variable
  no declaration supports (`D024`).
* **Fallibility asymmetry** `N028`/`N029` (full path vs short name); `m1.fnzeiger`: the declared
  *range* of a number at a `fn(…)` slot is not compared (contravariance — a callee that accepts
  *less* than the slot promises passes); disequality at a range boundary does not narrow
  (`if n == 0 { return 0; }` then `n - 1` still reports `M104`).
* **Defaults with a named escape** (§10 lever 2) are not built; **`own` at the boundary** (§5).
* **Template ceiling** (§8.2): 41 entries, 48 admissible; each further one costs a proof; the
  `designed` entries (`consuming.umhaengen`, `transition.transset`, `exchange.rmw`, `walk.mappings`,
  `entry.abdruck`, `ops.suche`, `state.reset`) are the debt.
* **Probe coverage `A_p`:** the guardian does not run until its path is fixed (§15); the booked
  value is the last measurement, 18 of 51.

---

## 15. Findings of this consolidation (2026-10-17) — for the next owner

Measured while writing this document; none of them was repaired here (the scope was
documentation). Each is checkable by the command given.

1. **`A_p` was unguarded** when `pruefe-sondendeckung` aborted on the moved probe directory
   (`instrumente/sonden/`, commit `6744cf30`); the guardian was retired on 2026-10-17 (see git history).
2. **The count of the four GabbroV exception rows is unguarded:** the guardian `pruefe-ausnahmen`
   named for it never existed, and the retired `pruefe-waechter` mentioned it only in a comment.
3. **`gabbro annahmen beispiele/*.gab` aborts** with *"`linux_write_contract` is declared twice with
   different content — a contradiction in the assumption set"*: six examples at the top level
   (`74`, `90`, `96`, `149`, `163`, `182`) declare an assumption of that name with different
   statements. The retired `pruefe-zahlen` (2026-10-17) read exactly this command for the figure `A`.
4. **`AGENTS.md` §7 counters lag the tree:** `beispiele/gift/1444-…` and `beispiele/1161`–`1163`
   exist, so the next free numbers are gift **1445** and example **1164** (the row says 1444 and
   1162). `N587` is correct.
5. **Booked figures lagged `gabbro paesse`:** the retired `KENNZAHLEN` register held *198 sentences, 190
   measured, 419 codes*; the binary says **216, 208, 443**. The retired `PASSREGISTER` register carried the
   headline "56 sentences over twelve passes". The pass-register figures are re-booked from this
   document's §8.
6. **German diagnostic text in the checker:** `N584` and `N585` (`arena.rs`) are written in
   German (`… fragt … nach freiem Speicher, und das nennt kein Tor …`); the working language of diagnostics is English.
7. **The retired `pruefe-kennungen` reported 3 doubly-issued codes:** `N004`/`N005` (`namen.rs` +
   `zielbindung.rs`, the same rule re-applied per `target` binding, so deliberate) and `Y103`
   (`llvm.rs` + `llvm/memory.rs`). That guardian counted a deliberate reuse like an accident.
8. **`TODO.md` lags the tree in four places** (§14.2): `H102`'s `via idt` limit (widened), `O11`
   "booked by NOTHING" (`N583`), the alias decision (slices 1–4 built), `O25` listed as both
   closed and open.
9. **`A1-OWN-PAPER.md` §6 "Finding (checker)"** (an untraced name gives no root) was *repaired*
   on 2026-10-17 (`a6a2e2d6`); the paragraph still reads as open.
10. **Sentence reservations that predate later work:** `v2.relationale-verengung` ("no alias
    analysis anywhere in this checker"), `m3.zeigerrecht` ("only the BASE NAME"; fine), `m1.fnzeiger`
    (an old struck line is kept in its text).
11. **Measurement context:** the guardians that read `target/debug/gabbro` abort with "binary older
    than N source files" in a worktree whose files are newer than the shared binary. That is an
    apparatus finding, **not** a finding about the tree — build, then re-run.
12. **Not carried over from the old files because it could not be verified today:** the
    synthetic-unit timing table of «Z» (899 ms, 610 ms rebuild), the `.gabi` details beyond the
    sentences (representations of one type across libraries, template proof-state merging), the
    float plan's per-stage status F0–F8 beyond `GLEITKOMMA.md`, the 175/24 occupied/poison-only
    cells of the grammar table (struck in retired `KENNZAHLEN` register on 2026-09-27), the ceremony count after
    2026-09-13, and the K001 off-by-one mutation table of five domains.

---

## Appendix A — where the old section ids went

*A temporary table for rewriting the comments that cite the files this one replaces; delete it
when the last comment is rewritten.* `programmlogik/PLAN.md §3.1/§3.3/§5.2/§9.1/§15` is a
different file (the Lean model's plan) and is **not** covered here.

| Cited as | Now |
|---|---|
| `PLAN.md` PL.1, PL.3 (`lib.rs`, `saetze.rs`, `schablonen.rs`) | §8 ("The three steps of the register") |
| `PLAN.md` K11.1 (b) (`lib.rs`, `phasen.rs`, `kosten.rs`) | §4.1 table row 11, §4.6 (phases) |
| `PLAN.md` «OPT» (`schablonen.rs`) | the `restrict` template is §4.13/C-backend; the checker-side successor is §5 (`noalias`) |
| `PLAN.md` «ABI», «ABI4» (`abi.rs`) | §4.15 |
| `PLAN.md` "the sixth class" (`domaene.rs`, `saetze.rs`) | §8.2 |
| `PLAN.md` "Wozu Gabbro taugen wird" (`ast.rs`, `rechenwerk.rs`) | §8.2 (`comptime`: the line) |
| `PLAN.md` F3 (`m1.rs`) | §8.2 (outward rounding) |
| `PLAN.md` K100.4 way (b) (`zeugnis.rs`) | §8.2 (translation validation) |
| `PLAN.md` "Rennen nicht baubar" (`geteilt.rs`), K11.2.2 | §8.2, §4.10 |
| `PLAN.md` "wertgetragene Schranke" (`kosten.rs`) | §4.12 (parametric promises) |
| `PLAN.md` table cell `L <= 4` (`schablonen.rs`) | §8.2 (ratchet on `L`) |
| `PLAN.md` "Tor" for `gabbro kontexte` (`kontexte.rs`) | §8.2 (an empty run looks like a pass) |
| `dokumente/PRUEFER.md` §0b / §0c (+ points 2, 3, 5) / §2 / §3 / §6 | §6.2 / §6.3 / §6.4 / §6.5 / §6.7 |
| `dokumente/PRUEFER.md` §2, levers 1, 3, 4 | §10 ("What cannot be made lighter", levers 1, 3, 4) |
| `dokumente/PRUEFER.md` §4 (S4 seam witnesses) | §12.4 |
| `dokumente/PRUEFER.md` §2 | §11 ("Why a corpus count does not answer V") |
| retired `PFLICHTEN` register F10, F1 rows | §9 (rows that rules cite) |
| `PFLICHTEN-KORRESPONDENZ.md`, `PFLICHTEN-ORDNUNG.md` (cited from `pflichten.rs`) | not covered: those files are not in the consolidated set; §9 is the overview |
| retired `UNFALSIFIZIERBAR` register (`saetze.rs`) | §7.2 |
| retired `SONDENDECKUNG` register, `dokumente/PRUEFER.md` (guardians) | §7.3, §12.5 — and §13.4: the guardians read the old files |
| `dokumente/PRUEFER.md` §5, `dokumente/PRUEFER.md` §2c, `dokumente/PRUEFER.md` §7 | §4.3 (the three bullets under "What the measurements found") |
| `dokumente/PRUEFER.md` §3, §4.1, §4.2 | §11 (the K3 table) |
| `dokumente/PRUEFER.md` §1.1–§1.3, §2.3, §2.4 | §11 ("Forms that mean nothing"), §4.3 (`D017`–`D025`) |
| `dokumente/PRUEFER.md` §3, §4 | §4.7, §11 |
| `dokumente/PRUEFER.md` §3–§5 | §4.2 (`N041`/`N042`) |
| `dokumente/PRUEFER.md`, `dokumente/PRUEFER.md`, `dokumente/PRUEFER.md`, retired `FREMDVERENGUNG` register, `dokumente/PRUEFER.md`, `dokumente/PRUEFER.md`, `dokumente/PRUEFER.md`, `dokumente/PRUEFER.md`, `dokumente/PRUEFER.md` | §11; §4.3 (K001); §4.13 (`absenkung.rs` bound 18; the measured maximum was 17, the bound 18 = 17 + 1); `ERSTNAMEN` (English first names of the CLI sub-commands and flags, guarded by `crates/gabbro-cli/tests/fahnen.rs`) is a CLI fact, not covered |
