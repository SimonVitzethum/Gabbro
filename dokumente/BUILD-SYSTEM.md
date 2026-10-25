# The build system: `gabbro.build`, after Meson

*Rewritten 2026-10-25: the line-oriented `.bau` manifest is replaced by a project file and build directories after
Meson. Code: `crates/gabbro-cli/src/bau/` (`sprache.rs` the build language, `einheit.rs` one unit through LLVM,
`mod.rs` the commands). Tests: `crates/gabbro-cli/tests/{bausystem,onramp}.rs`.*

```
gabbro setup build                         configure build/ from ./gabbro.build
gabbro setup build-arm . -Dtarget=aarch64  a second configuration, a second directory
gabbro compile -C build [<target>…]        build every target, or the ones named
gabbro test -C build [<test>…]             build what the tests need, then run them
gabbro install -C build                    build, then copy `install: true` programs
gabbro configure -C build [-D<n>=<v>]…     print the options, or change them
gabbro introspect -C build                 the evaluated project as JSON
gabbro build [<dir|file>] [-D<n>=<v>]…     setup build/ if needed, then compile -C build
```

Each unit goes

```
checker  ->  LLVM IR  ->  opt -O3  ->  llc -O3  ->  <name>.o  ->  ld.lld -static -e _start
```

with `opt`, `llc` and `ld.lld` found on `PATH` (a missing tool is a refusal that names it). There is no `cc`, no
libc and no startup file: the entry `_start` is written by the generator around `pub fn main`, and every
operating-system call is a `syscall` item of the program itself.

## 1. What is taken from Meson, and what is not

**Taken:** one declarative project file per directory (`gabbro.build`, with `subdir`), project options in a file of
their own (`gabbro.options`), out-of-tree build directories where ONE directory is ONE configuration, `-D` to set an
option at `setup` or `configure`, tests declared next to the targets, `install` with `prefix`/`bindir` and
`DESTDIR`, and an introspection command.

**Not taken, for reasons in the language:**

| Not in the project file | Why | Where it stands |
|---|---|---|
| dependency lists between targets of one project | edges are COMPUTED from `module`/`use`; a second list over the same thing would drift (W7). `dependencies:` names other PROJECTS a target may draw from (§7.3); which files enter is still computed | the sources |
| compiler flags, defines | `arch`, `when TESTBUILD`, effects and costs are language | the sources |
| custom commands, generators | a build that runs arbitrary programs checks nothing it runs | -- |
| C sources | this build compiles no C | -- |
| a backend file (`build.ninja`) | the build runs in-process, incremental by content (§4) | -- |

## 2. The build language

Values: strings `'…'` (escapes `\n \t \\ \'`), integers, `true`/`false`, lists `[…]`, target handles. `#` starts a
comment. Statements: `x = e`, `x += e`, a call, `if`/`elif`/`else`/`endif`, `foreach x : list`/`endforeach`.
Operators: `+` (strings, integers, lists), `==`, `!=`, `in`, `not in`, `and`, `or`, `not`, `list[i]`.

| Function | Meaning |
|---|---|
| `project('name', version: '…')` | the first call of the root file, once |
| `program('name', <sources>…, install: false, dependencies: [])` | links to `<builddir>/name`; must carry `pub fn main`; `dependencies:` the projects it may draw from (also on `library` and `object`) |
| `library('name', <sources>…, export: false)` | a SOURCE library (§3); checked alone; must not carry `main`; `export: true` lets dependents `use` it |
| `dependency('name', path: '…', version: '…', options: ['k=v'])` | another Gabbro project (§7.3): from `path:` or `subprojects/<name>/`; returns a handle for `dependencies:` |
| `object('name', <sources>…)` | stops at `<builddir>/name.o`; must not carry `main` |
| `test('name', <program>, args: […], stdout: '…', exit: 0, timeout: 30)` | run by `gabbro test` |
| `files('a.gab', …)` | paths relative to the current build file (a bare string is too) |
| `subdir('dir')` | evaluates `dir/gabbro.build` in the same scope |
| `get_option('name')` | an option's value |
| `message(…)`, `warning(…)`, `error(…)` | `error` stops the evaluation |

`gabbro.options` holds only `option('name', type: 'boolean'|'string'|'integer'|'combo', value: …, choices: […],
description: '…')`. Built-in options: `target` (`x86_64`|`aarch64`), `buildtype` (`shipping`|`testbuild`; `testbuild`
opens `when TESTBUILD`), `prefix` (`/usr/local`), `bindir` (`bin`). **Every refusal names its file and line**, an
unknown keyword argument or function by name; a refused `-D` value never reaches the build directory.

```
# gabbro.build
project('store', version: '1.0')

library('store', 'store.gab')                       # declares `module store`
app = program('app', 'app.gab', install: true)      # `use store::…` -- the edge is computed
if get_option('buildtype') == 'testbuild'
  test('app-runs', app, stdout: 'ok\n')
endif
```

## 3. Units, libraries and computed edges

A **unit** is the set of files one translation sees: a program's or object's own files plus the files of every
library its `use` lines reach, transitively. A library's module must be unique among the project's libraries; two
targets that end in one unit must not declare the same module. **A program or object whose modules another target
uses is refused by name** ("make it a library"): separate compilation across units is not implemented in the LLVM
backend (the generator defines every item a `.gabi` preamble declares, so a second unit would define statics twice).
A library is therefore a source library -- its code reaches a binary only inside the units that use it -- and it is
also checked ALONE, so an error in it names the library before its users fall with it.

## 4. Incremental by CONTENT, never by timestamp

The fingerprint is FNV-1a over the unit's file names and bytes, the target, the build type and the target kind. A
`touch` does not rebuild; a deleted artefact with a valid record does -- *the artefact's presence is checked, not
believed.* The record is written last. The project file is evaluated again at every run, so an edit needs no
reconfigure step; the options are fixed in `<builddir>/gabbro-setup.txt` and changed only by `configure`.

## 5. What a run reports

`built`, `current` or `REFUSED <target>: <reason>` per target, then the coverage line: how many `.gab` files the
project names and how many below its root it does NOT look at -- "nothing found" and "nothing looked at" look the
same otherwise. `--dry-run` prints the plan with each unit's computed libraries. `gabbro test` exits `2` when a test
could not run (no test declared, or an `aarch64` binary on a machine without `qemu-aarch64`): not run is not a pass.

## 6. What is refused, by name

| Refused | Why |
|---|---|
| a source that is not a `.gab` file | this build compiles no C |
| `deps:` or any other unknown keyword, an unknown function | the edges are computed (§1); the language is closed |
| a dependency: missing project, other name, version outside the requirement, unknown option, a built-in option set for it, a cycle of projects, one version from two sources or with two option sets | §7.3; each names the `dependency(...)` line |
| a `use` into a dependency the target does not declare, a declared dependency no `use` reaches, a dependency's library it does not export | each with the fix |
| in a unit of several projects: an item outside a module, a module named like a dependency, a path into a project not declared | the name spaces (§7.6) |
| `compile` after a dependency changed | `gabbro.lock` (§7.3); `configure` accepts the change |
| an empty target, two targets or tests of one name | an empty target builds nothing and says it built; artefacts would overwrite one another |
| a module declared by two libraries, or twice in one unit | a `use` edge would have two targets |
| a program using an object's or program's module | no separate compilation across units (§3) |
| a `program` without `pub fn main`, a `library`/`object` with one | the entry rule, checked on the IR before any tool runs |
| `setup` over an existing build directory | a build directory is one configuration; `configure` changes it |

## 7. Plan: linking Gabbro projects with dependencies (2026-10-25, for review)

*Status: implemented in the build (2026-10-25, `bau/abh.rs`, `bau/namensraum.rs`, tests in `tests/bausystem.rs`)
except the open points of §7.11; the Lean side is §7.5-§7.10. Set by Simon: two or more Gabbro projects, the source of each present, each with
its own `gabbro.build`, dependencies between them. **Everything crosses the boundary, every guarantee is kept, and
the result is as usable as possible**: whatever works inside one project works across projects, and nothing that
could be allowed is refused. Out of scope: a dependency available only as a binary; dynamic loading.*

### 7.1 What must cross the boundary -- the requirement list

Every row is something a program can do inside ONE project today. Each must work across projects, with the same
guarantee, in both directions (dependent → dependency and back).

| Crosses the boundary | Guarantee that must hold across it |
|---|---|
| calls, in both directions, including callbacks and function pointers into the dependent | contracts (`requires`/`ensures`), effects, costs, call-order leg `folge` |
| exported tables and globals, read and written by the dependent | memory safety, race freedom, lock discipline, table invariants (`invRuhe`/`invSicht`) |
| locks of either project held across a call into the other | no deadlock, no wait cycle (`KeinWarteZyklus`), lock ranks ONE order over all projects |
| shared atomics read and written on both sides | the atomic rely (`GeteiltA`), `schwach`, `rennfrei` over GA |
| arenas and allocations handed across (parameters, results, binding calls) | ownership (`besitz`): no double ownership, no use after release, across projects |
| regions from a provider in one project used in the other | `speicherAdressen`, region extents |
| threads: the dependent starts threads into the dependency, the dependency spawns threads that call back | all thread-machine legs (`spawnSicht`, `joinFrei`, pool safety) |
| interrupt handlers in one project reaching code of the other | `keinKernHalt` (masking across projects) |
| `assume`/`axiom`/`device`/`syscall` of either project | ONE set of hardware assumptions, the union; the parts may DIFFER as long as they do not contradict |
| initial memory and lock families of each project | the union, each project's invariants at its own initializers |
| `when TESTBUILD`, `arch` | the program's one configuration |

### 7.2 The guarantee carrier: the WHOLE program, always

The model has two statements for programs made of parts:

| | Whole program (`GabbroZiel` over ONE `Einheit`) | Separate units + link check (`GabbroZielVerbund`) |
|---|---|---|
| number of parts | any | two |
| shared atomics, ownership, callbacks, differing initializers or assumptions across the boundary | covered (they are just parts of one program) | NOT claimed or refused today |

**So the linked program is ONE unit for the checker and for `GabbroZiel`**, holding the files of every project it
uses. Every row of 7.1 is then covered by the statement as it stands -- not by a new, weaker one. What the project
boundary adds is only the question of REUSE: each project's own proofs (b), its own assumptions (c) and its own start
must compose into the program's, without re-proving a dependency in every program. That is the Lean work of 7.5.
Separate compilation (7.7) is then a speed measure that must give exactly the same guarantees.

### 7.3 What the project files say

```
# store/gabbro.build                         # app/gabbro.build
project('store', version: '1.3.0')           project('app', version: '0.2.0')
library('stock', 'stock.gab',                store = dependency('store', path: '../store',
        export: true)                                           version: '>=1.2, <2')
library('internal', 'helper.gab')            program('app', 'app.gab', install: true,
                                                     dependencies: [store])
```

* `dependency(name, path: …, version: …, options: […])` resolves a project from a local path or from
  `subprojects/<name>/` (as Meson does); no network fetch. `version:` is checked against `project(version:)`.
* A dependency's `export: true` libraries are visible to dependents. Its other libraries are used by its own
  exported code as usual and enter the unit when reached -- they are just not named by the dependent's `use`.
* **Declared and computed** (W7 stays): `dependencies:` says which projects a target may draw from; which files enter
  the unit is computed from `use`, as today. A `use` into an undeclared project is refused with the fix
  ("add `dependencies: [store]`", machine-applicable via `gabbro check --fix`); a declared dependency no `use`
  reaches is refused with the fix to delete it.
* **Options**: each dependency has its own options (`options:` in the call, `-Dstore:trace=true`, `configure`
  lists them). `target` and `buildtype` are the program's and are handed down.
* **Name spaces from the start** (7.6): every module of a dependency is reached as `<project>::<module>`, so two
  projects with `module util` link without a rename.
* **Several versions of one project** in one program are allowed when they are different dependencies of different
  projects: name spaces carry the version (`store@1`, `store@2`), each copy has its own globals. One version reached
  twice resolves to ONE copy (same source fingerprint and options); the same version with different source or options
  is refused (a unit cannot know which one a `use` meant).
* `gabbro.lock` (written by `setup`, checked by `compile`): per dependency the path, version, options and a content
  fingerprint of every file. A changed dependency rebuilds by content; a silent swap is visible.
* Only a CYCLE between projects is refused (a project cannot be configured before itself). Mutual calls between
  projects are not a cycle of projects: they are callbacks through function pointers or a third, shared project.

### 7.4 What the build does

1. Resolve the project graph (paths, versions, options, lock); evaluate each project file in its own scope.
2. Per target: the unit = own files + every library (own, or exported by a declared dependency, and whatever those
   reach) its `use` lines reach, transitively, with project-qualified names.
3. **Check the unit whole** (Rust checker; for certificates the Lean exporter over the same unit). Each exported
   library is ALSO checked alone, so an error names the project it is in.
4. Assumptions: the projects' sets are joined (`manifest::vereinige`); only a real contradiction (same name, same
   machine, different content or precondition) is refused, and it names both projects.
5. Lock ranks: each project declares its ranks relative to its own locks; the build composes them into one order
   using the rank constraints a dependency's interface states for locks held across its calls ("callers may hold
   locks of rank < r"), and the whole-program checker decides deadlock freedom over the composed order.
6. Compile the unit (today: one LLVM unit); link; test (a dependency's tests run with `gabbro test -C build
   store:`); install.
7. `introspect`: per unit which project contributed which files, with versions and options.

### 7.5 The Lean side: reuse without re-proof (before the build accepts dependencies)

Lean first: the build feature is merged only with these theorems, each with a non-degenerate witness -- two projects
where EVERY row of 7.1 crosses the boundary at once (a callback, a shared atomic, an arena handed over, a lock held
across, a thread spawned back, differing but compatible assumptions). Where the statement moves: a reviewed
`Spec.lean` diff.

* **L1 -- composition.** `komponiere : List (Projekt D) → Einheit D`: programs, lock families, initial memory, arenas
  and assumptions as unions over disjoint name spaces; the program project's starts. Disjointness is decided by the
  build (name spaces make it hold by construction). `GabbroZiel` applies to `komponiere ps` unchanged.
* **L2 -- the user's proofs compose, with every rely the program can create.** A project's proof of its own bodies
  must survive any program it is linked into. Two things grow in a bigger program and are made explicit:
  - *shared atomics*: a library proves its bodies against every unguarded atomic it can read (`OffenA`), a superset
    of `GeteiltA` in any composition; `koerperGutSA_mono` carries it into every program;
  - *callbacks*: a body that calls a function pointer or an imported head proves against that head's CONTRACT, which
    the composition holds the actual target to (the existing callee-answer quantification of (b)).
  Theorem: each project's `NutzerTeilA` (own functions, `OffenA`) + the program's start ⇒ `NutzerPflichtA
  (komponiere ps)`. For a library proved only against its own `GeteiltA` (the closed-world form, cheaper to prove),
  GabbroV re-checks exactly the obligations whose rely grew in this program, automatically, and reuses the rest --
  so both styles are usable, and neither weakens anything.
* **L3 -- assumptions compose.** `HardwareAnnahmen O (vereinige Qs)` ⇒ each part's, given no contradiction; the
  Rust `vereinige` gets a Lean Bool twin with a soundness theorem.
* **L4 -- start composes.** `StartPflicht (komponiere ps)` from each part's lock invariants at its own initializers
  (`SperrInvLokal`) and the program's root `requires`.
* **L5 -- lock order composes.** The composed rank order is a strict order whenever each part's is and the stated
  cross-project constraints are acyclic; then `KeinWarteZyklus` holds for the program.
* **L6 -- the statement the build relies on:** `gabbro_ziel_projekte`: (a) acceptance of the composed unit, (b) as
  L2, (c) as L3, (d) the runtime ⇒ `ZielFX` on every reachable machine of the linked program, `besitz` over the arenas
  of ALL projects. Proof: `gabbro_ziel` + L1-L5. No leg new, none dropped, none restricted.

### 7.6 Name spaces (a language change: Lean model first)

`use store::stock::Shelf` (and `store@2::…` when two versions are present) names a dependency's module. Lean parser
(`Parser/`), exporter and `SYNTAX.md` first, then Rust parser and checker. Machine G is untouched (the declaration's
names are opaque); the parser theorems and the exporter's export of qualified names move. Exported heads,
contracts, effects, costs and lock-rank constraints of a dependency are readable as its interface (`gabbro abi
--project`), for the reader and for 7.7.

Lean, done (2026-10-25, `Parser/Namen/Namensraum.lean`, THEOREM-MAP §97): a name of the unit is a pair (copy,
path); a project writes paths from its own root and reaches a dependency through the dependency's LOCAL name as
first segment; resolution keeps today's candidates (enclosing modules, then `use` lines) and accepts only VISIBLE
names (own, and public names of declared dependencies). `aufloeseK_platz`: a path means the same wherever the
project and its dependencies sit (alone or as `store@2` under any program); `aufloese_sichtbar`: nothing reaches an
undeclared copy or a private name; `namen_getrennt`: copies share no name. Decision: versions are NOT written in
the source (`store@2::` was planned): a project declares each dependency once, so its local name is unambiguous;
writing a version would let a project reach a copy it did not declare. The grammar is unchanged (`path` already
reads `store::stock::Shelf`). Rust next: the checker resolves against the visible names of the project, not the
whole unit, and refuses a project whose own top module has the local name of one of its dependencies.

### 7.7 Separate compilation -- the same guarantees, faster

Required, not optional, but ONLY in a form that gives exactly what 7.2 gives:
1. `GabbroZielVerbund` is extended to n units with every leg of `GabbroZiel` and every row of 7.1 (open-world rely
   across the link, `besitz` across the link, callbacks, differing initializers and assumptions, composed lock
   order) -- a reviewed `Spec.lean` diff -- with a theorem that "each unit accepted alone + link check" implies the
   whole-program acceptance. Then a dependency is checked ONCE and its verdict reused by content fingerprint.
2. The LLVM backend emits units with external linkage, every static defined once.
3. Translation validation covers each object and the link step (`PLAN-TRANSLATION-VALIDATION.md`).
Lean, done (2026-10-25, `Zielsatz/Projekte/Verbund.lean`, THEOREM-MAP §99): `gabbro_ziel_verbund_n` for any
number of units, each accepted ALONE, plus the link check `BindeSpec` (decided by `bindeB`, `bindeB_sound`) --
callbacks, shared atomics, ownership across units, differing assumptions and initial memories, one lock order.
It is a new statement beside `GabbroZielProjekte` (its own file, like that one), not a diff of `Spec.lean`; the
two-unit `GabbroZielVerbund` stays as it is. Open: points 2 and 3, and the Rust link check.
Until all three hold, the check results of a dependency are cached by content fingerprint (the check is
deterministic), and the program is compiled as one unit.

### 7.8 Order of work and size (ranges; critical path L2 → L6)

| Step | What | Size |
|---|---|---|
| 1 | name spaces in the Lean front end, then Rust (7.6) | 1-2 weeks |
| 2 | build files: `dependency`, `export:`, `dependencies:`, versions incl. several, options, `gabbro.lock`, `--fix` hints, probes (7.3/7.4) -- dependencies refused `NEEDS LEAN` until step 4 | 3-5 days |
| 3 | Lean L1, L3, L4, L5 with witnesses | 1-2 weeks |
| 4 | Lean L2 (open-world rely, callbacks, n-ary (b)) and L6; `Spec.lean` header, THEOREM-MAP, PROOF; then the build accepts dependencies | 2-3 weeks |
| 5 | GabbroV: per-project certificates reused by fingerprint; automatic re-check of grown rely for closed-world libraries | 1-2 weeks |
| 6 | separate compilation (7.7): Verbund extension, LLVM linkage, TV | after the TV backend |

### 7.9 Status (2026-10-25)

Every Lean step of 7.8 is done (THEOREM-MAP §94-§99): L1-L6, name spaces, the embedding with callbacks, L3's twin
of `vereinige` (`Annahmen.lean`), L4 (`Passend`, `StartTeil`, `startTeil_E`), the n-unit link
(`gabbro_ziel_verbund_n`) and the grown-rely re-check on the model side (`koerperGutSA_wachs`,
`nutzerTeilO_wachs`). Open outside the model: the Rust checker and build files (steps 1-2), GabbroV's reuse of
certificates by fingerprint (step 5, `programmlogik/`), LLVM linkage and translation validation (step 6).

Proved in Lean (THEOREM-MAP §94), all axiom lists standard:
* L1 composition (`komponiere`), L2 composition of (b) under the open-world rely (`nutzerPflichtA_komponiere`), L3
  assumptions as the conjunction of the projects' ensures (`qAlle`), L6 the statement `gabbro_ziel_projekte` --
  every leg across project boundaries, `besitz` over the arenas of all projects.
* Contract-free projects owe no hand-written proof (`nutzerTeilO_ohne`), via the generalized soundness of
  `logikFrei`.
* Witnesses for every unit and every boundary (`schnitt`, `projekte_zeuge`): whatever the unit carries across
  the boundary -- a shared atomic, a call with contract and a lock held across it, a guarded table, an invariant,
  an allocation -- crosses a project boundary.

Found while proving, and next:
* **Reuse across programs needs an embedding of declarations.** The projects are stated over ONE link declaration
  (as `GabbroZielVerbund` is). A library proved over its OWN declaration carries over into a program with a larger
  declaration only by a theorem that the obligations survive an embedding `D_lib ↪ D_link` (functions, tables,
  globals, locks, axioms; bodies translated, worlds restricted). Until it exists a project's proof is reused within
  one link declaration, and re-proved (cached by content) for another. L4 (each project's own initial memory) is
  part of this embedding. L5 (one lock order) needs no theorem of its own: the whole-program acceptance decides
  `stufen` over the composed program.
* Name spaces (7.6): Lean done (copy + path names, project-relative paths, visibility); Rust follows.
* Witnesses still to build: a thread spawned in one project running code of the other (the callback witness is
  `einbettung_zeuge` with `rueckruf_echt`, 7.10).
* `GabbroZielVerbund` for n units with every leg (7.7), then the build accepts dependencies.

### 7.10 Design: the embedding theorem (reuse without re-proof, 2026-10-25)

**What it says.** A project proved over its OWN declaration `D` (its items and the heads it imports) keeps its
proof in every program whose declaration `D'` contains it: given an embedding `ι : Einbettung D D'`, every
obligation `KoerperGutSA`/`InvGutSA`/`InvGutGrundA` of a function `f` of `D` (with the open-world rely) implies the
same obligation of `ι f` for the translated body in `D'`. With it, `gabbro_ziel_projekte` takes each project's proof
over its own declaration, not over the link declaration.

**The embedding** (`Einbettung D D'`): injections of every sort (tables with a bijection of their fields, globals,
locks, marks, functions, invariants, axioms, registers, assumptions) that preserve every attribute the semantics or
the checker reads (types, counts, guards, ranks, signatures, conformance, frames, ensures, carriers), and table and
signature NUMBERS used in the project's types, so that a type of `D` is the same type in `D'`. A diamond of projects
is two embeddings into one `D'`; no quotient is needed.

**Why the proof carries over** -- a simulation with a FIXED context: during one run of a project body in `D'`, the
part of the world outside the image of `D` does not change and is not read: the body names only items of `D`; a
callee of `D` writes only its declared frame (in `D`); an axiom of `D` writes only its frame (`RahmenO`); the
environment moves at a lock of `D` only that lock's carriers (`HavocOk`); an atomic read answers only for the
carriers it reads. So every `D'`-object the obligation quantifies over (world, oracle, environments, call handler)
restricts to a `D`-object, the `D'`-run is the translated `D`-run, and the trace grows only by the translated
events.

**Stages** (each a commit with witnesses, Lean only; LLVM later):
* E0 the embedding: sorts, types (numbers mapped by `num`/`tnum`), values, resources, signatures, contracts;
  the translation of syntax (`Zielsatz/Einbettung/{Einbettung,Ressourcen,Syntax}.lean`). DONE.
* E1 values, memories, environments (`Welt.lean`); E2a evaluation commutes (`Auswertung.lean`). DONE.
* E2b/E2c the simulation: one step beside its image under the KEYS (`Schritt.lean`), the induced handlers
  (`Handler.lean`), the run relation (`Lauf.lean`), loops (`Schleifen.lean`), and every statement, block, end
  block and arm list of `D` beside its image (`Koerper.lean`: `sim_stmt` ... `sim_grund`). DONE.
* E3 the obligation transfer: `logikPflicht_E` (`Uebertragung.lean`) with the lawfulness of the induced handlers
  (`Pflicht.lean`) and the witness `einbettung_zeuge` (`Zeuge.lean`: every library embedded into the
  program that adds a callback). DONE; `nutzerTeilO_E` feeds it into `NutzerTeilO` (`Projekt.lean`).
* E4 callbacks (below; no change of `Spec.lean`). DONE: `Rueck`, `VRel` and the call keys (`Welt.lean`,
  `Schritt.lean`, `Handler.lean`), the relational simulation (`Koerper.lean`), `RueckVertrag` and
  `konform_vertrag` (`Pflicht.lean`), the field `rueck` of `Uebernahme`; the witness `einbettung_zeuge` holds for
  every library, with a real callback (`rueckruf_echt`: one function outside the image conforms to the signature
  of the library function `g₀`, which is its head).

**E4: callbacks across the boundary without a change of the goal statement.** Before E4, `ZeigerfreiD` kept
every function pointer out of a project's state and interface, because a foreign function has no name in `D`. The
design: the project declares, per pointer signature `n` it hands out or calls through, a HEAD `ext n` (a function
without a body, conforming to `n`) whose contract is the pointer's contract (source: a contract on the `fnptr` type;
sugar over the existing model, no new form of G or `Akzeptiert`). The project's proof treats a call through a
pointer like any call: against the callee's contract, which for a foreign callee is `ext n`'s. The embedding then
relates a pointer value of `D` to one of `D'` instead of mapping it: an image function to its image, `ext n` to
every function of `D'` outside the image that conforms to `num n` (there is no equality test on function pointers,
so nothing observes the difference). `Treu` and `eval_exE` become relations at `fnptr` types; the keys also record
the callee of an indirect call; the induced handler answers for `ext n` what the `D'`-handler answered for the actual
callee. What the link adds is one obligation of the linking program, a premise of the transfer (not of
`GabbroZiel`): every foreign function it passes as a pointer of signature `num n` refines the contract of `ext n`
(its `requires` follows from `ext n`'s, its `ensures` implies `ext n`'s). A program that does not want to prove it
re-proves the library instead; nothing is assumed.

How it was built (2026-10-25):
* The head is chosen by the embedding, not declared anew: `Rueck.rep n` names a function of `D` conforming to `n`,
  and `Rueck.voll` demands one for every signature some function of `D'` outside the image conforms to.
* `VRel` relates values: at `fnptr n` the image, or (`rep n` = the `D`-value) any foreign function conforming to
  `num n`; elsewhere equality through the embedding. `Treu`, `EnvR`, `eval_exE`, every write and every outcome
  relation are stated with it.
* The keys are split by handler kind: main keys (world pairs), atomic keys (world pairs at an atomic read) and
  CALL keys (the `D`-world at a call with the callee `D'` really called and its arguments). Finding: with foreign
  pointers in shared or protected carriers, an atomic answer or a lock move can change the `D'`-world without the
  `D`-world changing, so one list of pairs is no longer functional; the call key also records which foreign
  callee stood for the head.
* `RueckVertrag` (a field of `Uebernahme`): a foreign function conforming to `num n` writes only images of what
  `rep n` may write, its `requires` holds EXACTLY where the head's does (an implication is not enough: the entry
  gate `torRuf` must answer alike on both sides), and its `ensures` gives the head's on the restricted answer.
* Pointer-free where `D` reads an answer of the hardware or the environment as a value (`Rueck.regFrei`,
  `regFreiG`, `atomFrei`, `aergFrei`, `aparamsFrei`, `rtypFrei`): a register or atomic carrier, an axiom argument or
  result, a register type. Finding: otherwise the induced oracle is not register-local (two `D'`-worlds beside one
  `D`-world may hold different foreign functions there). The induced oracle answers visibility of a
  pointer-carrying global constantly; no awaited global carries one, since awaited globals are atomic.
* The `logik` outcome of a foreign callee is seen from `D` as blaming the caller of the head, so the transfer no
  longer needs a premise that the `D'`-handler blames only images.

**What E3 needs** (`Uebernahme`, the link-time conditions, and the premises of `logikPflicht_E`):
* the bodies, contracts and invariant predicates of the program are the images (`Fortsetzung`);
* an image lock protects exactly the images of the lock's carriers under the same invariant;
* the program's atomic rely is no larger on the image than the project's (`OffenA` on both sides satisfies it);
* the program's axiom ensures agree with the project's on the image;
* **an invariant over an image table is an image invariant** (finding: a program may not add an invariant over a
  library table and expect the library's proof to keep it -- the library cannot know it; such an invariant must
  be the library's, or the program re-proves the library functions that write the table);
* `Rueck`: a head for every pointer signature a foreign function conforms to, and pointer-free register,
  atomic and axiom answers; `RueckVertrag`: foreign callbacks keep their head's frames and contract (E4);
* `PadOk`: the project declares a table, a global or a lock (the neutral trace piece). Finding: for a declaration
  with none of them the transfer is FALSE in general -- its worlds cannot tell two calls of a foreign function
  apart, so a proof may use "same world, same answer"; a stateless project gets a ghost carrier of its own.

**Finding while designing E1 (2026-10-25): obligations do not carry over WORD FOR WORD.** The user obligation (b)
quantifies over call handlers, oracles and environments that are FUNCTIONS of the world, trace included. In a larger
program the trace carries events the project cannot see (locks the caller holds, events a callee appended), so the
same project-visible world can meet different answers. A proof over `D` may use "same visible world, same answer"
(a body that calls `g()` twice with nothing in between and promises `x == y`); over `D'` that step is not valid.
So the transfer cannot map each `D'`-object to a `D`-object pointwise.

**The construction that still gives it, without changing the model or the statement:** the `D`-objects are built
from the given `D'`-run (run-indexed), and the `D`-trace is marked with harmless access events so that every
consultation of an outside object happens at a different `D`-world; then one function of the `D`-world reproduces
every answer the `D'`-run receives. This needs a carrier in `D` to mark with (a table or a global; a project
without any state is handled by a ghost carrier of its own). It is proof work, not a model change -- the strongest
variant -- and it is the critical path of E2/E3.

### 7.11 What the build does with dependencies (2026-10-25)

* `dependency(...)` resolves a COPY per source and option set (`bau/abh.rs`): evaluated in its own scope, its options
  from `options:` and `-D<project>:<option>=<value>`, the program's `target` and `buildtype` handed down; the version
  requirement (`'>=1.2, <2'`: comparisons joined by `,`) checked against `project(version:)`. Two versions are two
  copies, each in its own name space (`store_v1_3_0`); one version from two sources, or with two option sets, is
  refused; so is a cycle of projects.
* `gabbro.lock` lives in the build directory: per copy path, version, options and a content fingerprint of its build
  files and sources. `setup` writes it, `compile` refuses a changed dependency by name, `configure` accepts it.
* A target reaches a dependency through `use <dependency>::<module>::<item>` into a library the dependency marks
  `export: true`; that library and what it uses (of its own project or of ITS dependencies) join the unit. Each
  library of a dependency is also checked alone (`built store:stock`).
* Several projects in one unit get name spaces on the tokens before the checker sees them (`bau/namensraum.rs`,
  the rule of `Parser/Namen/Namensraum.lean`): every top-level module goes below its project's name space, a
  dependency's local name becomes its copy's name space, every item stands in a module, and a path whose head is a
  project the file's project does not declare -- or a module a dependency does not export -- is refused. The program
  is ONE unit for the checker, as §7.2 says; `gabbro_ziel_projekte`/`gabbro_ziel_verbund_n` are its statements.
* Open, a language change (Lean model first): carriers and exported items are named by their SHORT name -- in
  `effects { writes T }` and in the product's symbols -- so two projects may not both export an item of one name
  (`N039`, tested). Modules of one name are fine. Lifting it needs qualified carrier names in effects and qualified
  symbols in the LLVM backend. Also open: running a dependency's own tests (`gabbro test -C build store:`), `--fix`
  applying the printed fixes, separate compilation (§7.7).
