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
| dependency lists between targets (`dependencies:`) | edges are COMPUTED from `module`/`use`; a second list over the same thing would drift (W7) | the sources |
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
| `program('name', <sources>…, install: false)` | links to `<builddir>/name`; must carry `pub fn main` |
| `library('name', <sources>…)` | a SOURCE library (§3); checked alone; must not carry `main` |
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
project('lager', version: '1.0')

library('lager', 'lager.gab')                       # declares `module lager`
werk = program('werk', 'werk.gab', install: true)   # `use lager::…` -- the edge is computed
if get_option('buildtype') == 'testbuild'
  test('werk-laeuft', werk, stdout: 'ok\n')
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
| an empty target, two targets or tests of one name | an empty target builds nothing and says it built; artefacts would overwrite one another |
| a module declared by two libraries, or twice in one unit | a `use` edge would have two targets |
| a program using an object's or program's module | no separate compilation across units (§3) |
| a `program` without `pub fn main`, a `library`/`object` with one | the entry rule, checked on the IR before any tool runs |
| `setup` over an existing build directory | a build directory is one configuration; `configure` changes it |

## 7. Plan: linking Gabbro projects with dependencies (2026-10-25, for review)

*Status: PLAN, nothing implemented. Set by Simon: two or more Gabbro projects, the source of each present, each with
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
# lager/gabbro.build                         # werk/gabbro.build
project('lager', version: '1.3.0')           project('werk', version: '0.2.0')
library('lager', 'bestand.gab',              lager = dependency('lager', path: '../lager',
        export: true)                                           version: '>=1.2, <2')
library('intern', 'hilfe.gab')               program('werk', 'werk.gab', install: true,
                                                     dependencies: [lager])
```

* `dependency(name, path: …, version: …, options: […])` resolves a project from a local path or from
  `subprojects/<name>/` (as Meson does); no network fetch. `version:` is checked against `project(version:)`.
* A dependency's `export: true` libraries are visible to dependents. Its other libraries are used by its own
  exported code as usual and enter the unit when reached -- they are just not named by the dependent's `use`.
* **Declared and computed** (W7 stays): `dependencies:` says which projects a target may draw from; which files enter
  the unit is computed from `use`, as today. A `use` into an undeclared project is refused with the fix
  ("add `dependencies: [lager]`", machine-applicable via `gabbro check --fix`); a declared dependency no `use`
  reaches is refused with the fix to delete it.
* **Options**: each dependency has its own options (`options:` in the call, `-Dlager:trace=true`, `configure`
  lists them). `target` and `buildtype` are the program's and are handed down.
* **Name spaces from the start** (7.6): every module of a dependency is reached as `<project>::<module>`, so two
  projects with `module util` link without a rename.
* **Several versions of one project** in one program are allowed when they are different dependencies of different
  projects: name spaces carry the version (`lager@1`, `lager@2`), each copy has its own globals. One version reached
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
   lager:`); install.
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

`use lager::bestand::Regal` (and `lager@2::…` when two versions are present) names a dependency's module. Lean parser
(`Parser/`), exporter and `SYNTAX.md` first, then Rust parser and checker. Machine G is untouched (the declaration's
names are opaque); the parser theorems and the exporter's export of qualified names move. Exported heads,
contracts, effects, costs and lock-rank constraints of a dependency are readable as its interface (`gabbro abi
--project`), for the reader and for 7.7.

### 7.7 Separate compilation -- the same guarantees, faster

Required, not optional, but ONLY in a form that gives exactly what 7.2 gives:
1. `GabbroZielVerbund` is extended to n units with every leg of `GabbroZiel` and every row of 7.1 (open-world rely
   across the link, `besitz` across the link, callbacks, differing initializers and assumptions, composed lock
   order) -- a reviewed `Spec.lean` diff -- with a theorem that "each unit accepted alone + link check" implies the
   whole-program acceptance. Then a dependency is checked ONCE and its verdict reused by content fingerprint.
2. The LLVM backend emits units with external linkage, every static defined once.
3. Translation validation covers each object and the link step (`PLAN-TRANSLATION-VALIDATION.md`).
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

### 7.9 Status (2026-10-25, branch `ziel/projekte`)

Proved in Lean (THEOREM-MAP §94), all axiom lists standard:
* L1 composition (`komponiere`), L2 composition of (b) under the open-world rely (`nutzerPflichtA_komponiere`), L3
  assumptions as the conjunction of the projects' ensures (`qAlle`), L6 the statement `gabbro_ziel_projekte` --
  every leg across project boundaries, `besitz` over the arenas of all projects.
* Contract-free projects owe no hand-written proof (`nutzerTeilO_ohne`), via the generalized soundness of
  `logikFrei`.
* Witnesses where a shared atomic, a call with contract + a lock held across it + a guarded table + an invariant,
  and an allocation cross the boundary.

Found while proving, and next:
* **Reuse across programs needs an embedding of declarations.** The projects are stated over ONE link declaration
  (as `GabbroZielVerbund` is). A library proved over its OWN declaration carries over into a program with a larger
  declaration only by a theorem that the obligations survive an embedding `D_lib ↪ D_link` (functions, tables,
  globals, locks, axioms; bodies translated, worlds restricted). Until it exists a project's proof is reused within
  one link declaration, and re-proved (cached by content) for another. L4 (each project's own initial memory) is
  part of this embedding. L5 (one lock order) needs no theorem of its own: the whole-program acceptance decides
  `stufen` over the composed program.
* Name spaces (7.6): a dependency's modules wrapped under its project name need relative module paths inside the
  dependency -- a language change, Lean front end first.
* Witnesses still to build: a callback through a function pointer into the dependent, a thread spawned in one
  project running code of the other.
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
* E1 worlds: restriction, merge with a fixed context, events and the trace (`offen` commutes with the filter).
* E2 semantics: `eval`, `execEndHA` simulation, oracle/environment/handler restriction.
* E3 the obligation transfer and `gabbro_ziel_projekte` over per-project declarations; a witness with two projects
  over DIFFERENT declarations.
* E4 callbacks: a function pointer of `D` may in `D'` point to a function outside the image. The project's proof
  then needs a contract per POINTER SIGNATURE (what every conforming callee promises); today contracts are per
  function. This is a language question (a contract on `fnptr` types) and is put to the owner before it is built;
  until then E3 requires that no foreign function conforms to a pointer type of `D` (decidable).

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
