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
