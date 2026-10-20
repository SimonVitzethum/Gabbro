# The build system: `gabbro build`

*Rewritten 2026-10-17, when the C backend was removed (tag `archiv/c-emitter-2026-10-17` keeps the old
build with its generated drivers, kernel-module and bare-metal products). Code:
`crates/gabbro-cli/src/bau.rs` (manifest, graph, fingerprints, the LLVM tool chain). Tests:
`crates/gabbro-cli/tests/{bausystem,onramp,verbund}.rs`.*

**What `gabbro build` does.** For each unit of a manifest, in dependency order:

```
checker  ->  LLVM IR (`gabbro llvm`)  ->  opt -O3  ->  llc -O3  ->  <unit>.o  ->  ld.lld -static -e _start
```

The tools `opt`, `llc` and `ld.lld` are found on `PATH`; a missing tool is a refusal that names it. There is no
`cc`, no libc and no startup file: the entry `_start` is written by the generator around `pub fn main`, and every
operating-system call is a `syscall` item of the program itself. `--target=x86_64|aarch64` picks the target
(default `x86_64`; the target is part of the fingerprint). A `program` unit is linked to `<out>/<name>`, an
`object` unit stops at `<out>/<name>.o`; the IR (`.ll`), the bitcode and the interface (`.gabi`) stay beside it.

## 1. The decision: Cargo-like with a manifest, not a generator

The reasons are in the language, not in taste: `when TESTBUILD` is a language construct, `arch x86_64` stands on
`entry`, `boot` and `entrust`, and *which files form ONE unit* is the question a manifest exists to answer.

| Quantity | In the source? | Where |
|---|---|---|
| a file's module name | yes | `module X { ... }` |
| dependency edges | yes | `use a::b::C;` |
| target architecture | yes | `arch ...` |
| conditional translation | yes | `when TESTBUILD` |
| effects, costs, locks | yes | `effects`/`costs`/`locks` |
| **which files exist / form ONE unit** | **no** | |
| **what the product is** (object, program) | **no** | |

*Edges are computed, never written*: a manifest that wrote them would be a second register over the `use` lines
(`W7`). The manifest names FILES per unit; a module name is unique only INSIDE a unit (`N039`).

## 2. The manifest

Line-oriented, `--` comments, **the indent is the whole syntax**: an indented line is one file of the unit above it.
Every refusal names its line number.

```
-- gabbro.bau
out      target/hallo

unit hallo program
    hallo.gab
```

| Line | Meaning |
|---|---|
| `out <dir>` | where the artefacts go (obligatory) |
| `unit <name> <object\|program>` | a unit; its indented lines are its `.gab` files |

`gabbro new <name>` writes a working pair (`<name>.gab`, `<name>.bau`): a libc-free program that makes the Linux
`write` call through its own `syscall` gate and prints `Hi`.

## 3. What is refused, by name

| Refused | Why |
|---|---|
| a `unit … module` and the words `kmod`, `provision`, `note` | a Linux kernel module needed the generated C driver and the kernel's C build |
| the word `metal` | a bare-metal image was linked from generated C |
| the word `compiler`, the word `nolibc` | nothing foreign is compiled; every program is libc-free |
| a `.c` or `.h` file in a unit | this build compiles no C |
| a unit that uses another unit | separate compilation across units is not implemented in the LLVM backend (the generator defines the items a `.gabi` preamble declares, so the second unit would define statics twice); put the files into ONE unit |
| a `program` without `pub fn main`, an `object` that has one | the entry rule, checked on the IR before any tool runs |

## 4. Incremental by CONTENT, never by timestamp

The fingerprint is FNV-1a over the files' names and bytes, the target, the build mode and the fingerprints below the
unit. A `touch` does not rebuild; a deleted artefact with a valid record does -- *the artefact's presence is checked,
not believed.* The record is written last. A tool that measures the time instead of the content errs in both
directions (the `rsync -a` trap of `CLAUDE.md`).

## 5. Beside the manifest

* `gabbro build a.gab b.gab …` (no manifest): the link check only (`gabbro link`), nothing compiled.
* `--dry-run` prints the plan, the computed edges and the coverage line: *what the build did NOT look at* is counted
  next to what it built, because "nothing found" and "nothing looked at" look the same otherwise.
* After several units the whole set is checked again as ONE program (`verbund::verbinde_alle`).
* `--testbuild` opens the build gate (`when TESTBUILD`); its absence is the shipping build.
