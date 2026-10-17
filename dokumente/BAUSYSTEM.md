# The build system: `gabbro build`

*Rewritten 2026-10-17 from the reckoning of 2026-08-31 (written before the first line of `bau.rs`) and what the
build grew into. Code: `crates/gabbro-cli/src/bau.rs` (manifest, graph, fingerprints, entry rules) and
`treiber.rs` (the generated drivers and runtimes). Tests: `crates/gabbro-cli/tests/{bausystem,zweieinheiten,eintritt,
verbund,onramp}.rs`.*

**Which backend this drives.** `gabbro build` is the build of the **legacy C11 path**: it emits C per unit
(`C-SPEICHERMODELL.md`), compiles it with the manifest's `compiler` line, links, and writes the generated drivers.
The LLVM backend ([`LLVM-BACKEND.md`](LLVM-BACKEND.md)) is not reachable through a manifest today: it is driven by
`gabbro llvm [--unit]` and `instrumente/teile/baue-llvm.sh`. A manifest word that selects the backend does not exist.

## 1. The decision: Cargo-like with a manifest, not a generator

The reasons are in the language, not in taste:

* `when TESTBUILD` is a language construct (`beispiele/52-baugatter.gab`), not a compiler flag.
* `arch x86_64` stands on `entry`, `boot` and `entrust`: the target architecture is a statement of the source.
* `gabbro emit a.gab b.gab --unit` already produces ONE translation unit; the link step is really the question
  *which files form a unit*.

**What stands in the source and what does not.** A second register over the same thing is `W7`, and a manifest that
rewrites the dependencies is exactly that: the `use` edges are already in the files.

| Quantity | In the source? | Where |
|---|---|---|
| a file's module name | yes | `module X { ... }` |
| dependency edges | yes | `use a::b::C;` |
| target architecture | yes | `arch ...` |
| conditional translation | yes | `when TESTBUILD` |
| effects, costs, locks | yes | `effects`/`costs`/`locks` |
| **which files exist** | **no** | a file does not know its siblings |
| **which files form ONE unit** | **no** | |
| **which foreign compiler, with which flags** | **no** | not a language question |
| **what the product is** (object, program, module) | **no** | |

Four lines without a representative in the source: that is the manifest, and nothing more.

**Measured on 2026-08-31 (491 `.gab` files; the tree has 1,339 now, the argument does not move):** only 16 files
carry the module name their file name suggests, 473 do not; 14 module names belong to more than one file, `module gift`
to 122 of them. So "module name = file name" is refuted (the manifest must name the FILES), and a GLOBAL module-to-file
map is impossible: a module name is unique only INSIDE a unit (`N039` says it when it is not). Hence:

```
the manifest names FILES per unit; the build READS them and computes
    file -> module (from `module`), module -> unit (from the manifest), unit -> unit (from `use`)
```

*Edges are computed, never written.* A manifest that wrote them would be a second register over the `use` lines, and
the first time a `use` is added and the manifest line is not, the build would build out of a mixture.

## 2. The manifest

Line-oriented, `--` comments, **the indent is the whole syntax**: an indented line is one file of the unit above it.
Every refusal names its line number; the build never guesses what a manifest meant. The manifest has no optional line
that a program needs beyond `compiler`, `out`, `unit` and the indented files (`gabbro new <name>` writes a working pair,
`<name>.gab` plus `<name>.bau`, that check, build and run as written; `dokumente/TUTORIAL.md` is the long form).

```
-- gabbro.bau
compiler cc -std=c11 -Wall -Wextra -Werror
out      target/bau

unit lager program
    programmlogik/beispiel/lager.gab
    programmlogik/beispiel/betrieb.gab
```

| Word | Meaning |
|---|---|
| `compiler <cc> <flags>` | the foreign compiler and its flags (the whole line enters the fingerprint: another flag is another artefact) |
| `out <dir>` | where the products go |
| `unit <name> <object\|program>` | the unit's art: `object` compiles, `program` links (not a language question, hence in the manifest) |
| `unit <name> module <init> <exit>` | the third art: a loadable Linux kernel module whose two loader entry points are the named functions (below) |
| indented path | a file of the unit; a `.c` path is a foreign body for an `extern fn` the program declared; a `.h` (module units only) replaces one of the module's generated headers |
| `nolibc` | the `program` units are Linux x86-64 processes WITHOUT a C library: linked `-nostdlib -static`, entered by a generated `_start` (template `start.nolibc`); the `compiler` line must carry `-ffreestanding` and `-fno-stack-protector`; the entry knows no system call: it calls the unit's `gabbro_os_anfang()` first when defined, then `main`, and hands a returned status to the unit's `gabbro_os_ende(code)`; a unit offering neither end is refused before any C (`eintrittsregel`) |
| `metal <dir>` | the bare-metal runtime directory (`laufzeit/metall`): the build links `<unit>.metall.elf` itself, and WRITES the image's arena runtime (`<unit>.metall.c`), memory functions (`<unit>.metall.speicher.c`) and `<math.h>`/`<string.h>` headers |
| `kmod <kernel build dir> <load symbol> <unload symbol>` | the kernel's own build tree and the two symbols its loader calls (for Linux `init_module cleanup_module`); all three named, none guessed |
| `provision <bytes>` | static storage of each dynamic arena of a `module` unit, a positive multiple of 4096; a `grow` past it answers `false` |
| `note <section> <text>` | a read-only string a module carries in a named section (e.g. `note .modinfo license=Dual MIT/GPL`) |

**Why `kmod`'s calls stand in the manifest.** A Linux module is entered by a call, not by a vector, so `entry ... vector`
is the wrong word, and what the product IS has no representative in the source. The same `.gab` becomes an object, a
program or a module depending on this line alone. The load verdict is the init function's answer (0 loads); the build
refuses an init that answers nothing, takes an argument, is not declared, or shares its name with the exit, and a module
unit that declares the hosted entry `pub fn main`.

**Not a Gabbro file, on purpose.** A manifest describes no unit (no `module`, effects or costs); writing it as Gabbro
would invent item kinds the language does not have, the direction `W24` stands against. (`gabbro abi` writes `.gabi` as
Gabbro because an interface DOES describe a unit.)

## 3. What the build generates (no handwritten C of Gabbro's)

Everything a finished binary needs beyond the emitted unit is written by the build from proved templates, over the
program's OWN binding (`bibliothek/linux/linux.gab` for hosted programs, `bibliothek/linux-kmod/` for modules): an OS
call is a `syscall` item the program declares, and nothing in the build knows an operating system.

| Product | Written by the build | Template (Lean `Bausteine/Schablonen/`) |
|---|---|---|
| hosted driver `<unit>.treiber.c` for units with roots (`concurrent`): one wrapper per root, one thread per root, join all, the never-spawned idle root, lock primitives, dynamic-arena reservation | `treiber.rs::erzeuge`, versioned `GENERATOR_KENNUNG` (a template change with unchanged sources rebuilds once) | `sperre.ticket`, `faden.laufzeit`, `arena.dyn`, `tor.trampolin` |
| process entry for `nolibc` | `prozess_start` | `start.nolibc` |
| kernel-module driver (Kbuild, loader entry points, arena pools, lock primitives, one kernel thread per root, `<stdatomic.h>` over the compiler's C11 builtins) | `treiber.rs::erzeuge_kmod`, then `make -C <kernel build dir> M=<dir> modules` -> `<unit>.ko` | `modul.lebenslauf`, `arena.modul`, `faden.modul` |
| bare-metal image (arena runtime, memory functions, thread runtime, IDT, headers) | `metall_bild_binden` | `metall.speicher`, `arena.metall`, `faden.metall`, `idt.metall` |

`gabbro runtime arena|threads|metal-arena|metal-memory|metal-threads|metal-idt|metal-include <dir>` prints the same
text for a harness. A `.c` path in any unit's list is the body of an `extern fn` the program declared: a module unit compiles it into the
module, a non-module unit compiles it beside its own object (`<unit>.fremd<N>.o`) and a `program` links it; a `.h` is the
module include mechanism and is refused elsewhere. The arenas are NOT in the manifest (only their storage `provision`): the emitted unit
carries `#define GABBRO_ARENEN`, and the driver binds exactly that list (`W7`).

Measured where it can only be measured: `instrumente/pruefe-kernelmodul.sh` builds the module probes through
`gabbro build` and loads them **in QEMU, never into the host's kernel**; `instrumente/pruefe-os-bindung.sh` checks what
the runtimes still take from the OS; `instrumente/pruefe-metall.sh`/`pruefe-freistehend.sh` the bare-metal stages.

## 4. Incremental by CONTENT, not by timestamp

`CLAUDE.md` carries two traps of this class in opposite directions (`rsync -a` against `cargo`, where the timestamp
lied; the lock after `abnahme.py --voll`, where it told the truth about something that did not matter). A tool that
measures the time instead of the content errs both ways.

Per unit the fingerprint covers: the content of every source file (manifest order), the compiler line with its flags, the
build mode (`--testbuild` or not), **and the fingerprints of everything the unit rests on** (a change in a dependency's
PRIVATE body does not move its `.gabi` and does move its object: without the chain a program would be reported current
over a library it no longer contains), plus the driver generator's version and, for a bare-metal image, the runtime
sources' bytes. If it matches the last record AND the product is present, nothing is done (*presence is checked, not
believed*). FNV-1a, 64 bit, by hand: not cryptographic, and not meant to be (it guards an accidentally unchanged product,
not a collision-seeker).

## 5. Commands and the coverage line

```
gabbro build [--testbuild] [--dry-run|--trocken|--c-liste] [<manifest>]    (German second name: bau)
gabbro build <a.gab> <b.gab> ...       the link check only, nothing compiled (like `gabbro link`)
gabbro new <name>                      a checking, building, running skeleton
gabbro link [--with L.gabi]... <a.gab> <b.gab> ...   do the units make ONE program?
```

The build prints what it built AND what it did not look at, because "nothing found" and "nothing looked at" read alike:

```
built 1 unit(s), 0 up to date, 0 refused
NOT looked at: N `.gab` file(s) in this tree stand in no unit of this manifest
  the manifest is the reach -- a file no `unit` line names is not a file this build passed
```

The manifest renders refusals through the same offset map as `pruefe --unit` (`main.rs::zeige_je_stueck`): file names and
line numbers are the file's own, never the joined text's.

## 6. The edge between units: built and run (2026-09-01, `OB5`)

```
rechenwerk (object)   prog-vorrat.gab + prog-werk.gab  ->  rechenwerk.o + rechenwerk.gabi
     ^                                                     (checked, translated AND described as ONE unit)
     | use werk::ablegen, use werk::holen, use vorrat::Regal
haupt (program)       prog-haupt.gab                   ->  haupt.o, then the linker
```

(`messung/einheit-proben/zwei-einheiten.bau`; the program exits 137: 100 from a `5000` capped by a PRIVATE helper of the
other unit, plus 37 passing through, a number for which both halves of the border must hold.)

* **`emit --unit` and `abi --unit`.** A unit that CHECKS as a unit is TRANSLATED as one (seven refusals without the flag,
  zero with it, on the same two files).
* **The edge is carried, not only computed.** Before each unit stands the `.gabi` of everything it rests on, transitively
  and in build order (a signature that names a type it does not declare is what `N038` refuses inside).
* **The fingerprints of the sub-builds go into the own fingerprint** (section 4).
* **Effect derivation sees across the border** (`abi --vergleich`: a body with no own place touches `reads/writes
  Regal.slots` only through the callees' contracts, which come from the `.gabi`), and the opposite direction falls: an effect
  done beyond the border and not declared this side is `E008`; without the bridge the same file falls at `K003`.
* **An `assume` does not cross the border.** `abi.rs` says it in its head: a library shipping its `assume` lines forces
  its machine on every importer, and an override at import is not a replacement but a proof duty (`ABI4`). The importing
  program therefore passes with 0 assumptions over a library proved under one, and `gabbro pruefe` does not name it:
  the import form is unbuilt, not impossible.

Tests (the two kinds each way): `inkrementell_nach_inhalt_und_nicht_nach_zeitstempel`,
`eine_andere_uebersetzerfahne_baut_neu`, `der_graph_wird_gerechnet_und_nicht_gelesen` (`bausystem.rs`);
`das_zweieinheitenprogramm_uebersetzt_und_laeuft`, `ohne_die_kante_faellt_das_programm`,
`ein_programm_ohne_main_faellt_an_der_eintrittsregel`, `was_pub_nicht_traegt_bindet_nicht` (`nm -g` outside shows exactly the
exported names), `eine_aenderung_im_privaten_rumpf_baut_das_programm_neu`, `der_treiber_druckt_und_wird_verglichen`,
`die_effektableitung_sieht_ueber_die_grenze`, `eine_annahme_traegt_nicht_ueber_die_grenze` (`zweieinheiten.rs`).
Poison manifests under `messung/einheit-proben/gift-*.bau`: one module name in two units, a unit without a file, a unit
that does not check (`REFUSED ...: N error(s) -- no C written`), a program without an edge, a program without `main`.

## 7. The entry rule (a manifest rule, so no `Satz`)

A `unit ... program` names exactly one entry, an ordinary `pub fn main` (`main` is an identifier, not a keyword;
`entry` declares an interrupt stub entered by hardware, a different construct). Before the rule the lower rows were
refusals from foreign tools one or three tools downstream (`ld`: undefined `main`; `cc -Werror=main`: a private or
mistyped `main`); `N039` covers only two EXPORTED `main`. The rule fires in `bau.rs::eintrittsregel`, before any C. It
carries no identifier: a `Satz` says what is true of a program the checker passed, and a manifest is read by no pass
(`paesse.rs` holds the passes at twelve, `pruefe-saetze.py` counts identifiers owing a statement as a ratchet). The same
reading governs every manifest refusal here (module in two units, cycle, empty unit, linker refusal, `kmod`, `provision`,
`note`, `nolibc` hooks, module rules, bindings): no `-- erwartet: CODE` probe can name them; the probes are `.bau` files.
**Name collisions with C** (`putchar`, `exit`, ...) are `N041` (`C-SPEICHERMODELL.md` section 8): a Gabbro program does not
print by calling `putchar`; it declares its own `syscall` item (`bibliothek/linux/linux.gab` `gabbro_os_schreibe`).

## 8. What is NOT decided or not built

* **A cycle BETWEEN units**: the sorter names it, no manifest carries one; whether it is refused stays open.
* **`arch` across a unit border**: two units with different `arch` are unmeasured, the `.gabi` carries no `arch`.
* **Lock ranks across a BUILD border**: ranks travel since 2026-08-21 and `H012` falls across a unit border, but
  `zwei-einheiten.bau` has no ring, so the case is unmeasured in the build.
* **Parallelism**: units build one after another.
* **`--testbuild`** enters the fingerprint but no probe drives it through a full build.
* **A manifest word choosing the backend** (LLVM): none; the LLVM backend has no manifest path.
* **Whether the units of this tree are cut correctly**: the manifest says what belongs together; no tool says whether it
  does.
* **Refinement of linked code**: linking proves nothing about the linked bytes; the model half is `GabbroZielVerbund`
  (OFFEN O28 remainder), the byte half is translation validation (`PLAN-UEBERSETZUNGSVALIDIERUNG.md`).
