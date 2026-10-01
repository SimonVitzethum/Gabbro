# MUSE-REPORT-276: Final image ABI and loader contract

Lane 276, wave A. Model: opencode-go/muse-spark-1.3-contributor. No delegation,
no other model processes.

## What was done

Wrote the owned deliverable `dokumente/x86/IMAGE-ABI.md` (new file, ~17
sections): one generic validated image representation (`bytes` + `base` load
bias + `sections` + resolved `relocs` + `entries`), with decode boundaries as
validated decoder output; initial data/BSS; W^X section permissions incl.
guard pages; relocation/load-bias rules per image kind (hosted static/PI,
bare-metal fixed 1 MiB, kernel module post-load); entries for every control
inflow (hosted `main`, `nolibc` hooks + `start.nolibc`, module init/exit,
metal `_start`/AP trampoline, thread roots, IDT/timer/wake entries, clone
child path); direct/indirect control-target obligations; ABI (gate register
maps N063-N066, C ABI/arity, aggregates/layout, function pointers/`entry fn`
N575-N577, variadic N573, foreign-body N574, result/reason/region channels,
int-to-ptr refusal M140, extents N463/N464/N506/N569-N572); stack alignment,
red zone, spills, call-saved registers incl. C187 clone minimum; threads and
interrupt entries as user logic with proved-template obligations
(`arena.dyn`, `sperre.ticket`, `faden.laufzeit`, `faden.modul`,
`tor.trampolin`, `tor.kind`, `tor.region`, `tor.fehlbar`, `tor.nie`);
whole-image coverage per product (hosted driver `treiber-gen-10` contents,
`linux.gab`/`linux-kmod.gab` gates, `laufzeit/metall/` inventoried handwritten
pieces with reasons); loader contract (mapping == checked image, same
relocation values, entry predicates, no tool-correctness premise); target-data
vs generic-mechanism split (N562-N567 `zielbindung`); minimal image-backend
interface declared as interface only, explicitly not claiming existence;
generic certificate obligations; 10 concrete rejection cases; architectural
hazards; sec. 17 gaps/wave-B handoffs. Ends with a CUTS block; no Lean file
added, no code changed, no numbers/counters touched.

## Sources read

`dokumente/x86/WELLE-A.md`; `grammatik/Grammatik/X86/Typen.lean`;
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` secs. 0-5 (+ historical 6-7
skimmed as labelled legacy); `crates/gabbro-cli/src/treiber.rs` (rg outline:
`GENERATOR_KENNUNG treiber-gen-10`, `ARENA_LAUFZEIT`, `BINDUNG_KOPF`,
`FADEN_LAUFZEIT`, `SPERRE_TICKET`, `erzeuge`/`erzeuge_metall`/`erzeuge_kmod`,
roots/stacks/guard, join words); `crates/gabbro-cli/src/bau.rs` (rg outline:
`eintrittsregel`, `modulregel`, `bindungsregel[_gehostet]`, `nolibc_haken`,
`nolibc`/entry/manifest rules); `crates/gabbro-check/src/syscall.rs`
(N063-N066, buffer bound, gate shape), `zielbindung.rs` (N562-N567),
`abi.rs` (`.gabi` bridge, C ABI note); `bibliothek/linux/linux.gab`
(gate list, clone-56 contract, reserve/commit/madvise/yield/write/exit),
`bibliothek/linux-kmod/linux-kmod.gab`; `laufzeit/metall/metall.ld`
(ENTRY, 1 MiB, ALIGN(4096) sections, discards), `start.S` (entry paths,
vectors 0x40/0x41, trampoline, BSS/stack sections), `kern.c` (existence).

## Checks

- Isolation gate: pwd `/home/simon/Dokumente/gabbro-muse/a276`, toplevel same,
  branch `muse/276` -- pass.
- Claim check (docs-only task, no cargo/Lean run per wave rules): all 13 cited
  files exist; anchor grep hits confirmed (`treiber-gen-10` etc.).
- No `./lean-bau` / `./cargo-pruef` run: docs-only task, no Lean/Rust change;
  nothing to keep green beyond the new prose file. This is truthful
  non-execution, not a green claim.
- Scope respected: only `dokumente/x86/IMAGE-ABI.md` + this report written;
  no edit to Typen.lean, semantics, checker, emit.rs, TODO/AGENTS/SATZKARTE,
  ledgers, or MARKE_EMIT; no new diagnostic/gift/example/CLI numbers.

## New definitions/theorems

None. Prose contract only; CUTS block in the document states nothing is proved.

## What remains open / possible errors in the task

- The doc generalises `metall.ld`'s fixed layout to hosted/PI/module image
  kinds whose exact section bases and relocation-kind enumerations are target
  data not yet frozen anywhere; wave B must pin those per target.
- Red-zone choice for async entries and per-CPU stack switch are recorded as
  open (OFFEN O32 residue) -- the contract requires the choice be recorded
  and checked, but does not make it.
- `entry fn` whole-hand-over rule and jump-table certificate shapes are stated
  as obligations; their exact certificate syntax belongs to lanes 275/277.
- If the coordinator intended a NEW Lean file with an umbrella import for this
  lane, that was deliberately not done: a prose contract needs no `sorry`-free
  placeholder module, and an empty theorem file would add audit surface
  without content. Happy to add one on instruction.
