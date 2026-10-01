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

## Review repairs (2026-10-01, coordinator review)

Five findings, all fixed in `dokumente/x86/IMAGE-ABI.md`, no other file
touched:

1. File vs virtual addresses (§1 rewritten): the old `base + file offset +
   addend` formula is gone. File ranges and virtual ranges are now related by
   one checked per-section mapping (file containment, virtual nonwrap,
   canonicality, `filesz <= memsz`, disjointness in both spaces, alignment);
   relative displacements are computed from the actual virtual next-RIP.
   Relocation kinds declare their operand field inside the decoded
   instruction; a site in a matching field is the legal case. §4 and §15 now
   refuse the same thing: sites with fields invalid for their kind (wrong
   range/width, overlapping opcode bytes, between instructions, in data,
   wrong section kind), never every instruction-interior site.
2. Two-mode bias contract (§4 rewritten, no third case): mode F (pinned
   absolute virtual addresses: hosted static, bare-metal 1 MiB identity,
   module post kernel relocation pass) vs mode P (quantified `base` with
   checked alignment/range/nonwrap/canonicality side conditions plus the
   syntactic condition that no absolute site outside a bias-carrying
   relocation depends on `base`; hosted PI only). No loader-only fixup exists
   in either mode; an unlisted loader fixup breaks sec. 11 mapping equality.
3. Software is never hardware (§11 rewritten, §12 extended, doc audited):
   loader/kernel/page-table software correctness is checked by outputs
   (bytes, mapping equality, entry predicates) or validated code, never booked
   as a hardware assumption. Hardware assumptions are silicon-only (mapped-byte
   execution per admitted profile, named device/timing behaviour). The
   `os_bindung_*` family plus storage/page-return/clone-register premises are
   marked as historical source-level gaps (kernel software behaviour taken as
   premise), explicitly non-hardware, with replacement by checked binding
   logic as the stated direction. Timing-bound mentions in §14 now say
   silicon-only; the §8/§2/§5 clone/storage premises carry the sec. 12
   qualifier.
4. Proved vs open separated (§§5/9/10/17): abstract results (`CTicket.lean`
   over `sperrAbstrakt`) and C-target machine-checked template instances are
   named as what exists; x86-byte correspondence for EVERY template
   (`tor.*`, `faden.*`, `arena.dyn`, `sperre.ticket`, `start.nolibc`, module
   lifecycle) and for the LKMM mapping table is stated as unproved wave-B
   work. LKMM "proved table" wording removed. Handwritten pieces: inventory
   plus reason exempts nothing; executed body bytes need validation plus
   refinement or the image is refused (OPEN). Interrupt paths need
   source-correct save/call/restore refinement, not manifest rows (§5 entry
   bullet now states the checked sequences).
5. Loader domain scoping (§11, §15): the validated execution domain is the
   image sections plus declared stacks/reserved ranges; the surrounding kernel
   (module case) and loader mappings (hosted case) are outside it -- never
   assumed safe, reachable only at listed external-call sites with three
   cumulative obligations (checked declaration, proved x86 stub
   correspondence, and -- REPAIRED AGAIN below -- no longer a named
   software-side premise). The module does not
   require the address space to hold only its text; any other escape from
   validated bytes is refused.

Repair-pass verification: `rg` audit over the doc -- no remaining
`base + file offset` formula, no "instruction middle" refusal, no "proved
template/LKMM" claim, no software booked as hardware; section references
verified (`entries` = sec. 5, loader contract = sec. 11, gaps = sec. 17).
Docs-only repair: no Lean/Rust change, so no `./lean-bau` / `./cargo-pruef`
run (wave rules: file/claim checks, not gratuitous builds).

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

## Second review repairs (coordinator review, same day)

Two findings; the first is a bypass the previous repair introduced, the second
a wrongly broad refusal. Both fixed in `dokumente/x86/IMAGE-ABI.md`:

1. No premise bypass in §11(c): the old obligation (c) ("kernel-side premise
   stated explicitly as a named software-behaviour premise") admitted external
   code on a renamed assumption -- a third trust category the intended chain
   (user-logic proof obligations plus named silicon hardware, nothing else)
   does not have. New (c): a SUPPLIED, Lean-proved contract obligation for the
   callee side at the ACTUAL call -- requires/ensures, effects/footprint,
   errno/reason mapping discharged in Lean at actual arguments, results, and
   effects, with the implementation/refinement boundary explicit. A gate name,
   an `assume` item, or any named premise alone discharges nothing. Where (c)
   cannot be supplied, the path is OPEN and final validation refuses the
   image. Consequences applied consistently: `os_bindung_*` premises are gap
   records ONLY (§12 rewritten ending; §17 handoff rewritten) -- they qualify
   no final image and do not satisfy (c); the §2 zero-fill, §5 clone-child,
   §8 clone-register, and §9 kernel-side qualifiers now say gap record plus
   "no final image accepted on that premise alone, sec. 11(c) applies".
   Source-level checker acceptance is stated as a different chain with a
   different claim, unaffected. The proof/contract side is binding/user logic
   in Gabbro and Lean; the generic compiler hardcodes no OS and no Linux.
2. Data relocations are legitimate (§1, §4, §15 fixed consistently): two
   admissibility classes -- code-operand sites (declared operand field of one
   decoded instruction; re-decode plus correspondence re-check) vs data-field
   sites (standalone words of a kind-defined format: function-pointer and
   static-address tables, declared constant pools; width/alignment/target-rule
   checks; code pointers to decoded starts or listed entries, data pointers to
   declared data). Sitting "inside data" is no longer a refusal ground; the
   refusal is a site matching neither class, a target-rule violation, or a
   kind outside its section kinds. §4 mode-P wording now says "operand field
   or data field".

Verification: `rg` audit -- no remaining "named software-side premise" as an
acceptance basis (one historical mention in the repair note above, clearly
marked superseded), no "inside data" refusal, no software-as-premise
acceptance; §15 relocation bullet matches the §1/§4 two-class rule.
Docs-only repair: no Lean/Rust change, no `./lean-bau` / `./cargo-pruef` run.
