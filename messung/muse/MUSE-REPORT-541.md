# Muse Report 541: Independent portability design review (lane 540 candidate)

## Scope

Review-only lane. No Lean/Rust code, no model changes, no edits outside this report.
Clone verified: `/home/simon/Dokumente/gabbro-muse/a541`, branch `muse/541`.
Reviewed artefacts (from `.tmp/review/author-540/`, not the live tree):
`PATCH.diff`, `DIRECT-COMPILER-DESIGN.md` (§12 addition),
`dokumente/x86/TARGET-PORTABILITY.md` (new, 470 lines), `MUSE-REPORT-540.md`,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json`, against the actual tree at base
`0a41ca0bbf1802df2eb4deb37bff4294288de07c`.

CANDIDATE: 540 7165ebaabf2e886f0b23509ded9c3ec3bcc56eef

## Independent checks performed

1. **One chain, three concerns.** Candidate keeps exactly one source model, one
   shared IR, one executor vocabulary, one validation chain; variability is
   profile/binding DATA. No duplicated semantic backend, no per-OS fork of
   semantics/IR/executor/validator. Consistent with QUELLBRUECKE §4
   (`valX86_sound` generic, `schluss_x86` derived, refinement never assumed).
2. **No hidden Linux/POSIX/libc/ELF assumptions.** Compiler/checker/optimiser
   carry no implicit entry shape, section base, stack size, gate numbers,
   loader or thread library. Covered per profile as checked data:
   16-byte call alignment, red zone permitted-or-disabled, shadow space
   reserved-and-checked where used, callee-save per call/return, TLS only
   where used with private-area footprints, unwinding tables as validated
   data (never trusted metadata). Freestanding has no implicit libc,
   allocator, threading library or loader; freestanding does NOT require
   every program to implement an OS (unused services absent, used services
   validated). Containers (ELF/PE-COFF/Mach-O/raw) are explicitly
   unimplemented planned examples; native linker success is never acceptance.
3. **OS contracts not trusted as hardware assumptions.** Gate/kernel half is
   user logic: three external-body obligations (checked declaration, proved
   caller stub correspondence, supplied Lean-proved callee contract at actual
   arguments/results/effects); a name/`assume`/named premise discharges
   nothing; `os_bindung_*` family correctly cited as gap records per IMAGE-ABI
   §§11-12 (verified in tree). Unresolved obligations refuse, never warn.
4. **Exact bytes/mappings and closure boundary.** Validation covers emitted
   unit, driver, binding/runtime bodies, handwritten entries plus the actual
   loaded mapping; bias modes F/P, admissibility classes, patched re-decode,
   loaded-mapping re-check all present. No demand for unrelated kernel bytes.
5. **Concrete references verified in tree:** `EntryState.lean`
   (`stapelOk`/`stapelRW`/`guardOk`), `Syscall.lean`
   (`SysAbi`/`sysAbiGutB`/`dekodiere`), `SyscallPaarung.lean`,
   `Stapel.lean`, `Bild.lean`/`Relokation.lean`, `TableLayout.lean`,
   `Regionen.lean`, `TSO.lean`, `Gleitprofil.lean`, `zielbindung.rs`
   (N562-N567), `bau.rs::nolibc_haken`, `start.nolibc`, `metall.ld`,
   N571/N572/N573/N574/N575-N577, M140, C186/C187. Absent `GateStub` module
   confirmed by grep: candidate correctly books it as pending lane-346 work
   instead of citing it. All IMAGE-ABI section cites (§§1,4,5,9,10,11,12,13)
   match actual headings; QUELLBRUECKE §4 cites match.
6. **Optimiser/central consistency.** IR cited as lane-287 PENDING per
   OPTIMIZER.md §2 (matches tree); friend-reserved files
   (`X86/OptimizationRules.lean`, `OptimizationWitnesses.lean`) untouched and
   reserved; cache keys extend design §8 list (adds bindings); central ledger
   `DIRECT-COMPILER.md` untouched in PATCH; AGENTS.md §3 portability
   requirements (arbitrary-OS profiles, freestanding, generic semantics,
   checked profiles, bindings with user obligations, full final-byte/entry/
   support/mapping validation) all addressed. Other ISAs explicitly excluded.
   Claim boundary clean: PROPOSED vs ACCEPTED marked throughout, no
   implemented-support or whole-compiler-closure claim.
7. **Hygiene.** `git diff --check` clean, `git status` clean (review used
   `.tmp/review` copies; nothing else touched). Design-doc addition is §12
   after §11, no collision. Documentation-only: no Lean/Rust build owed, and
   none claimed.

## Findings

None blocking. Minor non-material note (not a repair item): §2 names a
`main`/`argc/argv/envp` hosted entry shape as profile data; this is a
PROPOSED description of what a profile states, not a claim about an existing
implementation, so nothing follows from it.

## Verdict

VERDICT: ACCEPT
