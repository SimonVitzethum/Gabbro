# MUSE-REPORT-86: syscall checker (PLAN-SYSCALL.md lane S5)

Branch: `muse/86`. Rust lane. No Lean changes (`./lean-bau` green, see §7).

## What was built

The `syscall` item parses, checks, calls like an `extern fn`, and is refused
at the emitter. `P042` is issued nowhere and left the tree with its sentence.

**Parser** (`crates/gabbro-syntax`): `SyscallDecl` + `SyscallPaarung::Annahme |
Kernel` (`ast.rs`); `ItemArt::Syscall` wired into `name()`/`benennung()`;
`syscalldecl()` + `sysregs_in()` + `sysregs_out()` + `errmaps()` (`parse.rs`),
replacing the `P042` skip-and-refuse arm. Speech test rewritten
(`syscall_wird_gelesen`: `=` and `:` bindings, `kernel` tail, `entry syscall`
still an entry).

**Checker** (new pass `crates/gabbro-check/src/syscall.rs`, wired in `lib.rs`
as a helper pass like `geteilt`):
`N063` duplicate in-register, `N064` out register clobbered, `N065` every
parameter bound exactly once (3 sub-cases, 1 code), `N066` only x86_64 general
registers (the 16 GPRs), `N067` errors map total (4 directions, ONE issuance
site), `N068` `kernel` refused ("kernel pairing not implemented yet"),
`A006` sealed arch (anything but `x86_64`). Reused existing codes in
`namen.rs`: `A005` (syscall arch against declared arches, R16 preserved),
`N004`/`N005` (named assumption declared and falsifiable), `N001` duplicates
via `auswahl` (per-arch, like `fn`), `N028`/`N029` via the fallibility map.

**Call sites reuse the `extern` path**: `Signatur` (+ `or R` channel) in
`Umgebung`, call-graph node with declared effects and contract edges
(`aufrufgraph.rs`), `H007` foreign snapshot (`FremdEffekte::aus_syscall`,
`geteilt.rs`), identical `let … else` lowering (`emit.rs` signature map).

**Emitter**: units carrying a syscall are refused with `C001` (stub is S6);
`korr_form` and all item walks classify `Syscall` (no `_` arms added).

**Certificate**: `zeugnis.rs` books a `syscall` `Fremd` line (abi, arch,
number, counterpart) and a `syscall` row in `EINORDNUNG`.

**Probe program**: `sonden/sonde_write.c` for `linux_write_contract` (pipe
round-trip + EBADF + empty transfer, `--kaputt` control that must fall,
`--runden`/bare count capped like the date probes); register row 51 (`P4`);
`SONDEN_MIT_PROGRAMM` entry; `MARK_QUOTE` (17,50)->(18,51); floor teeth
recomputed (eleven->twelve newest, stress 87->94, same standing rules).

**Probes**: `beispiele/74-syscall-schreiben.gab` (checks clean incl. a call,
falls only at emit with exactly one `C001`); gift `797` rewritten to pin the
`C001` emission refusal (was `P042`); new poison `802` (`N063`), `803`
(`N064`), `804` (`N067` target), `805` (`A005`), `806` (`N068`), `807`
(`H007` via syscall, mirrors `796`), `808` (`N065`), `809` (`N066`), `810`
(`A006`), `811` (`N067` dup errno), `812` (`N067` no channel), `813`
(`N004` via syscall).

**Documents**: `SYNTAX.md` §12.1 + §1 + State table (P042 wording replaced,
code names added, `sonde_write` in the example); `SONDENDECKUNG.md` (row 51,
18/51, P4 18); `PLAN.md` (A 57, A_p 18/51, Vorbedingungen 19); `TODO.md`
(Item-Arten 25); `README.md`/`DONE.md` census re-booked to measured
(74 / 568 / 311 / 165, strikethrough style).

## New definitions/theorems (all Rust; no Lean)

- `ast.rs`: `SyscallDecl`, `SyscallPaarung`, `ItemArt::Syscall`.
- `syscall.rs`: `pass`, `registerkarte`, `fehlertabelle`, `bauart`,
  `REGISTER`; codes `N063 N064 N065 N066 N067 N068 A006`.
- `saetze.rs`: `syscall.erklaerung` (replaces `parser.syscall-bevor-s5`).
- Extended (no new codes): `A005`/`N004`/`N005`/`N001`/`N028`/`N029`/`H007`/
  `E008` (graph)/`K003` (same-as-extern)/`C001` for syscalls.
- `sonden/sonde_write.c`: probe program for `linux_write_contract`.

## Verification

- `./cargo-pruef`: exit 0, 0 failing (final run after all edits).
- `./lean-bau`: `Build completed successfully (50 jobs).` (no Lean changes).
- `./emission-pruef`: red, PRE-EXISTING drift (marks 70/73/2/1/4 vs measured
  73/8/132/roots/2; none of my files emit — `gabbro emit` exits 1 with empty
  output on all of them; no syscall items outside my files by grep).
- Green guardians: kennungen, saetze (55), klauseln (modulo pre-existing
  `zucker`), sondendeckung (ALL PASS 18/51), grammatiktafel (0/226, was 2),
  syntax.sh (ALL PASS), konstrukte, gruende, reichweite, deckung,
  schablonen, manifest-side sondendeckung teeth.
- Red at base, untouched: vergabe (22/77 vs 20/68 — my lane contributes
  zero: no new candidate, no probe on a candidate), englisch (7905/7881,
  1085/1069, main.rs:713 sink), sondendeckung was red-by-me then fixed,
  emission (above), sonden.sh 5 WIDERLEGT (timing-calibrated date probes on
  this machine, independent C programs), todo 5 BEFUNDE (other lanes' stale
  prose), zahlen ~17 BEFUNDE (mixed drift; my six numbers updated, rest
  decomposed in §5), mutiere-pruefer --anker speech (Baumstand synthetic
  case + 20 dead anchors, all in files I never touched: 17 lean.rs,
  paarung.rs, and namen.rs/aufrufgraph.rs lines changed by earlier lanes —
  verified by grep), klauseln `zucker` (PLAN-BITS lane).

## What remains open (for S6/S7 and the tree)

- The stub template + `CForm` ruling (S6); the `kernel` pairing check (S6);
  the buffered-writer corpus example (S7); `entry syscall` rename question
  (S1 decided context-keyword, kept).
- Syscall `requires`/`ensures` are parsed, stored in the `Signatur`, and
  scanned for contract calls/edges, but no pass type-checks them yet (same
  gap `extern fn` contracts do not have — extern contracts ARE... actually
  extern contracts are equally unchecked bodies; the S7 flush-proof will
  need contract checking).
- No cost model for syscalls (callers with `costs` meet `K003`, exactly as
  for costless `extern fn`); no linear-mark tracking through syscall params.
- `regs out` pairs refused at the parser (documented §12.1); two identical
  out registers not refused by any code (booked in the Satz vorbehalt).
- `nummer` non-constant accepted (read by the stub later); errno side not
  held against a kernel table (named hardware outcome by design).

## What I believe is wrong in the task / specs

1. **SYNTAX.md §1 vs §12.1 disagree on the register spelling.** The
   production line says `regbind` (`:`) for both maps; every written example
   (PLAN §1, §12.1, gift 797, speech test) writes `rdi = fd` and bare `rax`.
   I implemented the examples (`=` or `:` in, bare out) and documented the
   split in §12.1 and the parser. The §1 production line still says
   `regbind` — S6 should fix the line, not the parser.
2. **"`assume` names a falsifier that exists (existing rule)"** has no
   existing checker rule that checks falsifier EXISTENCE — `N056`
   deliberately does not require resolution (probes are external programs).
   I implemented the `N004`/`N005` shape (assumption declared + falsifiable,
   SYNTAX §12.1's words) and left probe existence to the manifest/sonden
   machinery, which is where the tree decided it lives.
3. **`errors` "total over the listed errnos"** is vacuous as written (the map
   itself lists them); the checkable content is exactly-one-arm-per-errno
   plus channel membership, which is what `N067` holds.
4. **Stale prose found, not mine, left alone**: SONDENDECKUNG "Six rows"
   (17 P4 rows), TODO deutsch/Verweise drifts, emission marks, PLAN "four
   buckets over all 45". Touched only booked numbers my lane moves.
