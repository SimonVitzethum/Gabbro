# MUSE-REPORT-226: fd + open/read declarations, user-made syscalls (TODO §-1 wave A, L-2)

Branch: `muse/226`. Rust lane. No Lean changes, no `crates/` code changes, no
`saetze.rs` changes, no `MARKE_EMIT*` changes, no emission-script changes.
Touched, exclusively: `beispiele/` (2 new), `beispiele/gift/` (2 new),
`crates/gabbro-check/tests/paesse.rs` (+38 lines).

## 1. Verdict up front

The deliverable stands: the fd carrier plus an open gate and a read gate,
declared entirely in-program (ABI name, number, register map, errno decoding,
costs, effects), checked end to end — declare (checker-clean), call (call
sites checked, costs counted, carrier discipline enforced), emit prototype
(stub + wrappers emitted, `cc` and `clang` accept under `-Werror`).

Deliberately NOT built: any new checker code. `N406`–`N410` stay reserved and
unused. Every defect class at this boundary is already refused by name (§4);
the checker-silent shapes are emitter-refused by design (lane S6, gifts
850–854), and duplicating them in the checker would double-refuse and fight
the documented split. A lane that mints refusals to fill a quota is how the
register grows without meaning. If the reviewer wants codes anyway, §4 names
exactly where each would land and why each was declined.

`./cargo-pruef`: `== exit 0; failing tests: 0` (two full runs, see §3).
`./emission-pruef`: `== exit 0` pre-commit (untracked files are not counted
yet; post-commit the merger re-measures `MARKE_EMIT` 117 → 119, see §6).
`./lean-bau`: NOT run — no file under `grammatik/` is touched (`git status`
proves it); the merge gate builds Lean anyway.

## 2. Exact names

**`beispiele/149-fd-offen.gab`** — module `beispiel::fd_offen`: `opaque type
Fd = u32` (the carrier); `const MAXLEN : u64 = 1024`; `reason OpenError`
(`NotFound = 2`, `Denied = 13`, `Exists = 17`, `exhaustive`); the reused
assumption pair (`linux_write_contract` / `sonde_write`, byte-identical to
74/90/96 — §5); `syscall gate_open(path : ptr<normal, r> u8, pathlen : u64,
flags : u64, mode : u64) -> u64 or OpenError` (`abi linux arch x86_64 number
2`, `rdi`/`rsi`/`rdx`/`r10`, `EBADF`-family map, `requires pathlen <=
MAXLEN`, `ensures result <= 4294967295`, `effects { reads path }`, `costs <=
40 ops`); `impl fn oeffnen(...) -> Fd or OpenError` (the one wrap).

**`beispiele/150-fd-lesen.gab`** — module `beispiel::fd_lesen`: `Fd`;
`MAXLEN`, `CAP = 64`, `SCHRANK = 1048576`; `static mut EIMER : [u8; 64]`;
`reason ReadError` (`BadFd = 9`, `Interrupted = 4`, `Invalid = 22`,
`exhaustive`); reused pair; `extern fn leser_haengt() -> never` (watchdog,
the 96 shape); `syscall gate_read(fd : Fd, buf : ptr<normal, w> u8, len :
u64) -> u64 or ReadError` (`number 0`, `requires len <= MAXLEN`, `ensures
result <= len`, `effects { writes buf }`, `costs <= 40 ops`); `impl fn lies`
(single read, honest `writes buf` — no `pure` fiction); `impl fn zaehle(fd :
Fd) -> u64 or ReadError` (bounded count up to `SCHRANK`, `forever` +
`per_pass bounded 1024 ops` + watchdog + `progress`, the 96 idiom).

**`beispiele/gift/1067-fd-falscher-traeger.gab`** — `-- erwartet: D004`,
measured exact set `[D004]`: modules `tor` (carrier + user-made gate with
fully invented constants — `myabi`, number `100`, no errno names) and
`anwender` (cross-module `gate_lesen(anzahl, 8)` with a bare `u32` where
`Fd` is owed). The cpu/dev mixup, at the gate.

**`beispiele/gift/1068-fd-wird-gerechnet.gab`** — `-- erwartet: D003`,
measured exact set `[D003]`: `maske` OR-ing a flag word into `Fd`; `scheck`
(pure `u32` passthrough beside it) stays green, pinning what wrappers may do
instead. Gate with invented constants (`myabi`, `101`) so the file says what
the value was for.

**`crates/gabbro-check/tests/paesse.rs`** — `fn fd_gates_are_user_made`:
`faellt_nicht` over a fully invented gate declaration (no OS token in it —
the checker-keys-on-no-table pin) and `faellt_genau(…, &["D003"])` over fd
arithmetic. Ran green standalone (`1 passed … 145 filtered out`).

Gift numbers 1069–1071 and codes N406–410 stay free. Example numbers 147/148
were left for the lanes that own them.

## 3. Verification

- `./cargo-pruef` full runs, twice `== exit 0; failing tests: 0`. The
  first run overlapped file creation, so it is not a clean baseline; the
  measured run is the second, launched with every §2 file in place (the
  `paesse` binary rebuilt newer than its source, corpus files read at test
  runtime).
- Binary-level, each recorded: 149 and 150 check with `0 errors, 0 hints`;
  both emit; both emitted files pass `cc -std=c11 -Wall -Wextra -Werror
  -fsyntax-only` AND `clang` the same way. The emitted prototypes carry the
  carrier as its carrier (`uint32_t fd`, `uint32_t *_wert`).
- 1067/1068: `gabbro emit` (CLI) refuses via the checker fault — no C, so
  `n_emit_g` does not move.
- `python3 instrumente/pruefe-saetze.py`: `416 Kennungen, 170 Saetze, 55 ohne
  Satz` — the 55 un-sentenced are the pre-existing count (lane-114 report:
  130/55/0 lineage), nothing added, nothing owed (no new codes).
- 660/661 untouched in tree and verdict: 660 still falls `N046`, 661 still
  `N052` (suite asserts both). The syscall path supersedes NEITHER file —
  said loudly, as tasked: the `extern fn` border still refuses variadics and
  path-in-data shapes, and should; the user-made gate is the alternative
  route for open/read, not a re-verdict of the old probes.

## 4. Why no new refusal — the defect table

Probed empirically with the built binary (scratch files in `.tmp/`,
uncommitted). Each class already has its name:

| defect | refused by | at |
|---|---|---|
| dup in-register / clobbered out / unbound param / unknown register | N063/N064/N065/N066 | check |
| mistargeted errors map (4 shapes) | N067 | check |
| `kernel` pairing / sealed arch / arch mismatch | N068 / A006 / A005 | check |
| costless gate | N322 | check |
| `rax` in-binding / wrong out-register / foreign abi / named result / unfolded number | C180/C181/C182/C183/C184 | emit, by S6 design (gifts 850–854 document the split) |
| undeclared param type | C001 at emit (generic "no C") | emit |
| count where `Fd` owed, cross-module | D004 (+M101 on width) | check, at the call |
| arithmetic on `Fd` | D003 | check |
| non-exhaustive reason match at `let…else` | M123 | check |
| `pub syscall` | P041 (no `pub` on the item) | parse |

Declined, each with its reason: checker duplicates of C180–C184 (double
refusal, fights the S6 split); a checker ban on named results (would close
`-> Fd` forever — against this lane's own direction and lane 233's); a ban
on aliased numbers (two names, one gate with different contracts is a
judgement call, and the stub materializes each map honestly); a `pure` +
writable-pointer refusal (would rewrite `extern fn` semantics and move 74/96
— other lanes' files). What is left silent is either designed (in-module
conversion, §7) or owned elsewhere (§7).

## 5. Assumption reuse, stated plainly

149/150/1067/1068 redeclare the 74/90/96 pair byte-identically
(`linux_write_contract`, text and `sonde_write`). Same name, same text, same
probe: no new obligation (`N024` neutral), no new quota row
(`pruefe-sondendeckung.py` denominator keyed by name — unchanged), no new
`sonden/` program. The historical name says "write" while the gates are
open/read; what travels is the machine-answers-its-gates contract the three
files share. A per-gate split is honest follow-up, not this lane (it needs
either new `sonden/` programs — not my files — or a register row I may not
add).

## 6. OS-freedom grep-proof

`crates/` + `grammatik/` code diff: EMPTY (no code changed anywhere). Every
OS-looking token in the lane diff lives in a user program (`beispiele/`) or
a test (`tests/`), as the task's own trace rule contemplates:

- 149: `abi linux`, `number 2`, `rdi`/`rsi`/`rdx`/`r10`/`rax`/`rcx`/`r11`,
  `ENOENT`/`EACCES`/`EEXIST` + the reused `linux_write_contract` pair — all
  in the example, each header-marked as program constants, none a tree fact.
  No `CLOCK_*`, no `O_*`/`AT_*` flag constants (flags ride as parameters).
- 150: same class (`number 0`, `EBADF`/`EINTR`/`EINVAL`, reused pair).
- 1067/1068: invented throughout (`myabi`, 100/101, empty errno maps) apart
  from the reused pair name and the mandatory `regs` syntax (a `syscall`
  cannot be written without a register map; no VALUE in it is OS-fixed).
- `paesse.rs` addition: `myabi`/100 only; invented names throughout.

Corpus diff: +4 files, 0 verdict moves (suite green both directions).
Emission count: pre-commit `./emission-pruef` exit 0 (untracked files are
invisible to its `git ls-files` enumeration); post-commit the two emitting
examples count, so the merger re-measures `MARKE_EMIT` 117 → 119 with the
dated reason this report is. Gifts do not emit (refused), `MARKE_EMIT_G`
stays 18. `MARKE_EMIT_M/N/P/L/X` untouched.

## 7. CUTs and measured quirks (all filed, none built — wrong files)

1. `ensures` with a `const` bound does not propagate to the caller's
   `return` position; the same bound as a literal does (149: `MAXFD` vs
   `4294967295`, measured both ways). `m1.rs` — lane 224's file.
2. The emitter's unsignedness collector sees plain `let` but not `let…else`,
   so narrowing a call binding keeps `>= 0` over `u64` and `cc -Wtype-limits`
   refuses; the plain-`let` copy in 150's `zaehle` works around it.
   `emit.rs` — frozen for this lane.
3. In-module `u64`→`Fd` implicit conversion is silent by design (`D004`'s
   wall is the module boundary). Inside one module the mixup discipline is
   convention: convert once, at the gate wrapper, into `Fd` — the pattern
   both examples follow.
4. `errors {}` must stand even for infallible gates (positional, `P001`
   otherwise) — found while drafting 1067/1068, kept as empty maps.
5. Ghost OS state (`os.fds`-style effects, `requires Open(fd)`) is not
   expressed: effects over tables/params cover what the demos need; the
   ghost-carrier half is lane 233's Lean model plus a `wirkungen.rs` shape —
   neither mine.

## 8. Where the task text was wrong

- "`ast.rs` (fd carrier…)": no AST change was needed. `opaque type Fd =
  u32` is the carrier, nominal checking (`N030`/`D003`/`D004`) already holds
  it, the stub lowers it through its carrier. `ast.rs` untouched.
- "checked end to end (declare → call → emit prototype)": holds, with one
  asymmetry the task should know — a gate ANSWERING `Fd` checks clean but
  dies at `C183` (named results have no range to check against). Gates
  answer integers; wrappers carry the carrier. Demonstrated, documented in
  both example headers.
- Emission requires `abi linux` in the user text (`C182` refuses every other
  pair — correctly, the template IS one machine's instruction). OS-freedom
  therefore means: the tree assigns no ABI, number, register meaning or
  errno — the program assigns all four. That is what 149/150 (real user
  data) versus 1067/1068 + the `paesse` test (invented user data, same
  shape, same verdicts) jointly prove.

Co-Authored-By: muse-agent-226 <muse-agent-226@noreply.invalid>
