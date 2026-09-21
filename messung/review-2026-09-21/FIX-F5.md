# Fix lane F5 — fd carrier and foreign-call gates (reviews G04 F2–F6, G10 F5)

*2026-09-22, branch `review-0921-integration`, built and run locally (fisch unreachable).
Commit: see `git log` (one commit, "Fix lane F5").*

## What was fixed

### 1. Example 149: the `open` gate's registers and the NUL path (G04 F2, HIGH; Simon's decision)

- **Registers.** `regs in { rdi = path, rsi = flags, rdx = mode, r10 = pathlen }` — Linux
  x86_64 `open(path, flags, mode)`; `pathlen` rides in `r10`, which `open` does not read
  (`N065` binds every parameter once). **Measured on the emitted C**, with a harness that
  includes the generated unit and calls `gate_open` on `/etc//passwd` (13 bytes with its NUL,
  so `13 & 3 == O_WRONLY` if the length lands in the flags) as an unprivileged user:

  | emitted C | `gate_open("/etc//passwd", 13, O_RDONLY, 0)` | missing path |
  |---|---|---|
  | before (HEAD) | `ok=0 grund=13` (**`Denied`** — the length arrived as `O_WRONLY`) | `grund=2` |
  | after | `ok=1 fd=3` | `grund=2` |

- **The NUL-terminated path is a NAMED CALLER ASSUMPTION.** `spec fn
  path_nul_terminated(path, pathlen) = pathlen >= 1 && path[pathlen - 1] == 0`; the gate and
  the wrapper `oeffnen` both `requires pathlen <= MAXLEN, pathlen <= lenof(path),
  path_nul_terminated(path, pathlen)`. `gabbro obligations beispiele/149` lists it by name:
  `oeffnen :: gate_open requires #3  V  path_nul_terminated(path, pathlen)`. **The checker
  does not decide it** (no rule reads a byte's value; not cheap): it is user logic, counted.
  The frame's LENGTH is decided (item 2). It does not enter the goal's hardware assumptions
  (149 does not export: `LG001`), so `Spec.lean`'s list is unchanged; recorded as `OFFEN.md` O23.
- **Does the emission check execute the gates?** No. `pruefe-emission.sh` stage 9 only
  compiles (`cc -c`) every emitting file; no stage links or runs 149/150. The runs above are
  this lane's own harness (scratch, read-only opens and a pipe), not part of any guardian.

### 2. The read frame is tied to the object — `N463`/`N464` (G04 F3, MEDIUM)

- **Measured first:** with the HEAD checker, `lies(fd, EIMER, 1024)` over the 64-byte `EIMER`
  of example 150 checked **clean** (0 errors; the only trace was an open `V` row
  `len <= MAXLEN`).
- **New clause form** `requires x <= lenof(p)` (or `<`): `lenof` of a pointer parameter is the
  number of elements the caller's object holds from the pointer on.
- **`N464`** (`syscall.rs`, `buffer_bound`): a `syscall` parameter that points at numbers is a
  byte buffer (`u8`/`i8` pointee — the kernel counts bytes, `lenof` elements) and the gate
  carries such a clause over one of its integer parameters.
- **`N463`** (`m1.rs`, `transfer_bound_at_call`, in the one funnel every call form reaches): each such
  clause of any callee is DECIDED at the call — an array passed for `p` (it decays there and
  its length is last known) bounds the range of `x`'s argument, with matching element types;
  a pointer passed for `p` must be the caller's own parameter beside its own length parameter,
  under the caller's own identical clause (a parameter name rebound anywhere in the body drops
  out, fail-closed); anything else is refused. The strong reading holds only this clause form;
  every other `requires` keeps `M115`'s weak reading.
- Sentence `syscall.rahmenlaenge` (`saetze.rs`), module `rahmenlaenge.rs`, SYNTAX §12.1.
- Gifts: `1155` (`N464`, 150's old gate), `1156` (`N463`, the measured 1024-into-64 call),
  `1157` (`N463`, forwarding without the clause), `1158` (`N464`, a `u32` buffer). Each falls
  with exactly its code. Positive side: `tests/rahmenlaenge.rs` (14 tests, twins for const,
  literal, strict bound, forwarding, swapped length, shadowed parameter, wider elements),
  and examples 96/149/150.

### 3. Own assumptions and probes for open and read (G04 F4, MEDIUM)

- 149 names `linux_open_contract` (probe `sonden/sonde_open.c`), 150 `linux_read_contract`
  (probe `sonden/sonde_read.c`). Both probes call the gate's own raw number (`syscall(2, …)`,
  `syscall(0, …)`), walk the mapped errnos (open: descriptor in 0..2^32-1 and readable,
  `ENOENT`, `EEXIST`, `EACCES` unprivileged; read: at most `len` into a 64-byte window with the
  guard bytes intact, drain then 0, `EBADF`, `EINVAL` via a short eventfd read), and carry a
  `--kaputt` control. Measured: both exit 0, both controls exit 1
  (`cc -std=c11 -O2 -Wall -Wextra -Werror`).
- `N024` (one probe per obligation per unit) did not block anything: the quota is per unit, and
  both new assumptions come with new programs. `SONDENDECKUNG.md` rows 53/54 (54 rows, 21 with a
  program), `manifest.rs` `SONDEN_MIT_PROGRAMM`, and `pruefe-sondendeckung.py` re-measured:
  `MARK_QUOTE (19,52) -> (21,54)`, tooth SEVEN's smallest newest breaking set 13 -> 14 names,
  tooth EIGHT's stress 101 -> 115 (derivations in the file).
- **The `__builtin_unreachable()` leg is now named by the gate's own assumption**: the emitted
  C reads `hardware (linux_open_contract)` / `hardware (linux_read_contract)`; the
  `syscall.stub` sentence says the unreachable stands under the gate's OWN `assume`.
- Emitted 150 run through a pipe (scratch harness): `zaehle` over 14 bytes answers 14; over a
  closed descriptor answers `BadFd`.

### 4. Lean: the gate contract split (G10 F5)

`FremdRuf.lean` §9 (SATZKARTE §42): `AxPre` (a gate's argument precondition), `AxVertragOP`
(ensures only at calls meeting it; weaker than `AxVertragO`: `axVertragOP_of_O`),
`AufruferPflicht` (the caller's obligation), `fremdruf_gate_gilt_pre`, and the bridge
`hardware_aus_vertragP`: frame + register locality + the restricted premise + raw words outside
every declared result type give the FULL `Zielsatz.HardwareAnnahmen` for a re-dressed oracle
(`mitVorbedingung`) that answers every well-formed call exactly as the machine
(`mitVorbedingung_gleich`). **`Spec.lean` is unchanged** — no Spec diff. Non-degenerate
witnesses on the fixture with an oracle `fdObad` that answers garbage to a read with a
descriptor it never handed out: it meets the restricted premise (`fdObad_vertragP`) and breaks
the full one (`fdObad_nicht_voll`), the ill-formed call breaks the caller's obligation
(`fdPflicht_verletzt`), and the open gate's terminator precondition holds at the start world
and fails after its own marker write. `fdQ` for open no longer promises a nonzero descriptor
(fd 0 is valid); it promises the gate's marker in the answer world (`fdO_open_marke`).
The fixture was NOT widened to example 150's shape (opaque `Fd`, `buf`/`len`): every
environment and fit in the file names the one-parameter read, so it was not cheap.

### 5. Gift 1068's twin, `costs` on `-> never` (G04 F5/F6, LOW)

- `scheck` now `return fd;` (it returned the flag word as an `Fd`); the prose says why.
  Still `D003` only.
- `costs` on `-> never`: **measured that the three shapes already follow one rule**, now
  written down in `namen.never_forever_angenommen`: the bound is the work a call does before
  control leaves for good, the same bound a caller counts. Where Gabbro has the body it is
  checked (a tail call sums its callee's cost: `costs <= 6` over a 7-cost callee is `K001`, 7 is
  clean); where the body is opaque it is required and trusted (`A003`, extern cost rule); over
  an un-leavable `forever` no finite bound exists (`K003` on a written one, and on a bounded
  caller). No verdict changed; pinned by `never_kosten_sind_ein_satz_f5` (`tests/paesse.rs`).
  Gift 1058's comment now points at the `kosten.summation` sentence instead of a lane report.

## Measured results

(`free -g` before each heavy run: 31 GB total, 20 GB available, swap 8 GB, 20 cores.)

| check | result | baseline (F4) |
|---|---|---|
| `cargo test --no-fail-fast` | **71 collections, 1304 passed, 0 failed, 1 ignored** | 70, 1289/0/1 |
| `pruefe-emission.sh` | **ALL PASS** — 37 run, 288 of 288 compile, 2 reverse probes (ASan not run here) | ALL PASS |
| `lake build` (grammatik) | **281 jobs, 0 errors**; `#print axioms gabbro_ziel` = `propext, Classical.choice, Quot.sound`; section 9 uses `propext`, `Quot.sound` | 281 |
| `pruefe-saetze.py` | pass — 442 codes, 183 sentences, 0 invented | 440 / 182 |
| `pruefe-kennungen.py` | ALL PASS | ALL PASS |
| `pruefe-todo.py` | 16 findings | 16 |
| `pruefe-zahlen.py` | 37 findings (same rows; stale bookings moved by the new code/sentence counts) | 37 |
| `pruefe-englisch.py` | red on the same three ratchets (7965/37/5); German-stem identifiers 763 (= base; new identifiers are English) | same |
| `pruefe-sondendeckung.py` | rc 2 at its speech test, the same teeth `NO` as the base | rc 2 |

Cargo and emission were run twice (before and after renaming the new identifiers to English);
both runs gave the numbers above.

## Corpus diff

- Existing tracked files (899 in `beispiele/`, F4's `korpus.sh`): **0 verdict changes** after
  the edits.
- **Three corpus files had to change, and that is a finding, not a paper-over:** with HEAD's
  sources, the new checker refuses `beispiele/96`, `/149` and `/150` with `N464` each (their
  gates took byte buffers bounded only by a ceiling). Each now carries `len <= lenof(buf)` /
  `pathlen <= lenof(path)`; `N463` then holds their calls (`write(fd, WINDOW, 1)` over a
  1-byte array, `lies(fd, EIMER, CAP)` over 64). `messung/schreibprobe/S14` has no buffer gate
  and stays clean.
- New: gifts 1155–1158, each falling with exactly its code.

## What stays open

- `OFFEN.md` O23: the NUL path is a named, counted caller obligation, not a checked fact; the
  goal's premise (c) still quantifies over every argument (the split and bridge are proved
  beside it, run-level coincidence is not); `N464` does not hold `extern fn` byte buffers
  (`beispiele/64`'s `write`); `lenof` of a pointer is decided only where an array decays.
- Example 96's `write` gate still declares `effects { pure }` over a buffer the kernel reads
  (the file calls it a fiction); not changed here.
- Gift 1067 still borrows `linux_write_contract` (a refusal probe; the name is irrelevant to
  what it pins).
- The Lean fixture is narrower than example 150 (no opaque carrier, no `buf`/`len`).
- `pruefe-sondendeckung.py` aborts at its speech test on the base too (rc 2, the same three
  `NO` teeth before and after); not investigated here.
