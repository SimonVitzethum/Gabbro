# MUSE-REPORT-85: syscall pairing theorem (PLAN-SYSCALL lane S4)

## What was built

New file `grammatik/Grammatik/SyscallPaarung.lean` (registered in
`grammatik/Grammatik.lean`), proving the pairing theorem of
`dokumente/PLAN-SYSCALL.md` section 2 item 4.

- `KernelEintrag D Params`: kernel dispatch entry -- call number, `SysAbi`
  register map, proved contract (`Pk` requires, `Qk` ensures over the raw
  `Int` answer, `Ek`/`EkG` effects).
- `UserSyscall D Params Grund`: user-side declaration -- number, `SysAbi`,
  errno table, ok-range `lo`/`hi`, declared contract (`Pu`, `Qu` over the
  DECODED `SysAntwort Int Grund`), effects `Eu`/`EuG`.
- `antwortInt`: forgets the decoder's range proof (`ok v` to `ok v.val`).
- `PaarGut D a O u`: the oracle premise for ONE axiom in `GutO`-style
  shape -- `Rahmen Eu`, unchanged locks and trace, plus the decoded user
  contract whenever `Pu` holds at entry. Deliberately per-axiom, not a new
  global assumption.
- `syscall_paarung`: from `hnum` (same number), `habi` (same register
  map), `hreq` (`Pu -> Pk`), `hens` (`Qk -> Qu` after `dekodiere`),
  `hsub`/`hsubG` (`Ek ⊆ Eu`), `hKeff` (implementation keeps kernel frame,
  locks, trace), `hKcon` (implementation delivers `Qk` under `Pk`), and
  `hO` (every oracle answer is a kernel behaviour) -- conclude
  `PaarGut D a O u`. Proof: transport the behaviour along the dispatch
  identity, widen the frame with `Rahmen.weiter`, discharge both contract
  legs. All nine premises are consumed by the proof term.
- `syscall_paarung_abgelehnt`: if the kernel writes a table the user side
  does not declare, a kernel behaviour satisfying `Pk`/`Qk`/`Ek` violates
  the user frame (concrete shape: `fd = 3` open, count `5 <= len = 8`,
  slot bumped `5 -> 1`).

Witness (toy `write`, number 1, user side of PLAN-SYSCALL.md section 1):
`swD` (one offset table, one writing function, one axiom with params
`(fd : .int 0 7, len : .int 0 8192)`), `swK` (requires slot nonzero,
ensures count `<= len` with bump or EBADF `-9`, writes the table), `swU`
(same number/map, `schreibFehler` table, `0..8192`, `result <= len`,
declares the write), `swO` (bumps slot, answers `0`), `swKbeh`.
`syscall_paarung_zeuge` instantiates all eight pairing premises jointly
and adds non-degeneracy: the function writes the table and a `storeSlot`
step moves memory (`0 -> 1`).

## Last `./lean-bau` result line

`Build completed successfully (51 jobs).` -- whole project green,
including the six `#print axioms` lines for the new theorems
(all depend only on `[propext, Classical.choice, Quot.sound]`).

## What remains open

- `hKeff`/`hKcon` are hypotheses about the kernel implementation, not a
  verification: discharging them for a real Gabbro kernel is lane S5/S6
  work (dispatch entry proof over runs).
- The emitter side (stub template, register binding, clobbers) and the
  ghost-carrier wiring are untouched (lanes S3/S6 own them).
- `syscall_paarung_abgelehnt` covers one mismatch shape (undeclared table
  write), not wrong numbers, wrong maps, or weak `Qk`.

## Believed-wrong in the task

Nothing believed wrong. Two deliberate shapings, both within the prose:
(1) the "oracle premise" is concluded per-axiom (`PaarGut`), not as full
`GutO O`, since `GutO` quantifies over all axioms and the pairing is
about one `Ax`; (2) the witness is built on an own toy declaration
instead of `ReferenzB`, because `refD` has `Ax := Empty` and admits no
axiom at all -- the task's own witness description ("toy write-like
entry, number 1") says otherwise, which the standing rule allows.
Contracts hold at their place throughout (entry/exit worlds, actual
environments); no premise quantifies over all contracts, statements, or
expressions.
