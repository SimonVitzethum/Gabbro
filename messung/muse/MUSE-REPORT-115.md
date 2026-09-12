# MUSE-REPORT-115: align the syscall pairing with the recording `GutO`

## What was done

All work is in `grammatik/Grammatik/SyscallPaarung.lean` (already imported in
`grammatik/Grammatik.lean`; no import change needed).

1. **Restated `PaarGut`** as exactly the per-axiom instance of the current
   `GutO` (frame of `D.aschreibt a`/`D.agschreibt a`, unchanged held locks,
   and the conditional recording clause over `axiomSpur` with the same
   seven-part existential as `Satz.lean`), **plus** the decoded user contract
   (`Pu -> Qu` over `antwortInt (dekodiere …)`) as a second conjunct.
   The old third clause `spur = spur` is gone.
2. **Re-proved `syscall_paarung`** with the aligned kernel premise `hKeff`:
   frame + held locks + the same conditional recording (the kernel records
   the same `axiomSpur` events). Two new link premises `hEu`/`hEuG`
   (`u.Eu = D.aschreibt a`, `u.EuG = D.agschreibt a`) widen the kernel frame
   (`Ek ⊆ Eu` via `hsub`/`hsubG`) to the declared axiom frame. Every premise
   is consumed: `hnum`/`habi` transport the behaviour, `hreq`/`hKcon`/`hens`
   the contract legs, `hsub`/`hsubG`+`hEu`/`hEuG` the frame widening,
   `hKeff` frame/locks/recording, `hO` the oracle tie.
3. **Recording fixture.** `swO` now bumps the slot **and** records
   `axiomSpur [()] [] () [] σ.haelt` (complete domains, empty guard trace,
   admitted since `swD` guards nothing); `swKbeh` carries the same concrete
   spur equation; `swK.Qk` was weakened from full-world equality to
   slots-equality so the postcondition allows the extra trace
   (success: slots equal the bumped store; EBADF: slots unchanged).
   `swEff` proves the new `hKeff` shape (existential over
   `[()]`/`[]`/`[]`); `swO_trifft` proves frame by
   `rahmen_storeSlot.trans (rahmen_gleich …)` with `haelt`/`spur` by `rfl`.
   New `swEu`/`swEuG` prove the `Eu` coincidence (`rfl` / `nomatch`).
   `swEns` EBADF leg generalized from `σ σ` to `σ σ'` (worlds unconstrained
   by `Qu`).
4. **Re-proved** `syscall_paarung_zeuge` (now ten premises) and kept
   `syscall_paarung_abgelehnt` unchanged in statement (frame counterexample
   outside the empty `Eu`; still valid under slots-based `Qk`).
5. **New `paarung_gibt_gutO`**: a per-axiom family of the pairing
   frame/recording premises (`hnum`, `habi`, `hsub`, `hsubG`, `hEu`,
   `hEuG`, `hKeff`, `hO`) over all `a : D.Ax` yields `GutO O`. The contract
   legs are deliberately **not** premises: `GutO` needs only
   frame/recording, so including them would leave premises unused (rule 3);
   the full pairing gives `PaarGut`, whose first projection is the `GutO`
   instance. One `Grund` type is fixed for the whole declaration (covers the
   one-axiom witness).
6. **New `paarung_gibt_gutO_zeuge`** on `swD` (whose only axiom `()` is the
   toy `write` syscall): all eight family premises proved jointly by casing
   on `a = ()` to the `sw*` lemmas, plus non-degeneracy (`schreibt` + a
   `storeSlot` memory move `0 -> 1`).

## Exact new/changed names

- Changed: `PaarGut`, `syscall_paarung`, `swK` (`Qk` slots-based), `swO`,
  `swKbeh`, `swEff`, `swO_trifft`, `swEns` (EBADF leg), `syscall_paarung_zeuge`.
- New: `swEu`, `swEuG`, `paarung_gibt_gutO`, `paarung_gibt_gutO_zeuge`.
- Unchanged: `syscall_paarung_abgelehnt`, `swNum`, `swAbi`, `swReq`,
  `swSub`, `swSubG`, `swCon`.

## Last `./lean-bau` result line

`Build completed successfully (61 jobs).` `./lean-probe` on the file:
`== 0 error(s) in the COMPLETE output`. All `#print axioms` (including the
two new ones) report `[propext, Classical.choice, Quot.sound]` only.

## What remains open

- `hKeff`/`hKcon` remain hypotheses about the kernel implementation.
- `paarung_gibt_gutO` fixes one `Grund` type across axioms; per-axiom reason
  types need a type family generalization.
- Emitter/stub and ghost-carrier work (lanes S3/S6) untouched.

## Believed-wrong in the task

Nothing structural. Two shapings to record: (a) the witness stays on `swD`
rather than `ReferenzB`, because `refD` has `Ax := Empty` and admits no
syscall — the task's own witness line ("the write-like entry of the current
file, extended to a declaration whose only axiom is that syscall") describes
exactly `swD`; (b) `paarung_gibt_gutO` omits the contract premises
(`hreq`/`hens`/`hKcon`) since `GutO` does not need them — including them
would violate the every-premise-used rule. The `hEu`/`hEuG` equalities are
genuinely needed to connect `Ek ⊆ Eu` (PLAN-SYSCALL §2) to the declared
axiom frame that `GutO` speaks about.
