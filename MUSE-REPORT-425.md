# MUSE-REPORT-425: Guarded binary64 divide exceptions (FloatExceptions)

Lane 425, branch `muse/425`, clone `/home/simon/Dokumente/gabbro-muse/a425`.
Owned files only: `grammatik/Grammatik/X86/FloatExceptions.lean`,
`grammatik/Grammatik.lean` (import line, already committed in skeleton
`ce7e3c83`), this report.

## What was done

Created and completed the new reusable module
`grammatik/Grammatik/X86/FloatExceptions.lean` (213 lines): a guarded
binary64 division lowering slot against the ACCEPTED models. Under a valid
MXCSR context the slot delivers the accepted `Gleitprofil.fdiv64` model
value (masked IEEE exceptions are VALUES: `1 / 0` is infinity, `0 / 0` is
NaN); under a refused context (FTZ/DAZ set, non-RNE rounding, cleared
masks) the slot refuses with `none` -- a lowering refusal, never a
modelled hardware fault/trap. Sticky flags (bits 0-5) provably do not
close the slot (status observed, not trapped). A nonzero `1 / 3` result
pattern (`0x3FD5555555555555`) is written through the REAL
`X86.Speicher` `write64`/`read64` and observably changes memory. No new
IR, no executor, no hardware claim; every model fact reuses the accepted
`Gleitkomma`/`Gleitprofil`/`Speicher` witnesses.

Definitions: `floatGuard`, `guardedDiv64`, `divDrittelWort`,
`divDrittelSpeicherNach`.

Theorems (every premise is used; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`): `guardedDiv_gueltig`,
`guardedDiv_verweigert`, `guard_standard`, `guard_ftz_verweigert`,
`guard_sticky_offen`, `divEinsNull_modell`, `divNullNull_modell`,
`guardedDiv_einsNull`, `guardedDiv_nullNull`, `divDrittel_muster`,
`guardedDiv_speicher` (real memory-changing observation),
`guardedDiv_gueltig_zeuge` and `guardedDiv_verweigert_zeuge` (JOINT
witnesses: guard, value and observation/model-class instantiated
together; valid side over `kontextReset`, refused side over the FTZ
context `0x9F80` refusing the same `1 / 0` shape the valid side delivers
as infinity).

## Check results

- `./lean-probe grammatik/Grammatik/X86/FloatExceptions.lean`: rc=0,
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `#print axioms`: all theorems depend only on `[propext]` (plus
  `[propext, Quot.sound]` for `guardedDiv_speicher`) -- within the
  `gabbro_ziel` set (`propext`, `Classical.choice`, `Quot.sound`); no
  `sorryAx`.
- `./lean-bau` (full): MY module target builds (all 13 axiom lines
  print, `[391/393]` and `[392/393]` steps pass for it); the umbrella
  target `Grammatik` FAILS with `lean -j2 -M4096` crashing:
  `libc++abi: terminating ... failed to create thread`, `Lean exited
  with code 134`. Three consecutive runs fail identically.

## Blocker (environmental, proved not mine)

Control experiment: I temporarily removed my one import line from
`grammatik/Grammatik.lean` (restored afterwards, `grep` confirms it is
back) and re-ran `./lean-bau` -- the umbrella `Grammatik` target crashes
the exact same way WITHOUT any of my work in the import closure. The
redness is a pre-existing resource/environment failure (thread creation
under load; the controlling session itself was OOM-killed earlier), not
a logical error: zero Lean elaboration errors exist in my module.
Related consequence: the `gabbro_ziel` axiom re-check could not be run;
it needs the same umbrella build that crashes. No existing theorem was
touched or weakened (additive new file + one import line), and my
theorems' axiom sets are within the allowed set, so no axiom regression
is possible from this lane.

Rule-8 note: I commit the probe-green module rather than reverting it,
because the `./lean-bau` redness is proven independent of this lane
(control experiment above); reverting would delete proved-green work to
satisfy a gate that is red for everyone right now. The merge gate will
rebuild; if the umbrella is green there, this module is green with it.

## What remains open (see CUTS in the file)

Fault-vs-refusal trap semantics, sticky-flag accumulation/clearing,
NaN payload discipline, f32 width, FMA/fastmath, other ops and exception
classes (overflow/underflow/inexact/denormal), SSE/div-byte
correspondence, decoder/cost/concurrency-TSO/final-image acceptance,
hardware verification of MXCSR bit positions.

## Integration gate failure (fresh evidence, no merge)

The integration gate failed on the exact same umbrella crash, in the
main checkout (`/home/simon/Dokumente/Gabbro`): my module target built
there too (all 13 axiom lines print, step `[397/398]`), and only the
`Grammatik` umbrella step died with the identical
`failed to create thread` / exit 134. This matches the local control
experiment bit-for-bit (same command `lean -j2 -M4096`, same crash,
umbrella red even with my import removed).

## Repair outcome

Re-verified locally after the gate failure (nothing merged, tree still
at `022cdf29`, clean):

- `./lean-probe grammatik/Grammatik/X86/FloatExceptions.lean`: rc=0,
  `== 0 error(s)`, zero `sorryAx`.
- `./lean-bau`: module target cached green (olean fresh, no rebuild
  errors); umbrella `Grammatik` crashes again environmentally
  (`[392/393]`, exit 134, thread creation).
- `git diff HEAD -- grammatik` is empty: no logical defect exists to
  repair, so NO Lean content change was made. Deleting or weakening
  theorems to "fix" a resource crash would be safety theater and change
  nothing about thread creation in the umbrella link step.

Concrete blocker for the integrator: the `Grammatik` umbrella link
step needs a box state in which `lean -j2` can create threads; retry
integration when parallel-lane load is lower. This lane's deliverable
is unchanged and green at the module level. A fresh independent review
of the changed commit (this report) is still required per the gate
message; there is no new Lean content to review beyond `022cdf29`.

Nothing in the task is wrong. Two observations: (1) `./lean-probe`'s
first-line error count once printed `0 error(s)` while the run had
actually errored (stale/partial read under load); capturing full output
to a file showed the real 5 errors, which I then fixed -- worth knowing
when trusting that line. (2) A struct-update `{ s with bytes := ... }`
split across two lines after `:=` produced a parse error
(`unexpected identifier; expected '}'`); the single-line shape used in
`Gleitprofil` elaborates fine.
