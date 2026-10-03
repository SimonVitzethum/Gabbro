# MUSE-REPORT-871: Strength reduction rule (imul-by-8 to shl)

## What was done

New file `grammatik/Grammatik/X86/OptStrengthRed.lean` (~380 lines) plus one
import line in `grammatik/Grammatik.lean`. It states the DESIGN section 7
strength-reduction row as a generic rule lemma over arbitrary values with
validator-decided side conditions, and proves value/fault/observation
preservation at the source `eval`/`execEnd` level. Only reused vocabulary
(`Typen`, `Syntax`, `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`,
`X86.Ganzzahl`, `X86.ShiftLogic`, `X86.MulDiv`, `X86.StaerkeReduktion`);
no new machine, no new decoder, no source/checker/Spec/goal/emitter edit,
no friend-reserved optimiser file touched, no diagnostic/gift/example/CLI
numbers, no MARKE_EMIT changes.

Certificate shape: `StrengthCert` (`cfTot`, `breiteOk`, `keinFP`,
`keinSDiv` — recomputed liveness/range citations plus the two shape
exclusions) with admission Bool `staerkeZulassen` (conjunction; a refused
optional optimisation falls back to another certified translation, never
to a warning).

## Exact names of new definitions/theorems

- `StrengthCert`, `staerkeZulassen`
- §1 flag/fault identity: `imul_cf_gleicht_of` (IMUL locks CF = OF to the
  signed carry), `shl_drei_trag` (SHL-by-3: OF `none`, CF = bit 61),
  `cf_unterscheidet_imul_shl` (CE-6 numeric witness `2^62`: same value,
  IMUL CF `true` vs SHL CF `false`, by `decide`)
- §2 refusals: `staerkeVerweigert_cf`, `staerkeVerweigert_breite`,
  `staerkeVerweigert_float`, `staerkeVerweigert_sdiv`,
  `probe_staerkeZulassen_ok/cf/float`
- §3 values: `acht_ist_zwei_hoch_drei`, `mul_acht_shl_drei` (generic
  `a * 2^3 = a << 3` over arbitrary nonneg values, reuses `mul_pow2_shl`),
  `probe_mul_acht`, `staerkeWort_acht` (word readback under checked
  nonoverflow), `probe_staerkeWort`
- §4 `OptStrengthRed_verbindung`: `Endblock.bind` connection concluding
  jointly (1) bound-value preservation, (2) `execEnd` outcome equality
  (same faults, same successor worlds/envs — hence contracts at their
  place, call logs, shared accesses/`orte`, downstream IEEE `gleitPasst`
  outcomes agree since no `Block.gleit` is rewritten — and unchanged
  step-budget accounting for the same block shape), (3) width-exact word
  image, (4) admission implies `cfTot`/`breiteOk` (cannot fire on live CF)
- §5 `OptStrengthRed_verbindung_zeuge`: joint witness (`5 * 8` to `5 << 3`
  on `refD` with `Endblock.leave`, beside reached memory-changing run `MB`;
  uses `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`)

## Last `./lean-bau` result line

`Build completed successfully (511 jobs).` — whole project green.
`./lean-probe` on the new file: `0 error(s)`. All `#print axioms` are
subsets of the standard set (`propext`, `Classical.choice`, `Quot.sound`);
no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. `gabbro_ziel` itself was
not touched (only additive change: one new file + one import line), so its
axiom set is unaffected; the full build passing confirms no regression.

## What remains open (see CUTS in the file)

No machine-byte claim (stops at `eval`/`execEnd`/words); no `sdiv` and no
float `a*2.0 -> a+a` rewrite arms (both refused by name — no mul/add
flag-payload identity is established); no new `Befehl` forms (flag evidence
reused, wiring stays with the Typen owner); no TSO/GX bridge, ABI/loader, or
machine-work inequality (same block shape, never re-summed here).

## Anything in the task I believe is wrong

Nothing wrong. One note: the "per-width flag/fault identity lemma" premise
from the DESIGN row is proved here as three lemmas (imul CF=OF lock,
shl-by-3 OF-undefined + CF reading, CE-6 numeric distinguisher) rather than
one lemma, because the refusal needs both the structural fact (OF `none`
vs defined) and the value-level fact (CF functions differ). The float
refusal is by missing identity evidence, not by a model-level
counterexample: in the kernel model `a*2.0` and `a+a` may agree, but NaN
payload and invalid/inexact flags differ on silicon, which the model does
not capture — so no float arm is offered at all. This is documented in §2
and CUTS, not claimed as a proved inequality.
