# MUSE-REPORT-416: EffectiveAddress (continuous Lean proof reserve)

Lane 416, clone `/home/simon/Dokumente/gabbro-muse/a416`, branch `muse/416`.
Owned files only: `grammatik/Grammatik/X86/EffectiveAddress.lean` (new),
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was delivered

New reusable module `Grammatik.X86.EffectiveAddress` (~500 lines) with facts
about the ACTUAL pilot `effAddr`/`dispWort` of `Ausfuehrung.lean`, consumed
by the real pilot load/store steps and their `Zugriffe.zugriff` footprints.
No new register, memory, decoder, source model or IR. LEA/branch targets
were left to `ControlFlow.lean` (no duplication); this module covers the
missing part: signed displacements, modular-vs-admitted separation,
load/store-step consumption, and a future scaled-index helper.

Definitions (2): `skaliertAddr` (future scaled-index address over canonical
`Register`/`Wort`/`dispWort`), `dunkelSpeicher` (dark fault-witness memory).

Theorems (31):
- Displacement: `dispWort_null`, `dispWort_negEins`, `dispWort_negFuenf`,
  `dispWort_maxPos`, `dispWort_minNeg`.
- Bridges/shifts: `wort_add_allOnes`, `wort_add_negFuenf`,
  `wort_add_minNeg`, `effAddr_null`, `effAddr_negEins`,
  `effAddr_negFuenf`, `effAddr_maxPos`, `effAddr_minNeg`.
- Prestate/alias: `effAddr_prestate` (same base value gives same address),
  `effAddr_alias_beispiel` (different bases alias: no injectivity).
- Modular vs admitted: `effAddr_umlauf_wert` (wrap value exists),
  `effAddr_rand_kein_ohneUmbruch` (top-of-space admits no footprint),
  `effAddr_rand_wert`, `effAddr_fuss_addrs` (no-wrap Nat view),
  `effAddr_in_region` (extent admission per footprint byte; permissions
  stay a separate check).
- Step consumption: `effAddr_load_schritt`, `effAddr_store_schritt`
  (with `zugriff` footprint equations), `effAddr_load_verweigert`,
  `effAddr_store_verweigert` (refusal admits no step).
- Scaled future: `skaliertAddr_skala_null` (unscaled = pilot, no second
  model), `skaliertAddr_prestate` (two-register alias discipline),
  `skaliertAddr_weicht_ab` (divergence probe: 8352 vs 8192).
- Witnesses: `effAddr_lauf_zeuge` (reached run `movImm/store/load`
  through `rsp + 0 = 8192`: `rbx = 42`, byte changed 0 -> 42),
  `effAddr_laden_verweigert_zeuge` (dark-memory refusal),
  `effAddr_store_schritt_zeuge`, `effAddr_load_schritt_zeuge` (all
  premises jointly on `rax = 42` / `8192` with the changed byte).

Every theorem uses all its premises. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`, no `Prop`-typed premise, English only.
`#print axioms` for all 31 mains: all `[propext, Quot.sound]` or fewer,
except `effAddr_in_region` with exactly the standard triple
`[propext, Classical.choice, Quot.sound]`.

## Checks (measured, not claimed)

- `./lean-probe grammatik/Grammatik/X86/EffectiveAddress.lean`:
  `0 error(s)`, exit 0.
- `./lean-bau`: `exit 0; 0 error line(s)`, `Built Grammatik`,
  `Build completed successfully (393 jobs)`.
- `gabbro_ziel` axiom set: unchanged by construction — no goal/checker/
  emitter/source file touched (`git status` shows only the two owned
  files plus this report); the full-tree bau that covers `BeweisAtomar`
  is green. No new axiom introduced anywhere in this lane.

## What remains open (see file CUTS)

No hardware correspondence; no native scaled-index support (`skaliertAddr`
has no `Befehl` constructor, `Codec` row or `schritt` case — a future SIB
form needs its own decode/step extension plus review); no alignment
admission; no TSO/GX bridge (footprints are sequential byte sets, no
atomicity/interleaving claim); no source/ABI/cost/time/whole-image or
full source-to-byte validation claim.

## Findings for the coordinator (no safety impact)

1. Environment: repeated transient Lean `failed to create thread` crashes
   (OOM fallout, machine-wide), plus one real `omega` OOM panic. Probes
   succeed on retry when memory frees; a crashed check was never counted
   as acceptance. One earlier "0 errors" line accompanied a crashed
   process — I re-probed until genuine exit-0 output.
2. Real proof repair: `omega` could not close `x + allOnes = x - 1`
   from raw `toNat_add/sub/ofNat` forms; fixed by pre-proving the
   constant words' `toNat` values with `decide` first.
3. Parser facts (both cost real time): a `{ ... with ... }` struct-update
   literal must open AND close on the same line (multi-line args around
   it are fine); and `0/-1`-style text inside a `/-` comment nests as a
   comment opener (unterminated-comment error) — rephrased to words.
4. `simp [schrittRegister, regSet]` on a giant concrete state crashed the
   worker; the same goal goes through with a plain `decide` on the
   register projection.
5. The task text is sound; nothing in it appears wrong. The two
   `_zeuge` companions go beyond the strict HARD-RULE-13 trigger (no
   program-syntax premises, no `ZEUGE:` targets) and follow the X86
   joint-witness precedent instead.
