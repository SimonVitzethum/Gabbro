# MUSE-REPORT-430: Sound validation-cache reuse certificate

## Task
New reusable module `grammatik/Grammatik/X86/ValidationCache.lean` plus one
additive X86 import at the end of the umbrella: a small sound reuse
certificate for already validated EXACT canonical byte input/context
equality. No hash axiom, no trusted Rust semantic conclusion, no
source/profile/region/control binding beyond the compared pair.

## What was done
Created `grammatik/Grammatik/X86/ValidationCache.lean` (owned new file) and
appended `import Grammatik.X86.ValidationCache` to `grammatik/Grammatik.lean`.
The module reuses only accepted vocabulary: `Codec.decode`/`natByte`,
`Ausfuehrung.laengeOk`, `Bild.Profil`.

Definitions:
- `ValidKontext` (`profil : Profil`, `bias : Nat`): the compared context.
- `CacheEintrag` (`kontext`, `bytes`, `befehl`, `laenge`, `rest`): one
  validated byte window with its decoded outcome.
- `Cache := List CacheEintrag`; `eintragOk` (decoding the EXACT stored bytes
  reproduces the stored triple, length in 1..15); `eintragPasst` (exact
  context-and-bytes match); `cacheFind` (first exact match, else `none`).

Theorems (every premise used by its proof):
- `cacheFind_hit_gleich`: a hit returns a stored entry with exactly the
  queried context and bytes (identity completeness).
- `cacheFind_verweigert_bei_fremden_bytes`: no stored entry with the queried
  bytes implies `none` (failure on different bytes).
- `cacheFind_verweigert_bei_fremdem_kontext`: no stored entry with the
  queried context implies `none`, even on byte-identical input.
- `eintragOk_auspacken`: a validated entry reproduces its stored decode
  outcome with a valid length.
- `treffer_wiederverwendung` (main): hit + validated entry replays the
  stored decode triple for the queried bytes in the queried context. Reuse
  is congruence of `decode` from actual input equality; no hash, no
  collision assumption.
- Concrete evaluated witnesses: `zeugenEintragRet_ok` (validated `ret`),
  `zeugenTreffer` (exact-bytes hit), `zeugenMiss_bytes` (forged byte
  refuses), `zeugenMiss_kontext` (same bytes under bias 4096 refuse),
  `zeugenWiederverwendung_angewandt` (generic reuse theorem applied to the
  concrete entry).

## Checks (last results)
- `./lean-probe grammatik/Grammatik/X86/ValidationCache.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (393 jobs).`
- `#print axioms` for all ten theorems: `[propext]` or none (see file tail).
- `gabbro_ziel` axiom check:
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` (standard three, unchanged).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.
- No theorems quantify over program syntax (`Vertrag`/`Stmt`/etc.), so no
  `_zeuge` obligation under rule 13; joint concrete witnesses are the five
  `zeugen*` theorems above.

## Open / CUTS (also in the file tail)
No cache implementation or performance claim; reuse replays only the decode
triple through the accepted decoder (no source, contract, cost, lock,
region, control-flow, or multi-instruction claim); context is only
(profile, bias); no hardware/OS/loader/concurrency/TSO/timing claim; no
second decoder or IR introduced. An actual validator cache, eviction
reasoning and whole-image coverage remain OPEN.

## Environment note (finding, not a code problem)
The shared machine was repeatedly thread-starved today: `lake env lean`
died at startup with `failed to create thread` (exit 134) for both
`./lean-probe` and the final `./lean-bau` umbrella step across many retries
over ~30 minutes. All 392 dependency jobs built; only the top-level
`Grammatik` olean step failed transiently, then succeeded on retry. No proof
was changed to work around this.

## Task fidelity note
Nothing in the task statement looked wrong. The target was a bounded reuse
certificate, delivered as specified, without filling the slot with a
mini-machine or a manufactured correctness hypothesis.
