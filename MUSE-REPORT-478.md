# MUSE-REPORT-478: Independent exact-candidate review of 430

## Scope and method
Reviewed the pinned 430 snapshot (3 files: new module
`grammatik/Grammatik/X86/ValidationCache.lean`, one additive umbrella import,
report) against the owner task, the PATCH text, and the BUILD-EVIDENCE log.
Verified clone `/home/simon/Dokumente/gabbro-muse/a478` on branch `muse/478`.
Inspected accepted vocabulary in this clone (`Codec.decode`/`natByte`,
`Ausfuehrung.laengeOk`, `Bild.Profil` with `.p48`/`.p57`, `Typen.Befehl`
with `.ret`, `Decodiert`): `decode [natByte 195] = some ((ret, 1), [])`
(`pin_ret_dekode`, `roundtrip_ret`) and `laengeOk 1 = true` hold, so the
concrete `ret` witness is grounded in accepted facts, not invented.
Staged only the supplied candidate file temporarily in this clone, ran the
queued `./lean-probe` on it, checked forbidden/discard patterns and the tail
block, then deleted the staged file. Status is clean except this report.
Did not read any other clone. Did not modify any other file.

## Candidate content (inspected names)
Definitions: `ValidKontext` (profil, bias), `CacheEintrag`
(kontext, bytes, befehl, laenge, rest), `Cache` (abbrev for list),
`eintragOk`, `eintragPasst`, `cacheFind` (first exact context-and-bytes
match, else none). Results: `cacheFind_hit_gleich`,
`cacheFind_verweigert_bei_fremden_bytes`,
`cacheFind_verweigert_bei_fremdem_kontext`, `eintragOk_auspacken`,
`treffer_wiederverwendung` (main reuse: hit plus validated entry replays
the stored decode triple for the queried bytes, carrying the queried
context equality). Concrete evaluated cases: `zeugenKontext`,
`zeugenEintragRet`, `zeugenEintragRet_ok` (by `decide`),
`zeugenTreffer` (by `decide`), `zeugenMiss_bytes` (by `decide`),
`zeugenKontextAnderer`, `zeugenMiss_kontext` (by `decide`),
`zeugenWiederverwendung_angewandt` (main theorem applied to the concrete
entry). Tail has an explicit CUTS block plus `#print axioms` for all ten
theorems. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no
`intro _` / `have _ :=`, no contract-quantifier evasion. Every premise of
every theorem is used. No premise has type `Prop` itself.

## Material correctness
The main result is congruence of the accepted `decode` function from
actual input equality plus a carried context identity: a hit gives
`e.bytes = bs` and `e.kontext = ctx` (`cacheFind_hit_gleich`), a
validated entry gives `decode e.bytes = stored` (`eintragOk_auspacken`),
substitution yields `decode bs = stored`. No hash, no collision
assumption, no Rust-supplied semantic conclusion, no second decoder or IR.
`cacheFind` does not itself check `eintragOk`; the main theorem takes
validation as a separate premise, which is the sound separation.
Context (profile, bias) is compared but not consumed by `decode`; the
refusal on different context is therefore conservative (over-strict),
not unsound, and the report/CUTS say exactly that context is only the
compared pair with no source/profile/region/control binding beyond it.
Joint inhabitation is shown (validated `ret` entry that also hits), plus
two genuine negative cases (forged byte 194 refuses; same bytes under
bias 4096 refuse), so the premises are not vacuous and the negative
claims are evaluated by `decide`, not asserted. No theorems quantify
over program syntax, so no rule-13 `_zeuge` obligation arises; the five
concrete cases are the joint witnesses. No checker, goal, Rust, emitter,
or friend-owned paths are touched; snapshot file list confirms the bound.
Umbrella change is one additive import line. Note for integration: the
candidate base ends at `AccessList` while current master has five further
imports after it, so the merger must take the union and keep the new
import at the end rather than applying the hunk verbatim.

## Evidence reproduction
My queued probe in this clone on the supplied file:
`== 0 error(s) in the COMPLETE output; exit 0`, with axiom lines
`[propext]` for the five main/concrete-validated results and no axioms
for the three `decide` miss/hit identities — exactly matching the
report and the final BUILD-EVIDENCE probe. (My first probe attempt hit
the 120 s wrapper timeout with no output, consistent with the loaded
machine the author reported; the retry with a larger timeout succeeded
with no proof change.) The BUILD-EVIDENCE log honestly records the
transient `failed to create thread` (exit 134) retries and one
intermediate type error with `sorryAx` before the final green
`Build completed successfully (393 jobs)` and the standard three-axiom
`gabbro_ziel` check; nothing in it reads as forged. Full `./lean-bau`
was not repeated here: the change is additive over untouched `Zielsatz`
vocabulary and the single-file probe plus axiom reproduction covers the
delivered claim; the last full build result below is the author's
quoted line, not my rerun.

## Last build result line
Author-quoted `./lean-bau`: `Build completed successfully (393 jobs).`
My rerun: single-file `./lean-probe` 0 errors (see above); no `./lean-bau`.

## What remains open (per candidate CUTS, agreed)
No cache implementation or performance claim; reuse replays only the
single-window decode triple; no source, contract, cost, lock, region,
control-flow, multi-instruction, whole-image, eviction, hardware, OS,
loader, concurrency, TSO, timing, or termination claim.

## Assessment
The precisely delivered bounded claim — exact byte/context equality
lookup with hit identity, miss on different bytes/context,
validated-means-decided, and sound decode replay from actual input
equality over accepted vocabulary — is proved, witnessed (positive and
negative), honestly cut, and axiom-clean. No hidden assumption, vacuity,
duplicated execution model, or safety weakening found. Repair direction:
none; integration takes the umbrella import as a union at the end.

CANDIDATE: 430 269da277cfe4141d22abbb1cdbf5353330f7a6fa
VERDICT: ACCEPT
