# MUSE-REPORT-478: Independent exact-candidate review of 430 (re-review after repair)

## Scope and method
Re-reviewed the NEW pinned 430 snapshot (3 files: new module
`grammatik/Grammatik/X86/ValidationCache.lean`, one additive umbrella
import, report) against the owner task, the new PATCH text, and the
extended BUILD-EVIDENCE log. Verified clone
`/home/simon/Dokumente/gabbro-muse/a478` on branch `muse/478`. The
previous review (accepted head 269da277) is superseded; this is a fresh
substantive review of the changed commit, not an approval of the stale
snapshot. Inspected accepted vocabulary in this clone
(`Codec.decode`/`natByte`, `Ausfuehrung.laengeOk`, `Bild.Profil` with
`.p48`/`.p57`, `Typen.Befehl` with `.ret`, `Decodiert`):
`decode [natByte 195] = some ((ret, 1), [])` (`pin_ret_dekode`,
`roundtrip_ret`) and `laengeOk 1 = true` hold, so the concrete `ret`
witness stays grounded in accepted facts. Staged only the supplied new
candidate file temporarily in this clone, ran the queued `./lean-probe`
on it, checked forbidden/discard patterns, name collisions and the tail
block, then deleted the staged file. Status is clean except this
report. Did not read any other clone. Did not modify any other file.

## What changed versus the previously reviewed version
The integration gate had failed with `environment already contains
'Gabbro.Grammatik.X86.eintragOk' from Grammatik.X86.TableLayout`. I
confirmed the collision is real in this clone:
`TableLayout.lean:70` defines `def eintragOk (e : TabLayout) : Bool`
in the same `Gabbro.Grammatik.X86` namespace, so the old top-level
`eintragOk` (over `CacheEintrag`) could not coexist with it. Repair
(owned files only): the whole module body now lives in sub-namespace
`ValidCache`, so every provided name is
`Gabbro.Grammatik.X86.ValidCache.*`. Definitions, statements and
proofs are otherwise identical to the reviewed version; the only other
edit is a comment-style fix (`/--` cannot precede `namespace`). The
BUILD-EVIDENCE honestly shows one intermediate red probe from that
comment placement, then green. Umbrella import line is unchanged.

## Candidate content (inspected names, now qualified)
Definitions: `ValidCache.ValidKontext` (profil, bias),
`ValidCache.CacheEintrag` (kontext, bytes, befehl, laenge, rest),
`ValidCache.Cache` (abbrev for list), `ValidCache.eintragOk`,
`ValidCache.eintragPasst`, `ValidCache.cacheFind` (first exact
context-and-bytes match, else none). Results:
`ValidCache.cacheFind_hit_gleich`,
`ValidCache.cacheFind_verweigert_bei_fremden_bytes`,
`ValidCache.cacheFind_verweigert_bei_fremdem_kontext`,
`ValidCache.eintragOk_auspacken`,
`ValidCache.treffer_wiederverwendung` (main reuse: hit plus validated
entry replays the stored decode triple for the queried bytes, carrying
the queried context equality). Concrete evaluated cases:
`ValidCache.zeugenKontext`, `ValidCache.zeugenEintragRet`,
`ValidCache.zeugenEintragRet_ok` (by `decide`),
`ValidCache.zeugenTreffer` (by `decide`),
`ValidCache.zeugenMiss_bytes` (by `decide`),
`ValidCache.zeugenKontextAnderer`,
`ValidCache.zeugenMiss_kontext` (by `decide`),
`ValidCache.zeugenWiederverwendung_angewandt` (main theorem applied to
the concrete entry). Tail has an explicit CUTS block plus `#print
axioms` for all ten theorems. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`, no `intro _` / `have _ :=`, no
contract-quantifier evasion. Every premise of every theorem is used. No
premise has type `Prop` itself. Name-collision check: no other file in
`grammatik/` defines `cacheFind`, `eintragPasst`, `ValidKontext`,
`CacheEintrag`, `treffer_wiederverwendung` or the `zeugen*` witnesses;
`Cache` as `ValidCache.Cache` is shielded too.

## Material correctness (re-checked, all previous findings hold)
The main result is congruence of the accepted `decode` function from
actual input equality plus a carried context identity: a hit gives
`e.bytes = bs` and `e.kontext = ctx`, a validated entry gives
`decode e.bytes = stored`, substitution yields `decode bs = stored`.
No hash, no collision assumption, no Rust-supplied semantic conclusion,
no second decoder or IR. `cacheFind` does not itself check `eintragOk`;
the main theorem takes validation as a separate premise, which is the
sound separation. Context (profile, bias) is compared but not consumed
by `decode`; refusal on different context stays conservative
(over-strict), not unsound, and report/CUTS say exactly that context is
only the compared pair. Joint inhabitation is shown (validated `ret`
entry that also hits), plus two genuine negative cases (forged byte 194
refuses; same bytes under bias 4096 refuse), all evaluated by `decide`.
No theorems quantify over program syntax, so no rule-13 `_zeuge`
obligation arises. No checker, goal, Rust, emitter, or friend-owned
paths touched; snapshot file list confirms the bound. The namespace move
weakens nothing: it only lengthens names and cannot change provability
of the bounded claim. Minor wording note (not a defect): the report
body still lists short names in one section, but its repair section at
the top states the fully qualified `ValidCache.*` names explicitly.
Umbrella change is one additive import line; integration note from the
prior review still holds since the candidate base ends at `AccessList`
while current master has further imports after it, so the merger must
take the union and keep the new import at the end.

## Evidence reproduction (new file)
My queued probe in this clone on the NEW supplied file:
`== 0 error(s) in the COMPLETE output; exit 0`, with axiom lines
`[propext]` for the six validated/main results and no axioms for the
three `decide` hit/miss identities, all under
`Gabbro.Grammatik.X86.ValidCache.*` — exactly matching the new report
and the new final BUILD-EVIDENCE probes (`./lean-bau`
`Build completed successfully (393 jobs)`, `gabbro_ziel` on the
standard three axioms). The extended evidence log (old transient
`failed to create thread` retries plus the new namespace-fix red/green
pair) reads as honest development history, not forged output. Full
`./lean-bau` was not repeated here: the change is additive over
untouched `Zielsatz` vocabulary and the single-file probe plus axiom
reproduction covers the delivered claim; the last full build result
below is the author-quoted line, not my rerun.

## Last build result line
Author-quoted `./lean-bau`: `Build completed successfully (393 jobs).`
My rerun: single-file `./lean-probe` on the new file 0 errors;
no `./lean-bau`.

## What remains open (per candidate CUTS, agreed)
No cache implementation or performance claim; reuse replays only the
single-window decode triple; no source, contract, cost, lock, region,
control-flow, multi-instruction, whole-image, eviction, hardware, OS,
loader, concurrency, TSO, timing, or termination claim.

## Assessment
The precisely delivered bounded claim — exact byte/context equality
lookup with hit identity, miss on different bytes/context,
validated-means-decided, and sound decode replay from actual input
equality over accepted vocabulary, now under `ValidCache.*` — is
proved, witnessed (positive and negative), honestly cut, axiom-clean,
and collision-free. No hidden assumption, vacuity, duplicated execution
model, or safety weakening found. Repair direction: none; integration
takes the umbrella import as a union at the end.

CANDIDATE: 430 173551f4d79f71e1d73e7fc82c2f208ac8ec38cc
VERDICT: ACCEPT
