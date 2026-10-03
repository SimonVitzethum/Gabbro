# MUSE-REPORT-1045: Exact review of author 895 (Optimiser rule: return-path selection rule)

CANDIDATE: 895 6969d6601c61421afe17f754b4cefc82e93452ef
VERDICT: ACCEPT
Scope: bounded — taken-path discipline only; tail-rewrite/epilogue-jump and B/C citation soundness out of scope (see bounds below).

## Clone / snapshot verification

- Review clone `/home/simon/Dokumente/gabbro-muse/a1045`, branch `muse/1045` — verified.
- Review checkout HEAD `b040b155159f47629542b0083e2f0a8a607f2b4c`, which equals the pinned snapshot `base`. Snapshot (`SNAPSHOT.json`): author 895, head `6969d6601c61421afe17f754b4cefc82e93452ef`, base `b040b155…`, files `MUSE-REPORT-895.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/OptRetPathSel.lean`, clean `true`.
- Inspected exact artifacts: `OWNER-TASK.md`, `MUSE-REPORT-895.md`, `PATCH.diff` (full 537-line new file plus one-line `Grammatik.lean` import), `BUILD-EVIDENCE.json`. No other clones, no network, no keys. Own only this report; no source touched.

## What the candidate does

New file `grammatik/Grammatik/X86/OptRetPathSel.lean` (~537 lines) plus one import line. States DESIGN section 7 "Layout / allocation" row combined with section 3A ("callee-saved restores on all paths, checked per call/return") as a generic rule lemma over arbitrary registers/values over reused canonical vocabulary (`Typen`, `Speicher`, `Ausfuehrung`, `StackUnwind`) plus the `eD`/`eP` fixture for the joint witness. Certificate `RetPfadCert`: layer-A rewrite record (`pfade`, `epilog`, `gesichert`) plus layer-B/C validator-recomputed citations as checked `Bool` data (`alleOk`, `epilogOk`, `fremdOk`, `farbeOk`). Admission `retPfadZulassen` conjoins all four citations with per-path `retPaarOk` (tail `pop64 r` + `ret`), save-shape and epilogue-shape equations. No new machine/decoder/instruction, no source/checker/Spec/goal/emitter edits, no diagnostic/gift/example/CLI numbers, no MARKE changes, no friend-reserved optimiser files. Scope-compliant.

## Checks performed

- Full `PATCH.diff` read: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`; no `Prop`-typed premises; `CUTS:` block plus `#print axioms` for every main theorem present.
- Premise use: `retPaar_aus_zulassung` uses `hz` via `Bool.and_eq_true` chains and `of_decide_eq_true` for pair plus both shape equations. All four refusals use their premise (`fehlend`/`keinRet` via negated conjunction + `decide` case split; `fremd`/`farbe` via `simp [retPfadZulassen, h]`). `retPfad_wert_erhalten` forwards every guard to accepted `push_pop_wiederhergestellt`. `OptRetPathSel_flags` rewrites all four steps with `schritt_call32/push64/pop64/ret_erfolg` lemmas and chains `f1–f4`; every step guard is consumed. `OptRetPathSel_verbindung` extracts `hpair`, pins `dst = r` from `hbq`/`hpair.1` (`hz` load-bearing via `hdst_eq`), then forwards everything including `hdis` to accepted `verschachtelt_wiederhergestellt`. No `intro _` / `have _ :=` evasion in the diff.
- Reuse soundness: the two load-bearing targets exist in this checkout at the snapshot base — `StackUnwind.lean` lines 46 (`push_pop_wiederhergestellt`) and 127 (`verschachtelt_wiederhergestellt`) with matching guard-shaped premises (length-ok, opcode equations, write/read guards, disjointness). The candidate's call chains pass premises in the same order/shape. The flag proof mirrors the accepted `simp [schrittCall/schrittPush/schrittPopReg/schrittRet]` pattern.
- Architecture (Intel SDM 325462-093US local snapshot, `HARDWARE-REFERENCES/REFERENCES.json` verified 2026-10-02; AMD absent as declared): `call32`/`push64`/`pop64`/`ret` are the canonical 64-bit stack forms; `rsp`-as-implicit-operand handled explicitly with `dst ≠ rsp` guard; return address `ripNach s.rip dc.laenge` pushed by call and restored by ret (conclusion `s4.rip = ripNach s.rip dc.laenge` is the correct post-return value, not the call target). Length guards (`laengeOk`) on all four steps; read/write guards on both stores; disjointness keeps the inner save off the return slot. PUSH reg / POP reg / CALL / RET do not touch RFLAGS, so the flag-preservation lemma is architecturally correct and derived from canonical step definitions, not asserted from silicon. No LOCK/TSO/atomic forms involved; sequential single-`Speicher` facts only, with TSO/GX explicitly left to the bridge lane — correct, no invented atomicity. No FP forms in the pilot `Befehl` vocabulary; no MXCSR/FP claim made. No interrupt/enable gates touched. No pre-fault effect invented: fault behaviour rides exclusively on accepted guards, plus four loud-`false` refusals (never warnings), and no `ensures` derived.
- Witness `OptRetPathSel_verbindung_zeuge`: same-register `rbx` chain (`zeugRmp`/`zeugRS2`/`zeugRS3`/`zeugRS4`) over the accepted call frame (`zeugS`, `zeugSc1`, `zeugMc`, `zeugNobenP`, `zeug_call_schreibt`, `zeugOben_lesbar`), all `schritt` premises discharged by the `…_erfolg` lemmas, `hdis` by interval disjointness, memory change by `writeBytesN_hit` (`0 ≠ written return address`), restored top/value via the connection itself (`hconn.1`, `hconn.2.2.1`), source non-degeneracy via `(eD.signatur eSetze).schreibt () = true` (`rfl`) and `ziel_ort_einfaden_zeuge` unpacked to a reached `RufErreichbarG` run with slots `0 → 5`, `≠`, and log membership. Joint, non-degenerate, memory-changing — meets the bar.
- Negative mutations: `decide` probes for admitted-ok, missing-restore refusal, and false-`fremdOk` refusal. Refusal theorems additionally cover missing-`ret` and colouring mismatch (no dedicated `decide` probes for those two — minor, not verdict-changing since the theorems are proved and the two probed negatives exercise both the pair-check and citation gates).
- Axioms/build: `BUILD-EVIDENCE.json` shows honest intermediate reds (unsolved-goals, unknown-identifier) repaired in-file, final `./lean-probe` 0 errors, axiom print connection `[propext, Quot.sound]` and witness `[propext, Classical.choice, Quot.sound]` (within the standard triple), final `./lean-bau` `== exit 0; 0 error line(s)`, `Build completed successfully (511 jobs)`. `gabbro_ziel` files untouched.

## Bounded acceptance (what ACCEPT does and does not cover)

ACCEPT covers: the per-path restore check, admission shape, four loud refusals, value/flag preservation over arbitrary values, and the taken-path connection (admitted save/restore/return keeps callee-saved value, stack top, return address, all permission maps) with its joint witness.

Explicitly NOT covered (author states all of this in CUTS; I confirm the boundary is real): the tail rewrite itself (selected-path `pop/ret` tail replaced by a jump to the shared epilogue) has NO step correspondence — only the taken path's restore pair is pinned and connected. The certificate lists `pfade`/`alleOk`/`epilogOk` are carried `Bool` citations with no formal link to path enumeration or epilogue execution (admission can hold while `pfade` does not contain the taken path); their semantic soundness belongs to the validator/analysis lane, not this file. Source legs (contracts at place, call-log order, entry duties, budget timing), TSO/GX concurrency, IEEE scalar-FP correspondence, cost/work bounds, and any silicon/ABI-entry claim all stay with their owner lanes.

## Minimal-repair note (not required for this verdict)

If a follow-up wants the "selection" half rather than the "discipline" half, it must: (a) relate `pfade` membership / `alleOk` to the taken `dq/dr` (or admit the gap formally), (b) execute the shared `epilog` and prove the jump-to-epilogue step correspondence, (c) add `decide` probes for the `keinRet` and `farbe` refusals. None of this is a silent defect today because every gap is fenced in CUTS and no theorem claims the missing correspondence.

## Last build result

`./lean-bau` on this report-only checkout: `== exit 0; 0 error line(s) in the COMPLETE output`, `Build completed successfully (510 jobs)` (base without the candidate module; candidate's own final `./lean-bau` per evidence: same exit line, 511 jobs green with `OptRetPathSel`).

## What remains open / task notes

- Nothing open on the review itself. Integration (merge + fresh publication checks) belongs to the coordinator/watcher, not this lane.
- Task repeatedly asks for "IEEE, contracts, call logs, concurrency and budget" preservation in one rule lemma: at this layer only the machine half is provable without fabricating a source bridge. The author was right to prove the machine half and fence the rest as OPEN with named owners. The "single accepted IR" and "invariant/effect exports" named in the owner task do not exist in the tree; the author documented the substitution (`TableLayout`, `CostSummary`, `SpillPrivate`, `AufrufOpt`, `CallAlign16`/`StackUnwind` patterns) instead of inventing them — correct behaviour.
