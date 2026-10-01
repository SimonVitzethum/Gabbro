# MUSE-REPORT-494

*Lane 494 — independent exact-candidate review of 414.
Clone `/home/simon/Dokumente/gabbro-muse/a494`, branch `muse/494` — verified
(`git rev-parse --abbrev-ref HEAD` = `muse/494`, `git rev-parse HEAD` =
`7b9ffff2642f087610b010d1d58e2c6119ba80a3` at review time).*

## Scope and method

Reviewed the exact snapshot `.tmp/review/SNAPSHOT.json` (author 414, head
`b11bd5853332ec5feb8acf817ebc20f1e5a57fb2`, base `0b3132b7`, files
`MUSE-REPORT-414.md` + `dokumente/x86/AUDIT-SOURCE-FOOTPRINT.md`, clean true),
the owner task, `PATCH.diff` (372-line new audit + 71-line report, nothing else),
`BUILD-EVIDENCE.json`, and the supplied candidate audit copy. Checked every
material technical claim against the actual source files in this clone
(`grammatik/Grammatik/...`) and against the pinned base via `git ls-tree`
where the audit pins its as-read version. No other clone read. No Lean or Rust
build needed: the candidate is doc-only and claims no build signal.

## Claim-by-claim verification

- **F4 (P0): `accessList` never returns `luecke`. CONFIRMED.**
  `X86/AccessList.lean:64-65` defines `accessList := .voll (eintraege ...)`;
  `accessList_kein_luecke` (`:145-149`) proves `≠ .luecke` by unfolding and
  `cases h`. The `luecke` constructor exists (`:52`) and `pruefeBefund`
  refuses it (`luecke_faellt`, `:160`), but the sole producer can never emit
  it. The audit's "vacuous producer-side refusal; add a per-rule classifier
  or downgrade the claim" is a fair policy judgment with a sound repair
  direction, not an invented soundness hole.
- **F1 (P1): `Stmt.regs` misses the `transition` mirror read. CONFIRMED.**
  `ZielOrtGeraetSem.lean:186-197` ends `Stmt.regs` in `_ => []`, which covers
  `.transition`; `Semantik.lean:772-775` executes `transition` as
  `O.regLies m σ` plus `O.regSchreib r ...`. The mirror register `m` therefore
  never enters the device-carrier footprint. (`.regSchreib` also hits the
  catch-all but reads nothing, correctly empty — the audit notes this.)
- **F2 (P1): `callInd` footprint has no callee-contract disjunct. CONFIRMED.**
  `ZielOrt.lean:150-151`: direct `.call` adds
  `args.orte ++ requires/ensures`, indirect `.callInd` lists only
  `p.orte ++ args.orte`. Caller-side stability across an indirect call is
  unstateable from this footprint; `Block.gOk`'s `bindCallInd` allowlist
  (`ZielOrtGeraetSem.lean:128`) is admission, not cover. Audit books it as a
  consumer-side conservative rule plus a needed OPEN marker/disjunct.
- **F3 (P1): gate/oracle reads beyond `args.orte` are trace-invisible. CONFIRMED.**
  `D.Ax` (`Syntax.lean:165-175`) declares params/answer/write-frame/grounds
  but no read set; `stmtOrteP`'s `.axiomCall` arm (`ZielOrt.lean:157`) lists
  only `args.orte`; `GutO` (`Satz.lean:967-...`) constrains the write frame
  and records declared writes via `axiomSpur` (writes confirmed covered —
  audit explicitly credits this, `Satz.lean:904+`). A gate read outside
  `args.orte` yields no `lese` event and no delta, so `LiestG`/`ZugriffG` both
  miss it. The audit honestly flags the caller-duty alternative as open
  (report §"Open", audit §2.5) rather than forcing a model change.
- **F5 (P2): no `LockEreignis`↔`Zugriff` overlap adapter. CONFIRMED.**
  `OverlapRefusal.lean` consumes `Zugriff`/`Adresse` (`zugriffOk :44`,
  `fussDisjunktB :75`, `klassifiziere :88`) and never mentions
  `LockEreignis`; `LockedOps.lean` defines `LockEreignis :31` and never cites
  `fussDisjunktB`/`klassifiziere`. Trivial-but-unowned adapter, correctly
  filed as ownership, not as a bug in either module.
- **Checked-correct statements. AGREE.** Write-absence from `fussOrte` by
  design (dynamic write events + `¬ TraegerGleich` disjunct in
  `ZugriffG`/`SchreibG`, `RennfreiVoll.lean:511-518`, verified);
  `schreibG_voll`/`zugriffG_voll` keep the disjunct; per-byte-only atomicity
  claims respected (`einzelbyte_atomar`, `kein_atomarer_zugriff`,
  `lock_xadd_atomar` with tearing OPEN); `mfence_ordnung` local-only, no
  cross-core claim. `RufSchrittG` count 75 verified by grep
  (`grep -c "| [a-zA-Z].*(M :" RufMaschineG.lean` = 75).
- **§6 "missing bridge pieces". ACCURATE FOR ITS PIN.** At pinned base
  `0b3132b7`, `TableLayout`/`FenceDrain`/`GateStub`/`CostSummary`/`EntryState`/
  `ValidatorSkeleton`/`NarrowOps`/`ScalarFloat` are all absent from
  `grammatik/Grammatik/X86/` (verified via `git ls-tree`); several exist at
  current master HEAD because later lanes merged since. The audit pins its
  as-read version and labels these planned rows, not bugs — correct handling
  of drift, not a false claim.

## Rule compliance and evidence honesty

- Own-files only: PATCH adds exactly the two owned `.md` files; no Lean, Rust,
  checker, Spec, emitter, or ledger touch. Clean snapshot consistent.
- No `sorry`/`admit`/`axiom`/`native_decide`, no theorems, so no witnesses or
  `#print axioms` owed; none claimed. CUTS present at audit end; report lists
  open points. No full-compiler-closure claim; bounded audit claim only.
- Proof-vs-claim discipline good: cites existing `decide` witnesses and
  planted refusals by file/line instead of inventing probes; the owner task's
  "probes where useful" is addressed honestly given OWN-ONLY two `.md` files
  (no Lean file named, no committed probes possible). F1–F3 are definitional
  arm mismatches needing no probe to state; repairs will carry their own.
- BUILD-EVIDENCE coherent: first command shows files absent before staging
  (expected for new files), second shows untracked audit, the
  `arbeitsprotokoll` add failure is benign (gitignored path) and the author
  recovered in the next command; final commit `b11bd585` with co-author line
  and clean `git log`/`status`. No forged benchmark or axiom evidence.
- English only. Severity ordering (P0 for vacuous refusal vs P1 for real
  footprint gaps) is disclosed author judgment in CUTS; defensible either
  way, not a correctness defect. One trivial slip: "≈70 stale by two" for a
  75 count (actually five); immaterial.
- No hidden assumptions, no vacuity in the audit's own statements, no safety
  weakening, no duplicated IR/execution, no trust-boundary violation (source
  checker, Spec, goal, Rust, emitter, Typen/execution/codec untouched;
  friend-owned optimizer files untouched).

## Deliverables

- New definitions/theorems: none (doc review lane; nothing added here either).
- Last `./lean-bau` result line: not run — `grammatik/` untouched in this
  review clone (`git status` clean before and after except this report), so no
  build signal is claimed or needed.
- Open: F1–F3 repairs, `callInd`/gate consumer rules T1–T4, per-rule access
  table beyond `exchange`, F5 adapter ownership — all already OPEN and
  scheduled by the audit itself.

CANDIDATE: 414 b11bd5853332ec5feb8acf817ebc20f1e5a57fb2
VERDICT: ACCEPT
