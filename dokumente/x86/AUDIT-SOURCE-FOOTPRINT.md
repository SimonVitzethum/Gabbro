# Audit: source footprint extraction and its consumers (lane 414)

*Author lane 414. Scope: audit only — no model, goal, checker, emitter,
ledger or Lean change. Owns only this file plus `MUSE-REPORT-414.md`.
Status as-read at HEAD `0b3132b7`; line numbers are as-read and may drift.
No new Lean code, no new probes committed; all evidence below cites
existing proved theorems and `decide` probes by file and line.*

*Non-duplication: `REVIEW-TSO.md` §5.2 recommended the single-owner
`accessList` (now `AccessList.lean`); `QUELLBRUECKE.md` audits
source-computed interfaces for phase B; `REVIEW-QUELLE-INVARIANTEN.md`
covers invariant-side source obligations. This audit does not repeat
their architecture findings. It checks the ACTUAL current
implementations named below against the task's three questions only:
(1) missing raw hardware/atomic/gate access in source footprints and
event traces, (2) cross-carrier full-width overlap and source
instruction granularity, (3) what the proved claims actually cover
versus what their consumers (TSO bridge D-access/L-access, IR lowering,
overlap checker) still need.*

## 0. Verdict summary

Five findings, ordered by severity in §7. Two are genuine gaps in
accepted footprint code (F1 device-register read missed by `Stmt.regs`;
F2 indirect-call callee contracts absent from every footprint). One is
a silent-read hole in the oracle/gate interface (F3). One is a
producer-side refusal that can never fire (F4). One is an unowned
adapter between two accepted modules (F5). Everything else checked is
correct within its stated claim, including several shapes this audit
was asked to attack: gate *writes* are recorded (`axiomSpur`,
`Satz.lean:904`), the `zugriff` potential/realised split is explicit,
per-byte containment keeps `zugriffOk` wrap-safe, and the TSO bridge's
per-access requirements are openly marked OPEN where unproved.

## 1. Artifacts audited (exact)

Source side (G/GX):

- `grammatik/Grammatik/Semantik.lean:61-118` — `Ereignis`,
  `World.lese` (read events), `World.schreibSlot/schreibGlob`
  (write events), `World.storeSlot/storeGlob` (silent writes);
  `execStmt` `Semantik.lean:699-786`, `execBlock` `:788-878`,
  `execEnd` `:880-...`; `axiomAntwort(Sonst)` `:665-695`;
  `Orakel` `:454-462`.
- `grammatik/Grammatik/RennfreiG.lean:19-29` — `zugriffVon`,
  `zugriffe` (trace-delta access set, no atomicity bit, whole-carrier
  keys).
- `grammatik/Grammatik/RennfreiVoll.lean:498-523` — `ereignisse`,
  `ZugriffG`/`SchreibG` (with `¬ TraegerGleich` disjunct),
  `LiestG` (recorded-read-only).
- `grammatik/Grammatik/RufMaschineG.lean:263` — `RufSchrittG`,
  **75 constructors** (counted `^  | <name> (M :` at HEAD; the
  "≈70 rules" figure in older docs is stale by two).
- `grammatik/Grammatik/ZielOrt.lean:138-206` — `stmtOrteP`,
  `blockOrteP`, `endblockOrteP`; `fussOrte` `:251-256`,
  `fussOrtB`/`FussOrtOk` `:283-296`.
- `grammatik/Grammatik/ZielOrtGeraetSem.lean:186-...` —
  `Stmt.regs`/`Block.regs`/`Endblock.regs`; `fussOrteG`,
  `fussOrtGB` (`:471-...`).
- `grammatik/Grammatik/SperreFuss.lean:140` — `FussS`;
  `Speichermodell/AtomarReplay.lean:29` — `FussSX` (+`Tg` disjunct);
  `Satz.lean:904-967` — `axiomSpur`, `GutO`; `Syntax.lean:166-175`
  — `D.Ax` fields (no read declaration).
- `grammatik/Grammatik/Speichermodell/RMW.lean:117` —
  `exchange_liest_schreibt` (the only per-rule access lemma).

Target side (X86):

- `X86/Zugriffe.lean` — `zugriff` (`:42-58`), per-constructor equations
  (§1), realised-footprint theorems (§§3-6), `kein_atomarer_zugriff`
  (`:540`), witness + `decide` probes (§9), CUTS `:636-651`.
- `X86/AccessList.lean` — `eintraege`/`accessList`/`IstRMW`/
  `pruefeBefund` (`:56-78`), generic completeness (`:83-140`),
  `accessList_kein_luecke`/`luecke_faellt` (`:145-161`),
  `exchange_rmw_voll`/`exchange_zwei_liest` (`:170-195`), CUTS
  `:238-266`.
- `X86/OverlapRefusal.lean` — `zugriffOk` (`:44-48`),
  `fussDisjunktB_klingt` (`:119`), `einzelTraeger_wertUeberein`
  (`:141-...`), neighbour-carrier witness + `decide` probes (§4).
- `X86/LockedOps.lean` — `lockSchritt` (`:58-78`),
  `lock_xadd_atomar` (`:145`), `mfence_ordnung`, CAS lemmas,
  planted split-load-store refusal (§11, `:417-440`), CUTS.
- `X86/TSO.lean` — `issueByte`/`loadByte`/`flushKern`/`zaunBereit`
  (`:50-86`), `einzelbyte_atomar` (`:445`).

Bridge/plan docs: `TSO-GX-BRUECKE.md:575-...` (D-access, L-access-
complete, L-read/write/view/step), `WORK-ALLOCATION.md` items
B1/B2/C6 (owner rows).

## 2. Source footprint extraction, constructor by constructor

### 2.1 `stmtOrteP` (ZielOrt.lean:138-166) — full table

| Constructor | Orte listed | Writes carrier? | Verdict |
|---|---|---|---|
| `assignSlot` | `i.orte ++ e.orte` | `t` via `schreibSlot` (event ✓) | correct within claim (see §2.3) |
| `assignDurch` | `p.orte ++ i.orte ++ e.orte` | `t` via `schreibSlot` (event ✓) | correct within claim |
| `assignGlob` | `e.orte` | `g` via `schreibGlob` (event ✓) | correct within claim |
| `schreibBytes` | `i.orte ++ e.orte` | `t` bytes via `schreibBytes` (events ✓, `Semantik.lean:136`) | correct within claim |
| `assignVar` | `e.orte` | none (env only) | correct |
| `uebergang` | `.inl t :: i.orte` | `t` (event ✓) | correct (superset, harmless) |
| `ite/onOption/onTag/onGrund` | cond + branch bodies | via bodies | correct |
| `call g` | `args.orte ++ requires/ensures(g)` | via callee frame | correct (modular; callee has own `FussS`) |
| `callInd` | `p.orte ++ args.orte` | via unknown callee | **F2 §2.4** |
| `locks/breaking/traverse/retry/forever` | body/inv/bis + bodies | via bodies | correct |
| `axiomCall` | `args.orte` | declared (`aschreibt/agschreibt`, events via `axiomSpur` under `GutO` ✓) | correct for writes; reads **F3 §2.5** |
| `regSchreib` | `e.orte` | none on carriers (oracle only) | correct on carriers; device side out of carrier footprint by design |
| `transition` | `[]` | none on carriers (oracle only) | carrier side correct; device read **F1 §2.2** |
| `publish` | `e.orte` | `g` via `schreibGlob` (event ✓) | correct within claim (see §2.3) |
| `advances/retires` | `[]` | none (`.ok σ ρ`) | correct |
| `ret/retGrund/leave/next` | `e.orte` / `[]` | none | correct |

`blockOrteP` (`ZielOrt.lean:168-195`) mirrors `execBlock` faithfully:
`bindAxiomElse` adds `endblockOrteP err` (`:181`), `regLiesElse`
adds `zusage.orte + sonst` (`:184`), `awaits` adds `.inr g`
(`:185`), `exchange` adds `.inr g :: neu.orte` (`:186`),
`narrow/pruefung` add `e/c.orte + sonst` (`:188-190`).
No Block arm drops a carrier its execution reads — except through the
gate-read hole F3, which is an `Orakel` interface property, not a
missing list arm.

### 2.2 F1: `Stmt.regs` misses the `transition` mirror read

`Stmt.regs` (`ZielOrtGeraetSem.lean:186-198`) ends in `_ => []`,
which covers `.transition r _ m _ _ _ _` — yet `execStmt`'s
transition arm (`Semantik.lean:772-775`) reads the mirror register
`m` (`O.regLies m σ`). Hence the device carriers `D.rtraeger m`
never enter `(P.rumpf f).regs.flatMap D.rtraeger`, i.e. they are
absent from `fussOrteG` and from the second disjunct of `FussS`
(`SperreFuss.lean:140-143`) and `FussSX`. A function whose body uses
`transition` on `R` gets no footprint cover for `m`'s carriers.
`Block.regs` faithfully propagates `s.regs`, so the loss is exactly
at the `Stmt.regs` catch-all. (`.regSchreib` also hits `_ => []`
but reads no register — correctly empty.) Whether `Stmt.gOk`
(`ZielOrtGeraetSem.lean:106-116`) admits `transition` without any
register check is the same root cause on the checker side; the
checker itself is off limits for this lane, so this audit books
only the footprint consequence. Repair: one explicit
`.transition` arm returning `[m]` (and, if intended, `[r]` for the
write side), owned by whoever owns `ZielOrtGeraetSem.lean`, with
the existing `fuss_regG`-style lemma extended. Priority P1.

### 2.3 Checked correct: written carriers are absent from `fussOrte` by design

`assignSlot/assignGlob/publish/schreibBytes` do not list the carrier
they write. This is NOT a gap: the static footprint feeds stability
of reads/contracts/invariants (`FussS`, `stabil_of_fussX`), while
writes are caught twice dynamically — once as recorded write events
(`schreibSlot/schreibGlob` always `merke` an event,
`Semantik.lean:113-118`) and once as memory deltas (`¬
TraegerGleich` disjunct in `ZugriffG`/`SchreibG`,
`RennfreiVoll.lean:513-518`). The race leg (`rennfrei_g`) keys on
the memory footprint, not on `fussOrte`. A consumer that needs "every
carrier this step may touch" must use `AccessList.lean`'s
`eintraege`/`zugriffG_voll`, never `fussOrte` — documented as a
consumer rule in §7 (T1).

### 2.4 F2: `callInd` names no callee contracts anywhere

`stmtOrteP`'s `.callInd` arm (`ZielOrt.lean:151`) lists `p.orte ++
args.orte`; the direct-call arm adds the callee's
`requires/ensures` carriers, which have no analogue for an unknown
target. `vertrag_stabilX` (`AtomarReplay.lean:77-80`) can therefore
never be instantiated for an indirect call. The callee's own reads
are covered by the callee's own `FussS` once it runs, but the
CALLER-side stability across the call — the exact property the
direct-call disjunct exists for — has no statement for `callInd`.
`Block.gOk`'s `bindCallInd` checks a signature allowlist `K n`
(`ZielOrtGeraetSem.lean:128`), which is admission, not footprint
cover. Bridge task (P1): the lowering/bridge consumer must treat
`callInd` conservatively (target set restricted by `K`/codec, or
refusal where the target set's contract union is not covered); a
`callInd`-aware footprint disjunct or an explicit OPEN marker at
`ZielOrt.lean:151` is missing.

### 2.5 F3: gate/oracle reads outside `args.orte` are trace-invisible

Writes: covered. `GutO` (`Satz.lean:967-...`) forces the oracle
answer to respect the declared write frame (`Rahmen`) and, where the
axiom's guards are held, to record declared writes as `axiomSpur`
write events (`axiomSpur_write_tab/glob`). Reads: NOT covered.
`D.Ax` (`Syntax.lean:166-175`) declares `aparams/aerg/aschreibt/
agschreibt/agruende` — there is no read-footprint field, and
`execStmt`'s `axiomCall`/`bindAxiom(Else)` arms record only
`σ.lese Λ args.orte`. A gate implementation (`O.wirkt`) that reads
a carrier outside `args.orte` produces no `lese` event and no memory
delta, hence `LiestG`/`ZugriffG` are both false for that carrier —
a silent read the footprint, the trace, and `AccessList` all miss.
If gate contracts declaring touched carriers exist elsewhere in the
Gabbro surface (the C-free lane's position is that syscall/gate
contracts are user logic in `linux.gab`-style bindings), the link
"gate contract orte ⊆ caller footprint" is not established at the
three extraction sites (`stmtOrteP` axiom arm, `blockOrteP`
bind arms, `GutO`). Bridge task (P1): either a read declaration on
`D.Ax` with extraction + `GutO` recording, or a proved lemma that
callers must cover gate-touched carriers in their own
`requires`/`args.orte` (then F3 closes as caller duty with a
checker-side check to name). Until then, consumers must treat every
gate step as touching its declared writes PLUS an unknown read set.

## 3. Event trace vs memory delta: who catches what

| Access kind | Recorded event? | Memory delta? | Caught by |
|---|---|---|---|
| plain read of carrier | `lese` ✓ | no | `LiestG` |
| plain write | `schreib*` ✓ | yes | `SchreibG` (both disjuncts) |
| gate declared write (guards held) | `axiomSpur` ✓ | yes | `SchreibG` |
| gate declared write (guards NOT held) | unconstrained (`GutO` conditional) | yes | memory disjunct only |
| gate read beyond `args.orte` | — | no | **nothing (F3)** |
| register/device access (`regLies/regSchreib/transition`) | — (oracle) | no carrier change | nothing on carriers — by design; device carriers via `fussOrteG` except F1 |
| `awaits` when invisible | — (hardware stop `.sichtbarkeit`) | no | stop class, not an access — correct |
| atomic (exchange / shared-atomic read) | same encoding as plain (`zugriffVon` has no atomicity bit, `RennfreiG.lean:19-23`) | yes/no as plain | trace + declaration join required (see §4) |
| async device write (§7.2 `Semantik.lean:1006`) | beside `Orakel.wirkt` | yes | memory disjunct only — check bridge accounts it as foreign write |

The `¬ TraegerGleich` disjunct is load-bearing for every oracle- or
device-adjacent write; any consumer that filters on `zugriffe`
membership alone (dropping the disjunct) re-opens all of §3 as
silent-write holes. `AccessList.lean`'s `schreibG_voll`/`zugriffG_voll`
keep the disjunct — correct; the rule is restated as consumer rule T1
in §7.

## 4. Granularity: carriers in, bytes out, no atomicity bit

- Source keys are whole carriers: `TraegerGleich`
  (`ZielOrt.lean:526`) compares whole `slots t` / `globs g`;
  `TraegerWert` (`AccessList.lean:27-35`) ships whole slot functions.
  Two source accesses to one carrier ALWAYS fully overlap; there is
  no sub-carrier distinction on the source side. Any byte-level
  overlap reasoning must therefore live entirely on the target side
  (it does: `fussDisjunktB`, `klassifiziere`) AFTER a proved
  carrier→byte layout map. That map is `TableLayout.lean` (work row
  C1, lane 345) — missing at HEAD (no such file). The bridge cannot
  discharge L-read's bytes→value step without it; `O-align` (B2,
  present) covers only the target-internal half.
- `zugriffe`/`eintraege` carry no atomicity marking: an `exchange`
  step's read+write events are indistinguishable in shape from a
  separate load+store pair except via the `ExchangeKopf` head
  predicate. The bridge must join every access with `D.atomar` /
  `GeteiltA` before any TSO/LOCK correspondence. `TSO-GX-BRUECKE.md`
  L-write already routes RMW through the `rmw` field and
  O-rely-values; this audit confirms the source encoding forces that
  join (it is not optional) and that `AccessList.IstRMW` is exactly
  the `ExchangeKopf` reuse to cite — correct within claim.
- Per-byte TSO is not multi-byte atomicity — respected everywhere
  checked: `einzelbyte_atomar` (`TSO.lean:445`) claims one byte only;
  `kein_atomarer_zugriff` (`Zugriffe.lean:540`) empties the false
  atomic reading by construction; `lock_xadd_atomar`
  (`LockedOps.lean:145`) assumes declared `ausgerichtet8` + empty own
  buffer and says "indivisible word update" over the full `Fuss`
  with tearing explicitly OPEN in CUTS. No finding.

## 5. Target-side footprint modules: correct within claim, two consumer gaps

- `Zugriffe.zugriff`: the CHECKED-POTENTIAL vs REALISED-SUCCESSFUL
  split (header `:5-20`, §7 refusal theorems) is the right contract
  and proved per constructor. Fetch footprint excluded by ownership
  (lane 319) — respected, no duplication found. Narrow/LOCK/fence
  forms absent because `Befehl` (14 pilot forms) has none — correctly
  stated, not silently inherited.
- `OverlapRefusal.zugriffOk`: base-alignment + per-byte containment
  in one region. Wrap-safety: containment is per byte
  (`fussEnthalten`), so a wrapping footprint is admitted only if
  every wrapped byte is in-region — sound as admission; the
  value-agreement lemma `einzelTraeger_wertUeberein` correctly
  carries the explicit `OhneUmbruch` premise instead of assuming it.
  No finding on the proved claims.
- **F5 (P2): `LockEreignis` has no overlap adapter.** Locked RMW
  events carry `lesen/schreiben : List Adresse` in the same
  `Fuss`-address vocabulary as `Zugriff`, but `OverlapRefusal`
  consumes only `Zugriff`. The adapter (project `LockEreignis` to its
  two footprints and reuse `fussDisjunktB`/`klassifiziere`) is
  trivial but unowned: neither module may import the other without
  an owner decision (single-owner principle). Today a consumer
  checking a locked access against a plain access (the core
  `exchange`-lowering shape) has no citable lemma.
- `LockedOps`: `lockSchritt` gates on empty own buffer + alignment +
  permissions with explicit `none` refusals — correct. `mfence_ordnung`
  proves the local-only barrier; the cross-core non-drain is correctly
  NOT claimed here. Its home (row B4 `FenceDrain.lean`) is missing at
  HEAD — planned work, not a bug in this module. Flag/register/RIP
  effects of XADD absent (`TSOZustand` has no flags/file) — booked in
  CUTS as consumer duty; the lowering consumer must carry them.
- `SpillPrivate.lean`: TSO-side freshness⇒disjointness⇒commutation
  proved; SCFG application marked WAITING on the 287 IR — legitimate
  incomplete deliverable, correctly labelled.

## 6. Missing bridge pieces touching footprints (planned rows, not bugs)

At HEAD there is no `X86/FenceDrain.lean` (B4), no
`X86/TableLayout.lean` (C1), no `X86/GateStub.lean` (C2), no
`X86/CostSummary.lean` (C3), no `X86/EntryState.lean` (C4), no
`X86/ValidatorSkeleton.lean` (C5), no `X86/NarrowOps.lean` (A1), no
`X86/ScalarFloat.lean` (A6), and no source-side atomic-duty audit
module (C6 `AtomicPayload`, lane 350 — the checker half of
`QUELLBRUECKE.md` §3.3). All are `WORK-ALLOCATION.md` §2 rows with
owners; this audit lists them only because each is on the footprint
path: B4 holds the foreign-drain non-theorem, C1 the carrier→byte
map, A1 the narrow-overlap rule, C6 the admitted-atomic footprint
membership checks. Do not invent bugs from their absence; do not
claim the chain closed without them.

## 7. Prioritized repair / bridge tasks

- **P0 — F4: the `luecke` refusal can never fire.** `accessList`
  unconditionally returns `.voll` (`AccessList.lean:64-65`), proved
  (`accessList_kein_luecke`). The generic completeness lemmas hold
  for EVERY step uniformly, so a genuinely uncovered access shape in
  a future rule (or a consumer misreading whole-carrier values as
  byte values) can never surface as `luecke`. The "explicit refusal,
  never silent drop" policy (work row B1) is currently vacuous on
  the producer side. Either add a per-rule classifier that CAN return
  `luecke` (75-rule table; the work the CUTS already books as OPEN),
  or downgrade the claim: `pruefeBefund` gates consumers, but today
  it gates nothing. Owner: whoever owns `AccessList.lean`.
- **P1 — F1: `Stmt.regs` transition arm.** One-line footprint fix +
  `fuss_regG`-style coverage lemma. Owner: `ZielOrtGeraetSem.lean`
  owner.
- **P1 — F2: `callInd` footprint cover.** Conservative consumer rule
  now (T2 below); `ZielOrt.lean:151` needs an OPEN marker or a
  target-set-union disjunct with its checker-side check named.
- **P1 — F3: gate read set.** Declare (`D.Ax` read field +
  extraction + `GutO` recording) or prove-and-name the caller-duty
  reading with its checker check. Until then T3 binds every
  consumer.
- **P2 — F5: `LockEreignis`↔`Zugriff` overlap adapter.** Assign to
  `OverlapRefusal.lean` or `LockedOps.lean` owner (not both).
- **P2 — Per-rule access table (74 rules beyond `exchange`).**
  `TSO-GX-BRUECKE.md:575-577` requires L-access-complete per rule;
  only `exchange_liest_schreibt` exists. Generic lemmas do not
  discharge rule-indexed consumers (`D-lower` micro-event labels).
  This is the largest known-open item on the footprint path; it is
  already OPEN in `AccessList.lean` CUTS `:241-244` — keep it open
  and scheduled, do not work around it with a second extraction.
- **P3 — Consumer rules (immediate, no Lean needed):**
  T1: never consume `zugriffe`/`eintraege` without the
  `¬ TraegerGleich` disjunct (`schreibG_voll`/`zugriffG_voll` keep
  it; dropping it loses gate/async/device writes).
  T2: treat `callInd` steps as touching the union of the allowed
  target set until F2 closes.
  T3: treat every gate step as touching declared writes plus an
  unknown read set until F3 closes.
  T4: join every source access with `D.atomar`/`GeteiltA` before
  any atomicity-sensitive target reasoning; never read RMW-ness off
  the `(carrier × Bool)` pair alone.

## 8. Reproduction notes

No new Lean files were added (doc lane; `grammatik/` untouched —
`git status` shows only the two owned documents). The positive cases
cited are the existing `decide` witnesses: `zugriff_lauf_zeuge` /
`zugriff_zeuge_im_fuss` (`Zugriffe.lean:591-604`), `nachbarBild_wohlgeformt`
+ `push/store_in_traeger_angenommen` (`OverlapRefusal.lean`),
`accessList_ta_zeuge` (`AccessList.lean:206`, 29-step two-thread run
with a memory-changing write and a recorded read), `lock_xadd_atomar_zeuge`
and `cas_erfolg_zeuge` (`LockedOps.lean`). The negative cases cited are
the planted refusals: `zugriff_*_versagt_kein_erfolg` (`Zugriffe.lean:467-526`),
`luecke_faellt` (`AccessList.lean:160`), `rmw_nur_mit_lock` +
split load-then-store refusal (`LockedOps.lean:417-440`),
`klassifiziere_verweigert_unbekannt` (`OverlapRefusal.lean:113`),
`keine_lock_zyklus_schranke`. F1-F3 were verified by reading the
defining arms against the executing arms (references above); they need
no probe to state and their repairs will carry their own probes.

---

*CUTS of this audit: no Lean theorem is proved here; F1-F3 are
code-reading findings with exact sites, not failing probes; the
severity ordering is the author's judgement; line numbers may drift;
`grammatik/` was not modified and no `./lean-bau` signal is claimed
for this document (nothing to build). The TSO/GX semantic bridge
itself (D-tso, L-read/write/view/step/run) is outside this audit's
scope and remains as `TSO-GX-BRUECKE.md` states it.*
