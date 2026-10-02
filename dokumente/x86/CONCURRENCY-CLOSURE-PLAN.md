# Concurrency closure plan: TSO target to source W/GX bridge

*Lane 605, report-only audit. Owns only this file (plus `MUSE-REPORT-605.md`).
No Lean change, no semantics change, no checker/Spec/goal change.
All file:line claims checked on branch `muse/605` in this clone.*

## 0. Verdict up front

The accepted producers are real but **disconnected**: each proves true facts
about its own machine, and none constructs a source W step from a target TSO
event. The closure is owned by four pending lanes with a strict dependency
order: **SourceMemory570 first, then TSOTrace596, then BridgeWrite573 and
BridgeRead574 in either order**. No lane may take the desired simulation as a
premise, replace source W with a per-byte toy, or claim closure from a
byte-level projection alone. A precise proved obstruction is a `blocked`
finding, never closure.

## 1. What each accepted producer actually hands over

### 1.1 `TSOHistory.lean` (lane 567, accepted)

Canonical byte-TSO history/view projection over `TSOZustand`
(`issueByte`, `loadByte`, `flushKern`): `histVon` (committed history:
timestamps 0 initial + 1 current canonical byte), `sichtVon` (per-core view:
1 iff own pending entry, else 0), `neuestens_jüngste` (youngest-own-entry
split), `load_lesbar_ohne_weiterleitung` / `weiterleitung_ist_jüngste`
(load cases), `issue_hist_bleibt` (issues invisible), and the key
`spülen_baut_frische_nachricht` (flush builds a `Frisch ... 2` message for
the OLD history + `Lesbar` in the NEW history). Proved refusal:
`fremd_weiterleitung_unsichtbar` (foreign forwarded value has NO committed
message). Joint witness `hist_zeuge_gelenk` (two-core, reached,
memory-changing flush). CUTS state the layer honestly: Address/Byte only, no
typed-carrier W/GX mapping, tearing shown (`hist_zerreissen`).

**Adequacy for 573/574:** hands `histVon`, `sichtVon`, fresh-message and
youngest-forwarding facts. Does NOT hand a growing history: timestamps are
projection-local (0/1/2 reused per flush, not a monotone counter), and
`Frisch ... 2` is the shape of one flush-built message, not coincidence with
source W timestamps.

### 1.2 Canonical TSO (`TSO.lean`, lane 284, accepted)

Real executable byte-TSO: per-core FIFO buffers, `issueByte` (permission
checked, memory unchanged: `issue_kein_speicher`), `loadByte` with youngest
own-buffer forwarding, `flushKern` writing canonical bytes
(`flush_schreibt_kopf`, frame `flush_rahmen`), FIFO (`fifo_reihenfolge`),
fence-as-gate (`zaunBereit_iff_leer`, `zaun_kein_fremd_drain`), store-buffering
witness `tso_store_buffering` (non-SC outcome reachable: both stale reads),
tearing `paket_reisst`, empty `LockSchritt` (`kein_lock_schritt`), and the
target-side view link `tso_last_lesbar` / `tso_frisch_beispiel` (instantiate
existing `Lesbar`/`Frisch` at target bytes only).

**Adequacy:** the actual executor 573/574 simulate FROM. Load-bearing limits:
per-byte flushes tear multi-byte packets; LOCK RMW is absent here (lives in
`LockedOps`); no source simulation (`TSOErreichbar` is target-only).

### 1.3 `AccessExecution.lean` (lane 568, accepted)

Connects checked potential footprint `Zugriffe.zugriff` to ACTUAL successful
`Ausfuehrung.schritt` / `Byteschritt.byteschritt` for all 14 pilot forms:
`realisiert_fuss_abdeckung` (uniform frame + empty-or-eight shape),
`byte_realisiert_fuss` (byte step carries a footprint decoded from actual
memory bytes), refusals `realisiert_versagt_laenge` /
`byte_ohne_fetch_kein_realisiert`, `realisiert_store64_wort_kein_atom`
(eight-byte set is NOT one atomic TSO event), joint witness
`realisiert_fuss_abdeckung_zeuge` (real reached memory-changing store).

**Adequacy:** the ONLY producer that ties footprints to executed decoded
bytes. What it does NOT give: no source correspondence, no W/GX mapping, no
concurrency (`lauf`/`laufBytes` are sequential folds), no LOCK/RMW/fence
forms (`Befehl` has 14 forms; locked forms live in `LockedOps.SperrBefehl`
and are NOT decoded pilot instructions).

### 1.4 `LockedOps.lean` (lane 339) + `WordAtomicity.lean` (lane 421)

`lockSchritt` (XADD-shape RMW bypassing the own buffer iff empty + aligned +
readable/writable; MFENCE as gate), `casSchritt` (success installs / failure
stutters), `lock_xadd_atomar` (one indivisible word update with full event
record), `mfence_ordnung`, `cas_schleife_unbeschraenkt` (retry cost
unbounded, proved), refusal `rmw_nur_mit_lock` (split load+store pair from
REAL `zugriff` footprints carries no RMW shape), witnesses
`locked_add_zwei_kerne`, `mfence_ordnung_zeuge`, CAS witnesses.
`WordAtomicity` adds the consumer guard `WortGuard`, read-back
`wort_schritt_liest_zurueck`, disjoint frame, three lock refusals, tearing
`wort_fuss_reisst` (byte-wise install inside one footprint tears), and the
empty bridge types `WortNachW` / `LockNachW` (explicit non-claims).

**Adequacy:** the only whole-word atomic update + the RMW/cost facts the
bridge needs (`rmw` field needs `neu = wahl.ts + 1`; cost needs
O-cas-cost shape per site). Limits: XADD flag/register/RIP effects NOT
modelled (`TSOZustand` has no flags/register file); alignment is a profile
contract, not silicon proof; no fetch/decode path for locked forms.

### 1.5 `AtomicPayload.lean` (lane 350, organisation plan C6)

Source-side atomic admission audit: decided check `atomarFussB` implying
`GeteiltV`, refusals for contract-mentioned and non-atomic carriers,
duty-side audit `audit_pflicht_deckt_aufgenommen` (`GeteiltV ⊆ GeteiltA`
narrowing), rely policy `audit_beobachtung_menge` (observations preserved as
a SET), payload boundary `nutzlast_braucht_restbeweis` (payload NOT admitted;
residue proof OPEN).

**Adequacy:** defines the EXACT admitted set `Tg := GeteiltV P ws` that
573/574 must map per access, and the rely (`HavocA (GeteiltA ...)`) whose
value domain the byte-concatenation lemma must respect. Does NOT construct
duties for atomic-bearing units (`nutzerA_aus_quelle` covers atomic-free
only) and claims no TSO correspondence.

### 1.6 Source W/GX/`Sicht` (accepted, reused unchanged)

`SchrittW` (`MaschineW.lean:150`): `schritt` (G steps on presented memory),
`lies` (`Lesbar` + `TraegerGleich`), `ungelesen` (G memory where unrecorded),
`frisch` (fresh timestamp above `vorSicht`), `histS`/`sichtS`/`sichtU`,
`lsicht`, `rmw` (`neu = wahl.ts + 1`). `Lesbar`/`Frisch`
(`Sicht.lean:133/139`). Reuse legs: `schwach_ist_gX` (`AtomarW.lean:279`),
`w_kein_verlust` (`RMW.lean:191`), `sicht_waechst` (`MaschineW.lean:269`).
Strategy doc: `dokumente/x86/TSO-GX-BRUECKE.md` (§5 items D-tso … L-run;
OBS-5, O-cas-cost, O-ord, O-align, O-lock, O-foreign-foot stay OPEN).

## 2. Snapshot `fresh2` facts vs a real preserved source W run

This distinction is the audit's load-bearing point; reviewers must enforce it:

- **Snapshot fact (what 567 proves):** `spülen_baut_frische_nachricht`
  shows timestamp 2 is `Frisch` for the OLD two-message history and the
  flushed value is `Lesbar` in the NEW two-message history. Both histories
  are FRESH snapshots (`histVon s`, `histVon s'`); no theorem relates a
  history at flush `n` to the history at flush `n+1` as an EXTENSION.
  Timestamps 0/1/2 are reused every flush. This is bounded legacy evidence,
  not a run.
- **Real preserved run (what 573/574 need):** an append-only source W
  history `W.hist` with strictly increasing fresh timestamps
  (`Frisch W.hist ... (neu c)` per `SchrittW.frisch`), previous messages
  preserved (`histU`), writer views joined (`sichtS`, `lsicht`), reached by
  `RufErreichbarW` from `RufStartW`, with `wahl`/`neu` witnesses per step.
  NOTHING accepted today constructs one from TSO events. TSOTrace596 owns
  exactly this gap on the target side (growing history + writer views);
  573/574 own the per-access construction of `wahl`/`neu` on the source side.

**Gate rule:** any 573/574 lemma whose conclusion is a `SchrittW` /
`RufSchrittGX` must exhibit `σ`, `M''`, `wahl`, `neu` built from the TSO
event + representation map, never assumed. A `Lesbar`-shaped hypothesis
about the desired read is the desired simulation as a premise: reject.

## 3. Exact interfaces needed by 573/574

### 3.1 Relation (per access, not per block)

Per dynamic TSO memory event (one flushed byte-group / one LOCK RMW / one
load micro-event): either SILENT (spill/private/lowering-internal: touches
no `Tg` carrier and no recorded carrier, cf. O-spill) or LABELLED with an
access-list index `(G-step rule, carrier `c : D.Tab ⊕ D.Glob`, read/write,
value)`. Counterexample B (`TSO-GX-BRUECKE.md` §2) forbids block
transactions: interleave at access granularity; W tolerates it (reads checked
independently against the pre-step view).

### 3.2 Access grouping

One source G step's lowering = one LABELLED GROUP (its access list) +
silent events. 573 assembles the group's stores into ONE `SchrittW`
(`histS` per written carrier); 574 shows each group load's TSO options ⊆
`Lesbar` options at its access. Grouping needs O-access completeness
(~70 `RufSchrittG` rules; only `exchange_liest_schreibt` exists as pattern):
until complete, 573/574 work on the ADMITTED REPRESENTED CARRIER PROFILE
(see §3.5) and keep everything else refused.

### 3.3 Shared atomic rely

`Tg := GeteiltV P ws`; duty quantifies over `HavocA (GeteiltA E.P E.ws)`
(total havoc on `Tg` outside the read list). 573/574 need the
byte-concatenation lemma: with O-align (below), the x86-observable value set
at each `Tg` carrier ⊆ the rely's value domain, via `einpassen` (undecodable
bytes refused, never havoc-guessed). Tearing breaks this: misaligned or
cross-carrier access = lowering refusal (no new diagnostic; manifest-level
precondition), witnessed by `paket_reisst` / `wort_fuss_reisst` applied to
the refused shape.

### 3.4 Own-buffer forwarding

Forwarded load = youngest own entry (`weiterleitung_ist_jüngste` split);
unforwarded load = canonical byte (`load_lesbar_ohne_weiterleitung`).
574 must map BOTH to `Lesbar` options at the access: forwarded value =
writer's own message (own view covers it via `sichtS`), unforwarded =
committed message at/above the reader view. `fremd_weiterleitung_unsichtbar`
is the negative gate: foreign pending values are NEVER `Lesbar` in the
committed history; a 574 claim admitting one is unsound.

### 3.5 Release/acquire views

Order-parametric simulation (O-ord): every shared x86 access justifies at
least `freigabe` behaviour; plain aligned MOV already carries
release/acquire on TSO; LOCK ops exceed it. Concretely: `lesesicht` /
`locksicht` / `vorSicht` joins simulated from TSO program order + flush
order + lock linearisation points (`tritt` acquire joins lock view, `gibt`
release joins thread view into lock). Proving only for `freigabe`
everywhere does NOT imply `entspannt` (different `beitrag` joins): the
simulation stays parametric over `ord`, never instantiated.

### 3.6 RMW / cost

LOCK XADD success = THE RMW access: `neu = wahl.ts + 1` + `w_kein_verlust`
pattern. CAS-loop failures = silent stutter (safety-harmless); cost is
SEPARATE: O-cas-cost per site ((i) static retry bound `k` from contention
structure, or (ii) DIVERGENCE: O-time transfer void for programs reaching
it, recorded per program). `cas_schleife_unbeschraenkt` + `keine_lock_zyklus_schranke`
forbid silent absorption of unbounded retries into "finite stutter".

### 3.7 Source carrier representation (from 570)

The ONE map 573/574 consume: source `Deklaration`/`Welt` table carriers
(bounded integer/table fragment) ↔ `TableLayout`/`Speicher` bytes, with
generic source table-write and target `write64`/`read64` preserving it +
disjoint-carrier frame. Needs: `execStmt` actual table writes (worlds from
`execStmt`/`exec`, never a second semantics), range/region/width/layout
premises, little-endian `wortByte` order matching carrier value encoding,
overlap/out-of-range/width-mismatch refusals, non-degenerate joint witness
(source table AND mapped bytes change). Sums/FP/fn-pointers stay explicit
cuts. Until 570 lands, 573/574 MUST NOT invent a byte→carrier guess: keep
unrepresented carriers refused and prove the obstruction (`blocked`) if the
profile cannot cover an access the pilot emits.

## 4. Prioritised gaps (concrete, ordered)

1. **G1 — growing history.** No append-only target history with monotone
   timestamps exists. Owner: TSOTrace596 (one-flush + finite-trace extension,
   preserving messages, FIFO, writer views; preserve `histVon` as legacy).
2. **G2 — carrier representation.** No source-carrier↔byte map. Owner:
   SourceMemory570. Blocks all of §3.3/§3.7.
3. **G3 — per-access write construction.** No `wahl`/`neu` from TSO flushes.
   Owner: BridgeWrite573 (needs G1+G2 interfaces, NOT their proofs to
   start: work against the STATED interface, keep unrepresented refused).
4. **G4 — per-access read simulation.** No TSO-load → `Lesbar` derivation.
   Owner: BridgeRead574 (same posture as G3).
5. **G5 — access completeness.** ~70 G rules lack access lists (O-access).
   Bounded form: complete ONLY the rules the admitted profile's lowering
   uses; everything else refused. Owner: follow-up of 573/574 or a new
   disjoint lane (not 605 business to assign numbers; coordinator allocates).
6. **G6 — group assembly + run induction.** L-step/L-run (§5 items 7–8 of the
   bridge doc). Owner: after G3+G4 accepted; needs O-spill silence proof +
   O-lock linearisation reuse.
7. **G7 — OBS-5 / O-ord / O-cas-cost / O-mmio / O-enable.** Per-lowering or
   per-binding proofs, several possibly ending in a REVIEWED `Spec.lean`
   diff. NOT 573/574 work; recorded so nobody claims closure past them.

## 5. Proposed bounded disjoint tasks (existing architecture only)

| # | Owner | Consumes (exact names) | Delivers | Proof / witness / refusal criteria |
|---|-------|------------------------|----------|-------------------------------------|
| T1 | TSOTrace596 | `TSOZustand`, `TSOSchritt`, `issueByte`, `flushKern`, `loadByte`, `histVon`, `sichtVon`, `spülen_baut_frische_nachricht`, `fifo_reihenfolge`, `Sicht.Lesbar`, `Sicht.Frisch` | `TSOTrace.lean`: append-only projection, one-flush + finite-trace extension | Generic extension preserving messages + latest value + FIFO; joint two-core trace writing/reading actual bytes with non-degenerate timestamps; forwarded-load case or precise obstruction; planted refusal (foreign pending invisible); standard axioms; `histVon` preserved |
| T2 | SourceMemory570 | `execStmt` table writes, `TableLayout`, `Speicher.write64/read64`, range/region/width premises | `SourceMemory.lean`: ONE representation interface + preservation both directions | Generic table-write ↔ byte-write preservation + disjoint frame; joint witness changing source table AND mapped bytes; overlap/out-of-range/width refusals; standard axioms |
| T3 | BridgeWrite573 | Accepted T1 + T2 interfaces, `SchrittW` fields (`frisch`, `histS`, `sichtS`), `WortGuard`, `lockSchritt_xadd_erfolg` | `BridgeWrite.lean`: per-access store issue/flush → W write | `wahl`/`neu` DERIVED per access; FIFO order kept; issue-vs-flush visibility explicit; `WortGuard` admission; two-core reached memory-changing witness; tearing + foreign-drain refusals; unrepresented profile refused, or `blocked` obstruction |
| T4 | BridgeRead574 | Accepted T1 + T2 interfaces, `SchrittW.lies`, `Lesbar`, `weiterleitung_ist_jüngste`, `schwach_ist_gX` (reuse ONLY after real W step derived) | `BridgeRead.lean`: per-access TSO load → W read | Value + view + rely duties preserved; youngest-forwarding + stale-history cases; two-core witness + stale/foreign/tearing negatives; no `Lesbar`-as-premise; no fairness/block claim |
| T5 | (coordinator) access-completeness slice | `LiestG`/`SchreibG`/`ZugriffG`, `exchange_liest_schreibt` pattern | Per-rule access lists for the admitted profile's rules only | One lemma per rule + joint inhabitation where the rule touches syntax; all other rules refused, never silently covered |

Dependencies: T1, T2 independent; T3, T4 need T1+T2 STATED interfaces
(they may start against the stated shape, but may not claim what T1/T2
have not proved); T5 parallelisable per rule. No lane touches
checker/`Spec`/goal, friend optimiser files, or another lane's owned paths.
New `TSOTrace596` owns growing histories; no conflicting writer of
`histVon`/`sichtVon` vocabulary.

## 6. Explicit non-goals restated (so reviewers can hold the line)

- No per-byte toy W: source W stays carrier-granular (`D.Tab ⊕ D.Glob`,
  `TraegerGleich`); byte facts are BELOW `Tg` until T2+T3/T4 actually bridge them.
- No desired-simulation premise: `Lesbar`/`Frisch`/`SchrittW`-shaped
  hypotheses about the event being mapped are rejectable on sight.
- No competing interpreters: one shared source semantics (`execStmt`/`exec`),
  canonical executor (`TSOZustand` ops + `schritt`/`byteschritt`); no extra
  IR without reviewed decision 594.
- Decoder/profile helpers are checked models, not silicon proof; encoder
  round-trip is not hardware correspondence (per handoff §11).
- A proved obstruction (`blocked` + exact refused shape + witness) is a
  GOOD outcome; a conjunction of checks labelled execution is not.

## CUTS (of this document)

- Design/audit only: no Lean theorem added; every file:line claim is
  checkable by `grep` in this clone.
- 570's interface is PENDING (read from `lanes/570.md` + bridge doc, not
  from an accepted module); if 570 lands with a different shape, §3.7 and
  T2/T3/T4 rows must be re-audited.
- Lane-number → owner mapping for T5+ is the coordinator registry's
  business; this plan proposes scope, not numbers.
- OBS-5, O-ord, O-cas-cost, O-time, O-mmio, O-enable, O-irq, O-spawn remain
  OPEN per `TSO-GX-BRUECKE.md`; this plan orders them after G1–G6.
