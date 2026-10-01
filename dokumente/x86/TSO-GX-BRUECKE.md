# x86-TSO to W/GX bridge: exact refinement obligations

*Lane 274, wave A, 2026-10-01. Docs-only design task: no Lean file, no model
change, no goal-statement change. All definition claims below were checked
against the tree on branch `muse/274`; file:line references are part of the
claim. Namespace of the source model is `Gabbro.Grammatik` (X86 pilot:
`Gabbro.Grammatik.X86`).*

## 0. Verdict up front

**Strategy: per-access forward simulation from an x86-TSO machine into W,
then reuse of the existing DRF leg to land in GX.** The required refinement
direction is `x86 behaviours ⊆ W behaviours` (W over-approximates), followed
by `schwach_ist_gX` (AtomarW.lean:279), which collapses W steps to GX steps
on checked programs. Nothing in the goal statement moves: the bridge
instantiates the existing `SchwachX` leg (Spec.lean:2200), whose conclusion
is already `RufSchrittGX ... /\ σ agrees outside Tg`.

**What is reused, exactly:**

- (a) `PrueferX` (Spec.lean:2137), sound against `AkzeptiertSpecX`
  (Spec.lean:2109), whose footprint rule `fuss` admits exactly the shared
  atomics `GeteiltV P ws` (Spec.lean:2104) beside signature-guarded,
  thread-local and lock-protected carriers.
- (b) `NutzerPflichtA` (Spec.lean:2152): every body against EVERY atomic
  environment satisfying `HavocA (GeteiltA E.P E.ws)` (AtomarSem.lean:49).
- Conclusion legs `ZielX`/`ZielFX` (Spec.lean:2218/2254) over GX runs:
  `schwach` (`SchwachX`), `rennfrei` (`RennfreiBisGA`, Spec.lean:2125),
  `sperrWechsel`/`sperrSicht` (`SperrWechselGX`/`SperrSichtGX`,
  Spec.lean:2157/2165, both over GX *steps*), `zeit` (`ZeitAbX`,
  Spec.lean:2210, over `SegLaufX` runs), `fortschritt` (`FortschrittG`,
  Spec.lean:1828), `keinKernHalt` (`KernHaltEA`, Spec.lean:2188, over GA
  runs), `folge` (`FolgeG`, via `folgeG_erreichbarX`, BeweisAtomar.lean:149),
  plus the contract/invariant legs via `ziel_ort_atomar`
  (AtomarLauf.lean:404).

**Granularity finding (the load-bearing one): one source G step contains
several memory accesses, so the bridge must decompose G steps into access
lists; mapping a G step to one uninterrupted x86 block is unsound-by-
incompleteness (§2, counterexample B).** No blanket assumption "x86 is
W/DRF-SC" is made anywhere in this design; store buffering refutes it (§2,
counterexample A).

### Status convention (review repair, 2026-10-01)

- [PROVED] — a Lean theorem in the tree (with file:line). May be reused.
- [REUSE] — an existing proved leg/theorem applied unchanged.
- [PROPOSAL] — a design decision of this document (strategy, refinement
  direction, linearisation points). Not proved.
- [OPEN] — an unproved obligation. Some [OPEN] items are routine wave-B
  work; three of them (OBS-5 in §4.9, liveness scope in §4.10, CAS cost
  in §4.11) could, if they resist discharge, require a REVIEWED
  `Spec.lean` diff — i.e. a statement change. This document does NOT
  pre-conclude that no such change will be needed; §6.9 is corrected
  accordingly. "No change to the goal statement" in the lane task means
  this lane changes nothing; it does not mean the simulation proof will
  need nothing.

## 1. What the REAL definitions say (checked, not from headers)

### 1.1 One G step is coarse and multi-access

`RufSchrittG` (RufMaschineG.lean:263) has ~70 rules; one rule fires per
thread step. Two rules carry the whole granularity argument:

- `blatt` (RufMaschineG.lean:265) / `dannBlatt` (RufMaschineG.lean:354):
  run a whole *leaf* statement `s` (`s.istBlatt = true`) through `execStmt`
  in ONE step. `execStmt` reads every carrier its expressions name and
  writes every carrier the leaf assigns. A leaf such as a float op reads
  `a.orte ++ b.orte` (cf. `dannGleit`, RufMaschineG.lean:1957);
  nothing in the rule restricts a leaf to one read or one write.
- `dannExchange` (RufMaschineG.lean:1933): at an `exchange g neuE` head,
  read `σ₁ = (M.weltVon f).lese Λ (.inr g :: neuE.orte)` — the global `g`
  AND every carrier the update expression reads — then write
  `σ₂ = σ₁.schreibGlob g Λ ...`, all in ONE G step. An exchange step of G
  therefore reads `g`, reads arbitrarily many further carriers, and writes
  `g`, atomically as one source step.

Access recording: `LiestG M M' u c` (RennfreiVoll.lean:522) is
`(c, false) ∈ zugriffe M M' u` — a *recorded read event only*.
`ZugriffG` (RennfreiVoll.lean:513) is a recorded event OR a changed value;
`SchreibG` (RennfreiVoll.lean:517) is a recorded write event OR a changed
value. Consequence: a step can *change* a carrier it never recorded a read
of, and the W step's `lies` field only constrains recorded reads.

### 1.2 W reads old values only where G recorded a read

`SchrittW` (MaschineW.lean:150) presents memory `σ` with four load-bearing
fields: `lies` (at a recorded read, `σ` holds SOME message at or above
the reader's view — `Lesbar`, not necessarily newest), `ungelesen` (at an
unrecorded carrier, `σ` IS G's memory), `frisch` (every write takes a
`Frisch` timestamp strictly above the pre-step view), and `rmw` (an
exchange of `g` writes at exactly `(wahl (.inr g)).ts + 1`).
MachineW.lean's own header states the granularity explicitly: a W step is
one coarse G step, every read is checked against the *pre-step* view, and a
release message carries the view *before* the step's own writes (weaker
than C11 — safe direction).

Unrecorded reads are SC by construction: `Orakel.wirkt`, `O.regLies`,
`O.sichtbar` (Semantik.lean:454) and `axiomAntwort` read over G's memory
wherever the step does not record. That the foreign side, the device and
the `awaits` hand-off see *that* memory — the last executed write — is
assumption (5) of the Spec header, ASSUMED, not derived. The TSO bridge
must discharge or re-state it at every foreign/device boundary (§4.8).

### 1.3 GX is G with shared atomics answered elsewhere

`RufSchrittGX` (AtomarLauf.lean:33): a G step on a presented memory `σ`
that agrees with G's at every carrier outside `Tg`, successor taking
written carriers from the step. `schwach_ist_gX` (AtomarW.lean:279) says:
under `GutO`, closed call graphs, `FussSX` footprints, locality, and
`hTA : ∀ c, Tg c → AtomarAusgenommen c`, every W step from a reached state
IS a GX step and its `σ` agrees with G's outside `Tg`. `gx_ga`
(AtomarLauf.lean:55) embeds GX in GA when `Tg` is inside the atomics;
`gx_leer_g` (GXMaschine.lean:48) collapses GX to G when `Tg` is empty;
`w_aus_g` (MaschineW.lean:586) embeds every G run in W.

RMW facts: `exchange_liest_schreibt` (RMW.lean:117) — an exchange step
reads AND writes its global (inversion over the G rules; only
`dannExchange` fires at such a head); `w_kein_verlust` (RMW.lean:191) — no
two exchanges read one message, from the `ts + 1` rule.

## 2. Why ordinary block atomicity cannot be assumed

Three concrete counterexamples, each with the trace that refutes the
shortcut. All use the REAL litmus facts of Sicht.lean, not slogans.

### Counterexample A — store buffering is not SC

`sb_erlaubt` (Sicht.lean:446): with release stores and acquire loads,
thread 0 does `x := 1; r0 := y`, thread 1 does `y := 1; r0 := x`; the
outcome `r0 = 0` on both sides is REACHABLE on the weak machine. On the SC
machine (`LSchrittSC`: reads take the newest, writes append) the same
outcome is NOT reachable: `sb_sc_verboten` (Sicht.lean:566). x86-TSO
admits exactly this outcome (both loads bypass the thread's own buffered
store). **Any bridge step that assumes "x86 behaves as SC", or that maps
x86 runs to G runs directly, is refuted by this four-step trace.** The
bridge must target W (which admits it), never G, for the memory part.
Note the sharp edge: W models `seq_cst` as release/acquire (Sicht.lean:33,
an OVER-approximation that keeps SB even where RC11 forbids it for `seq`).
For the TSO bridge this over-approximation is soundness-safe — x86 can
only exhibit *fewer* behaviours than W admits — but it must be named, not
silent: the day a `seq` total-order leg is added, this paragraph becomes a
gap (see §6.4).

### Counterexample B — a G step's lowering interleaves

Take `let x = g exchange update(h) { ... }` where `h` is a second shared
atomic admitted in `Tg`. One G step (`dannExchange`) reads `g`, reads `h`
(inside `neuE.orte`), computes, and writes `g`. Any x86 lowering emits at
least: load `h`; locked RMW (or CAS loop) on `g`. The following x86 trace
is REAL and must be mapped: T0 loads `h = 0`; T1 stores `h = 1` (buffered,
then flushed); T0's locked RMW on `g` commits, having computed from the
stale `h = 0`. A bridge that maps each G step to one uninterrupted x86
block has NO image for this trace — the interleaving lands strictly inside
the block — so the bridge would be incomplete, and incompleteness here is
unsoundness of the validation claim (a real binary behaviour with no
source-side justification). W, by contrast, ADMITS this trace: the two
reads are checked independently against the pre-step view (`lies` per
carrier, `lesesicht` folds each contribution). **Hence the bridge must be
per-access: decompose each G step into its access list
(reads with values, writes with values, RMW flag), map each x86 dynamic
memory event to one access, and interleave at access granularity.**
The existing pattern for access extraction is `exchange_liest_schreibt`;
it must be repeated for all ~70 rules (obligation O-access, §5).

### Counterexample C — tearing has no single W message

A W write installs ONE message carrying the whole post-step carrier value
(`histS`, MaschineW.lean:173; a carrier `D.Tab ⊕ D.Glob` is one location).
An x86 8-byte store to a misaligned address, or any access overlapping two
source carriers, can tear: two observers see different halves, and NO
single W message corresponds to the event. **Obligation O-align: the
lowering must prove every emitted shared access naturally aligned,
fully inside one carrier extent, and non-overlapping with any other live
carrier; byte-level x86 memory (`X86/Typen.lean`: `Speicher.bytes`,
per-byte permissions) must be related to carrier-granular `Speicher D`
by a proved access-to-bytes mapping.** Overlap also breaks `FussSX`'s
carrier reasoning (AtomarReplay.lean:29), which is per-carrier. This is
partly lane 269's inventory (widths/orders); the proof obligation is
stated here.

## 3. Precise reuse points (hypotheses and directions checked)

### 3.1 (a) `PrueferX` / `AkzeptiertSpecX` — what the bridge may assume, and what it must supply

`AkzeptiertSpecX.fuss` (Spec.lean:2112) is
`∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws) f`, i.e. every footprint
carrier of every body is signature-guarded, thread-local (`lokW`), or
lock-protected — OR an admitted shared atomic (`FussSX`,
AtomarReplay.lean:29; second conjunct: register carriers are always
guarded/local). The `renn` field (Spec.lean:2117) covers only NON-atomic
carriers. For the TSO bridge:

- O-checker-Tg: the bridge sets `Tg := GeteiltV P ws` (the unit's admitted
  shared atomics, Spec.lean:2104: `GeteiltA` + `VertragsFrei`). Every
  carrier in `Tg` must be lowered to an x86 access the TSO model covers
  (plain aligned MOV or LOCK-prefixed op — §4.3). `hTA`
  (`∀ c, Tg c → AtomarAusgenommen c`, premise of `schwach_ist_gX`) is then
  exactly this lowering contract.
- O-checker-race: every NON-`Tg` carrier's x86 accesses must be race-free
  at the x86 level whenever the source DRF argument needs it — the DRF leg
  concludes `σ` agrees with G's outside `Tg` (`praesentiert_gX`,
  AtomarW.lean:94), and that conclusion is false if the binary has an x86
  data race on a plain carrier the source proof calls thread-local. In
  practice: spill slots, lowering temporaries and register-home stack
  slots must be proved thread-local (`GetrenntK`) or lock-guarded at the
  x86 level (§4.5). No new checker rule is needed (wave-A rule); the proof
  is per-lowering.

### 3.2 (b) `NutzerPflichtA` — the rely already quantifies over everything

`KoerperGutSA` (AtomarRec.lean:39): each body, run by `execEndHA` against
EVERY `O'`, `U` (`HavocOk`) and EVERY `A` with `HavocA T A`, meets its
contracts and never ends in `logik`. `HavocA T A` (AtomarSem.lean:49)
says: `A` changes at most the carriers in `X ∩ T` — otherwise the rely is
*total havoc* on `T`: any value, any time. With `T = GeteiltA E.P E.ws`
(Spec.lean:2153; note it is `GeteiltA`, :2100, not `GeteiltV` — the duty
covers shared atomics even where a contract mentions them;
`koerperGutSA_mono` narrows `GeteiltV ⊆ GeteiltA` inside `zielX_aus`,
BeweisAtomar.lean:222). For the TSO bridge this is the good direction:

- O-rely-values: every value an x86 access can observe at a `Tg` carrier
  must lie in the rely's domain. Concretely: x86 loads return bytes;
  `einpassen` (Semantik.lean:425) refuses unrepresentable raw answers, and
  the decoded value reaching the source read is always a well-typed value
  — prove that the x86-observable value set at each `Tg` carrier is a
  subset of what `HavocA` quantifies over. Tearing would break this (see
  O-align); with O-align it is a byte-concatenation lemma.
- O-rely-oota: W is promise-free (Sicht.lean header: no load buffering,
  `po ∪ rf` acyclic, no out-of-thin-air). x86-TSO likewise forbids
  load-buffering outcomes. The bridge must state this alignment explicitly
  (TSO's causation structure implies no OOTA) rather than inherit it
  silently — a C++-memory-model lowering would NOT have it for free.

### 3.3 Conclusion legs — which machine each lives on

- `schwach : SchwachX` (Spec.lean:2200): for EVERY `ord`, every W-run from
  `RufStartW M0` reaching `W` with `W.g = M`, every `SchrittW` from `W`
  yields `RufSchrittGX P O passes Tg M u W'.g` AND `σ` agrees with G's
  outside `Tg`. This is the bridge's landing zone: the TSO simulation must
  PRODUCE `wahl`/`neu` witnesses turning each x86 step-group into a
  `SchrittW`, then `schwach_ist_gX` applies. Note the universal `ord`:
  the source declaration's orders are not carried by the exporter
  (MaschineW.lean header), so the lowering must refine W under ALL order
  assignments — obligation O-ord: prove the simulation order-parametric,
  i.e. every shared x86 access must justify at least the `freigabe`
  behaviour (on TSO, plain aligned MOV already has release/acquire
  semantics; LOCK-prefixed ops exceed it). Proving for `freigabe`
  everywhere does NOT imply `entspannt` for free (different `beitrag`
  joins) — the simulation must be parametric, not instantiated.
- `rennfrei : RennfreiBisGA` (Spec.lean:2125): over GA runs, non-atomic
  carriers only. x86 races on plain carriers are out of scope of the
  conclusion — they must be excluded by O-checker-race, not modelled.
- `sperrWechsel : SperrWechselGX` / `sperrSicht : SperrSichtGX`
  (Spec.lean:2157/2165): quantified over GX STEPS. The x86 lock lowering
  must linearise: each take/release takes effect at exactly one GX step
  boundary (obligation O-lock, §4.6). The ticket lock's four instructions
  (`zieht`/`dreht`/`tritt`/`gibt`, CTicket.lean header) vs G's `nimmt`/
  `gibt` events (RennfreiVoll.lean:732/738): `tritt` (return of `L_nimm`)
  and `gibt` (release store) are the linearisation points; `dreht` spins
  are stutter.
- `zeit : ZeitAbX` (Spec.lean:2210): per-thread GX-step counts
  (`segZaehleX`, GXMaschine.lean:288) bounded by `kostenTief`, proved by
  `frame_schritte_beschraenktX` (GXMaschine.lean:344) — which holds
  *whatever the weak memory answers*. x86 instruction counts are a
  TRANSFER on top: obligation O-time (§4.11): a per-G-rule worst-case x86
  instruction bound (valid only with O-cas-cost shape (i) on the
  program's paths), composed with `ZeitAbX`.
  Lane 278 owns timing; this document states the interface.
- `fortschritt : FortschrittG` (Spec.lean:1828): per-state enabledness —
  finished, waiting, named-stopped (flag, budget, hardware,
  `nieZurueck`), or able to step. No eventuality, no fairness in the
  statement. x86 spins (ticket `dreht`, CAS retries, lowering loops) do
  not threaten it; the binary-level need is enabledness preservation
  (O-enable, §4.10), and no fairness assumption is invented (§4.10).
- `keinKernHalt : KernHaltEA` (Spec.lean:2188): over GA runs with the
  hardware schedule `KernPlan` (Spec.lean:1858): handler entry only when
  unmasked + run-to-completion. Obligation O-irq (§4.7): map `cli`/`sti`
  (resp. the lowered masking) to `D.maskiert`, drain the store buffer at
  handler entry (a handler reading stale buffered stores breaks the
  entry-only-when-unmasked reading), and name run-to-completion as a
  hardware assumption.
- `folge : FolgeG`: thread-local call-log order (`folgeG_erreichbarX`,
  BeweisAtomar.lean:149). Control-flow lowering must preserve the
  directly-behind-return shape (L50/L52); memory-model independent, but
  the optimiser wave must not insert calls between a named return and its
  log entry — recorded here so lane 275 does not break it.
- Contract/invariant legs (`vertrag`, `invRueck`, `invGrund`, `invRuhe`,
  `invSicht`, `sperrInv`, `startEnde`, `keinStartGrund`, `keinLogikHalt`,
  deadlock legs): via `ziel_ort_atomar` (AtomarLauf.lean:404) and
  `zielInvSA_erreichbarGX` (AtomarLauf.lean:286) from `KoerperGutSA` —
  fully reused once the TSO trace is a GX trace. No per-leg x86 work
  except through the obligations above.

## 4. Topic obligations

### 4.1 Store-buffer forwarding and flush

W admits both: the writer reads its own write (`sichtS` sets the view to
the fresh timestamp; a later `Lesbar` includes the own message), other
threads may read older messages (`Lesbar` = any message at/above view),
and flush timing is invisible (any flush order is some `Lesbar` choice
sequence). Obligation O-tso-read: for each x86 load micro-event, the set
of values TSO permits (own-buffer forward OR memory at flush state) is a
subset of the `Lesbar` options at that access. Obligation O-tso-write:
each OBSERVED x86 flush (finite traces only — no "eventually flushes"
claim; liveness of flushing is not needed for any leg, §4.10) takes a
`Frisch` timestamp (strictly above the acting thread's pre-step view — holds because
views only grow, `sicht_waechst`, MaschineW.lean:269, and flush order
respects per-core FIFO, so a monotone counter works). Same-core FIFO write
order (TSO) is STRONGER than W (MaschineW.lean header: a write may take any
fresh timestamp, two writers ordered either way) — safe direction: every
TSO flush order is an admissible W timestamp choice, not vice versa. The
simulation must NOT require W to be FIFO.

### 4.2 Alignment, overlap, tearing — see O-align (§2, counterexample C)

Byte memory of the pilot (`X86/Typen.lean`: `Speicher.bytes`,
per-address `lesbar`/`schreibbar`) vs carrier memory `Speicher D`.
Every shared x86 access must be proved to touch exactly the bytes of one
carrier, naturally aligned, with the pilot's little-endian mapping
(lane 271) matching the carrier's value encoding. Unaligned or
cross-carrier accesses are REFUSED by the lowering (a lowering refusal,
not a new diagnostic — wave A mints none).

### 4.3 Locked RMW and CAS retries

x86 `LOCK`-prefixed RMW = full barrier + single atomicity unit. Maps to
W's `rmw` field (`neu = wahl.ts + 1`) + `w_kein_verlust` (RMW.lean:191).
The emitter's fragment (Sicht.lean header): release/acquire declaration
→ `memory_order_release` store / `acquire` load / `acq_rel` fetch-RMW
(`holordnung`); CAS loop with release-on-success, acquire on the load;
`seq` → `seq_cst` both sides; `relaxed`/no word → `relaxed`. On x86-TSO:
plain MOV covers relaxed AND release/acquire (TSO's ordering); `seq_cst`
lowered to LOCK-prefixed op or MFENCE-bracketed MOV covers `seq_cst` and
a fortiori W's `freigabe` modelling (§2.A). CAS loops: failed attempts are
silent x86 steps (stutter for the safety legs, §4.10; cost §4.11); the successful attempt is THE RMW access
of the access list; the update computation's input reads are ordinary
accesses of the same G step (counterexample B shape — explicitly allowed).
CAS cost/divergence is obligation O-cas-cost (§4.11), which REPLACES the
earlier O-cas wording: there is no "fairness assumption" alternative that
keeps a constant bound — unbounded retries void the bound.

### 4.4 Release / acquire / seq-cst

Covered in §§3.3 (O-ord) and 4.3. No fence instructions are emitted for
this fragment (Sicht.lean header: no `atomic_thread_fence`, no
`consume`); TSO needs none for release/acquire. `seq` needs the LOCK (or
equivalent) only because of the C11-level promise, not because W demands
it — W's `freigabe` modelling is weaker. Document the lowering choice per
declaration order; do not claim a `seq_cst` total order anywhere.

### 4.5 Private spills and lowering temporaries

Register allocation spills, caller-save areas and lowering temporaries
live in thread-private stack slots. Obligation O-spill: each such slot is
proved `GetrenntK` (never in any other thread's call-graph footprint, never
in `Tg`, never observed by oracle/device code) — then the DRF legs ignore
it exactly as they ignore source thread-locals. Stack memory is ordinary
WB memory; red-zone / signal-handler clobbering must be excluded by the
ABI contract (lane 276), not here.

### 4.6 Locks: take/release, ticket linearisation

The C model treats `L_nimm`/`L_gib` as acquire/release (`treiber.rs`;
Sicht.lean header). The proved ticket lock (CTicket.lean) refines
`sperrAbstrakt` with linearisation at `tritt` (lock now held) and `gibt`
(lock released); `zieht` allocates the ticket (thread-local `my`),
`dreht` spins (stutter). For x86: the lock words are `Tg` carriers with
LOCK-prefixed accesses; `tritt`'s load is the acquire that joins the
lock view (`locksicht`, MaschineW.lean:112), `gibt`'s store is the release
joining the thread view into the lock (`lsicht` field, MaschineW.lean:183).
Obligation O-lock: prove the x86 lock template's `tritt`/`gibt` implement
exactly the `genommenVon`/`gegebenVon` events (RennfreiVoll.lean pattern:
`genommen_von`, `gegeben_von`, DRF.lean:186/197) of the corresponding GX
step, so `SperrWechselGX`/`SperrSichtGX` see them at a step boundary.
`ticket_mehr_als_frei` / `gib_ohne_wache` (CTicket.lean header: where the
concrete lock says more/less than the spec) must be re-checked for the
x86 template — they are template-specific, not inherited.

### 4.7 Start / join

`FadenSchrittX.start/kind/join` (GXMaschine.lean:92/100/105) move no G
memory except through the acting thread's state; the invariant
`FadenInvX` (GXMaschine.lean:181) carries reachability across them.
x86 thread creation (`clone`-family via the runtime's thread template,
lane 278/276 territory) is a full barrier on real hardware (syscall
boundary). Obligation O-spawn: the spawning thread's store buffer is
drained before the child observes memory, and the child's initial views
join the spawner's views at the spawn point (mirroring `vorSicht`'s lock
join); join symmetrically. Without the drain, the child's first reads
would be stale beyond any `Lesbar` option. [OPEN] The drain covers the
spawner's buffer; visibility of OTHER cores' writes to the child is the
same publication problem as OBS-5 (iii) (§4.9) — recorded there, not
resolved here.

### 4.8 Interrupts

O-irq: (i) map the lowered interrupt masking to `D.maskiert` and the
  handler roots to `P.unterbricht` (`HandlerVon`, Spec.lean:1871);
(ii) drain the interrupted thread's store buffer at handler entry (a
handler is a new x86 observer; undrained stores would let it read older
values than its W view permits) — local drain only; visibility of other
cores' writes to the handler falls under OBS-5 (§4.9); (iii) keep `KernPlan`
run-to-completion as a NAMED hardware assumption — x86 does not guarantee
it (higher-priority interrupts, NMIs, faults inside the handler);
(iv) handler accesses to `Tg` carriers are recorded accesses of a GX step
of the handler thread (they are ordinary steps, `FadenSchrittX.lauf`),
while handler interaction with devices is foreign (assumption (5)).

### 4.9 Unrecorded oracle accesses — open observation OBS-5 (review repair)

Assumption (5) (Spec header): `Orakel.wirkt`, `axiomAntwort`, `O.regLies`,
`O.sichtbar` read G's memory — the LAST write — wherever the step records
nothing (`ungelesen`, MaschineW.lean:160). On x86 these are: foreign calls
(`extern`/syscall gates), device-register reads, and the `awaits`
visibility check.

[OPEN] OBS-5: a LOCAL drain (MFENCE on the acting core) is necessary but
NOT sufficient, and "MFENCE everywhere" does not resolve assumption (5).
A local fence makes the acting core's own buffered writes visible; it
does NOT make every OTHER core's last issued write visible to the
unrecorded reader. But assumption (5) demands the reader see G's memory —
the last executed write, whichever thread executed it. The gap between
"my buffer is drained" and "every core's last write is visible" is the
open obligation. It decomposes into four proof needs, recorded here, not
discharged:

- (i) Footprint [PROVED facts, OPEN question]: `RegLokal`
  (ZielOrtGeraetSem.lean:48) pins `regLies r` to the declared device
  carriers `D.rtraeger r` and `sichtbar g` to `g` alone — those readers'
  observable sets are bounded. But `Orakel.wirkt`'s READ footprint is NOT
  bounded by the model: `RahmenO` (ZielOrtVollBeweis.lean:48) constrains
  only what an axiom WRITES (declared frames), and `GutO`
  (Satz.lean:967) constrains the trace shape and held locks, not which
  carriers the foreign side reads. So which carriers a foreign call may
  observe is an OPEN per-binding question (obligation O-foreign-foot):
  for each `extern`/syscall gate, prove which carriers its result can
  depend on — from the binding's contract and implementation, not from
  the generic model.
- (ii) Ownership [PROPOSAL, dischargeable]: where the observed carrier is
  thread-local to the acting thread (`GetrenntK`) or protected by a lock
  the acting thread holds with no concurrent writer possible, no other
  core holds an unflushed write — local drain IS sufficient. This is the
  only case MFENCE-before-the-call closes. The bridge must sort every
  unrecorded-read site into this case or the next two; the sorting proof
  is per lowering+binding.
- (iii) Lock/publication chains [OPEN, proof required]: where the observed
  carrier was written by another thread (e.g. published before unlock,
  read by the foreign side after), visibility needs the RELEASER's writes
  flushed — a TSO-level publication lemma. A LOCK-prefixed acquire on the
  reader's core does NOT flush other cores' buffers; the argument must go
  through coherence/flush ordering (or the x86 DRF-SC shape), and must be
  PROVED for the exact lock template in use (cf. O-lock), not assumed.
  Until proved, this is the load-bearing hole in reusing assumption (5)
  for x86.
- (iv) User/binding implementations [OPEN]: OS and binding calls are user
  logic, never assumptions (AGENTS.md §3): the Gabbro-side syscall gates
  and binding libraries that mediate sharing (e.g. thread-start, join
  words, OS-published memory) must carry visibility in their CONTRACTS
  (`ensures`), proved as user logic. Publication that the OS performs
  (scheduler, clone, futex wake) lands here as the binding's proof
  burden, not as a hardware assumption.

Consequence [OPEN]: if any of (i)–(iv) cannot be discharged at
lowering/binding level, assumption (5) as stated does not cover the x86
target, and a REVIEWED `Spec.lean` diff (a narrowed assumption (5) plus
the corresponding proof adjustments) would be required. Whether that is
needed is decided by the simulation proof, not by this document. The
DMA-style concurrent foreign writer stays excluded regardless (§4.12).

O-spawn (§4.7) is the one instance of (iii) already identified: the
spawning thread's buffer drained before the child observes + the child's
initial views joining the spawner's — kept as a lowering constraint, now
marked [OPEN] pending the publication lemma.

### 4.10 Stuttering and progress — exact claim first (review repair)

[REUSE] What `FortschrittG` (Spec.lean:1828) actually claims, verbatim in
meaning: at a reached machine `M`, every thread `t` satisfies ONE
disjunct — `FertigG M t` (finished), `WartetG M t` (waits for a lock or a
publication), a NAMED stop (`HaltBenannt`: `.flagge`, `.budget`,
`.hardware`, `.nieZurueck`), or `∃ M', RufSchrittG P O passes M t M'`
(it CAN step). That is per-state ENABLEDNESS. It claims no eventuality:
not that a thread will run, not that a spin terminates, not that a
buffered store becomes visible. There is no scheduler and no fairness in
its statement.

Consequences for the bridge:

- Spins and CAS retries do NOT threaten `fortschritt`: a thread whose G
  state has an enabled step satisfies the existential no matter how many
  silent x86 micro-steps (ticket `dreht`, CAS-loop failures, spill
  traffic, lowering expansion) its lowering takes. The earlier draft's
  O-stutter item (ii)–(iii) is WITHDRAWN as a `FortschrittG` need: no
  termination proof for spins is required by any existing leg, and no
  scheduler fairness or hardware buffer fairness may be invented to
  transfer a stronger eventual-execution guarantee than the goal states.
  Binary-level liveness beyond enabledness is NOT CLAIMED — consistent
  with the Spec header (starvation freedom out of scope).
- What `fortschritt` DOES need at the binary level is enabledness
  preservation [OPEN, O-enable]: where G can step, the lowered machine
  code at that state must not be stuck — i.e. no fault the source has
  none of. The named stops need x86 counterparts: budget exhaustion is a
  G-level counter (unaffected by lowering); `.hardware` stops (faults:
  #GP/#PF/divide errors) must be classified per emitted form — lane 272's
  witnesses plus lane 276's image contract feed this; a fault the binary
  takes where G has none is a gap, not a refinement.
- Silent steps remain harmless for the safety legs (`schwach` sees only
  access events; `rennfrei`/`sperrSicht` read access records). Their COST
  is a separate obligation and is NOT absorbed here — see §4.11.

### 4.11 Time and the CAS divergence obligation (review repair)

`ZeitAbX` bounds per-thread GX-step counts (`segZaehleX`) by
`kostenTief`, independent of memory answers
(`frame_schritte_beschraenktX`) [REUSE]. A source exchange is ONE G step:
constant model cost. Its x86 lowering as a CAS loop is UNBOUNDED in retry
count. These two facts together force an explicit divergence/cost
obligation — [OPEN] O-cas-cost: NO unbounded retry may vanish in
stuttering while retaining a constant runtime bound. Two admissible
shapes, per CAS site:

- (i) Static retry bound `k` [PROPOSAL]: proved from the contention
  structure (e.g. bounded competing threads on that location); the site
  contributes factor `k` to the O-time transfer below.
- (ii) Unbounded [OPEN]: the site is a DIVERGENCE source — x86 dynamic
  steps per GX step unbounded. The O-time transfer is then VOID for any
  program reaching it; this must be recorded per program (a refused
  cost-bound claim), never silently absorbed into "finite stutter".
  Single LOCK-prefixed fetch-RMW (`atomic_fetch_*`: one locked op, no
  loop) has constant cost and is the preferred lowering wherever the
  emitter uses it; the CAS-loop shape (release-on-success, acquire load —
  Sicht.lean header) is where O-cas-cost bites.

Obligation O-time [OPEN]: worst-case x86 dynamic-instruction count per G
rule, valid only where every CAS site on the program's paths has shape
(i) — plus an explicit statement that spinning/waiting time is unbounded
and excluded, matching `ZeitAb`'s existing weakness for waits (Spec
header: "`zeit` ... says nothing about waiting"). No cycle model is
claimed here; lane 278 owns any cycle-level statement.

### 4.12 Ordinary WB memory vs MMIO / DMA

The bridge covers cacheable write-back coherent memory only.
MMIO (UC/WC mappings), DMA buffers written by devices, and async device
writes (the shape beside `Orakel.wirkt`, Semantik.lean:1006) are OUTSIDE
TSO coherence: stores may never become visible in order, loads have side
effects, and device writes are not TSO stores. Obligation O-mmio:
`Tg` carriers are never mapped UC/WC; no `Tg` carrier aliases a DMA
buffer; device interaction stays in the foreign/oracle part of the model
(assumption (5) / `HardwareAnnahmen`), never in `Tg`. A `Tg` carrier
reachable from a device is a checker/lowering refusal (manifest-level,
no new diagnostic in wave A — record as a lowering precondition).

## 5. Bridge strategy and lemma dependency order

Chosen: **per-access forward simulation x86-TSO → W, then
`schwach_ist_gX` → GX, then the existing legs.** Rejected alternative:
block-level (G step → atomic x86 transaction, e.g. via a global lock or
HTM) — refuted by counterexample B (real interleavings unmapped) and
incompatible with `SperrWechselGX` (a global lock serialisation would
move lock effects away from their GX step boundaries and void the ticket
lock's own progress story). The simulation is forward (x86 trace → W
trace) because W is the weaker (more permissive) machine: every TSO
per-access option must be shown admissible in W, never the reverse.

Proposed definitions/lemmas in dependency order (wave-B work; names are
proposals, not reservations — no Lean file is added by this lane):

1. D-tso: x86-TSO state over the pilot (`X86/Typen.lean` `Zustand` +
   per-core store buffers + a flush relation + LOCK-exclusion), with a
   per-dynamic-event access record (address bytes, read/write, RMW flag).
2. D-access: access list of a G step — reads (carrier + value), writes
   (carrier + value), RMW target — extracted per `RufSchrittG` rule.
   L-access-complete (per rule, pattern `exchange_liest_schreibt`,
   RMW.lean:117): the list covers exactly `LiestG`/`SchreibG`.
   Depends on: `zugriffe`/`ereignisse` (RennfreiVoll.lean:499);
   O-access.
3. D-lower: lowering map per G rule: instruction sequence over the pilot
   `Befehl` set (extension proposals to lane 272 where the pilot lacks a
   form — notably LOCK-prefixed opcodes, fences, and wider/narrower
   accesses), with each memory micro-event labelled by its access-list
   index (O-access) or as silent (spill/private/lowering-internal).
4. L-read (O-tso-read): each labelled x86 load's TSO options ⊆ `Lesbar`
   options at its access (uses O-align for the bytes→value step and
   O-rely-values for the value domain).
5. L-write (O-tso-write, O-align): each labelled x86 store flushes to a
   `Frisch` timestamp; LOCK-prefixed RMW pairs satisfy the `rmw` field
   (`neu = wahl.ts + 1`; pattern `w_kein_verlust`, RMW.lean:191).
   Depends on: FIFO flush order + monotone views (`sicht_waechst`).
6. L-view: view updates (`lesesicht`/`locksicht`/`vorSicht`,
   MaschineW.lean:106/112/116) simulated: TSO program order + flush
   order imply the W view joins (release/acquire mapping §4.4; lock
   linearisation O-lock; spawn/join drains O-spawn).
7. L-step: a labelled x86 group (one G step's lowering, interleaved with
   other cores' groups at access granularity) assembles to a `SchrittW`
   (witnesses `σ`, `M''`, `wahl`, `neu`). Depends on: L-read, L-write,
   L-view, L-access-complete. Silent events must not touch `Tg` or
   recorded carriers (O-spill).
8. L-run: induction over x86 runs → W runs from `RufStartW M0`
   (start state: empty buffers, single-message histories — matches
   `RufStartW`, MaschineW.lean:77). Unbounded silent sequences are NOT
   excluded here (no leg needs it, §4.10); they are recorded per program
   for O-cas-cost/O-time (§4.11).
9. Instantiate `SchwachX` via `schwach_ist_gX` (AtomarW.lean:279) with
   `Tg := GeteiltV P ws` — needs O-checker-Tg (`hTA`), `FussSX` from (a),
   `KoerperGutSA` from (b) is NOT needed for `schwach` itself (only
   `GutO`/footprints/views) — check the actual premise list, not this
   sentence.
10. Legs: `rennfrei` via `RennfreiBisGA` (needs O-checker-race);
    `sperrWechsel`/`sperrSicht` via O-lock linearisation points;
    `zeit` via `ZeitAbX` + O-time transfer (valid only with O-cas-cost
    shape (i) everywhere on the program's paths); `fortschritt` via
    `FortschrittG` + O-enable (+ `fortschrittFX_aus`,
    BeweisAtomar.lean:117, for the thread machine) — enabledness only,
    no fairness; `keinKernHalt` via
    `KernHaltEA` + O-irq; `folge` free (`folgeG_erreichbarX`);
    contracts/invariants via `ziel_ort_atomar` once GX runs exist.
    Unrecorded-read legs route through OBS-5 (§4.9).

## 6. Impossibilities and model mismatches (named, not hidden)

1. No "x86 is W" and no "x86 is DRF-SC" blanket assumption — refuted by
   counterexample A. The bridge proves option-inclusion per access.
2. No G-step-as-transaction — refuted by counterexample B. Per-access
   interleaving is mandatory; the simulation relation must tolerate other
   cores' accesses between a step's own accesses (W does: reads are
   checked against the pre-step view independently).
3. W writes need not be FIFO; TSO writes are per-core FIFO. The inclusion
   goes TSO ⊆ W; any lemma requiring W to be FIFO is unprovable — do not
   write it.
4. `seq_cst` total order is modelled away (Sicht.lean:33). Sound today;
   becomes a gap the day a leg needs it.
5. Time is step counts, not cycles; x86 expansion needs O-time; spinning
   time is excluded exactly as `ZeitAb` already excludes waiting.
6. MMIO/DMA/device memory is outside the bridge (O-mmio); mapping a `Tg`
   carrier there voids every leg silently — hence a lowering
   precondition, not a proof.
7. No fairness assumption is invented or needed: `FortschrittG` is
   enabledness, not eventuality (§4.10). Livelock-freedom of spins/CAS
   beyond enabledness is NOT CLAIMED — consistent with the Spec header
   (starvation freedom out of scope). What IS claimed and open is the
   cost side: unbounded retries void constant runtime bounds (O-cas-cost,
   §4.11).
8. Unrecorded oracle/device reads route through OBS-5 (§4.9), not through
   a drain rule: local MFENCE is insufficient (other cores' buffered
   writes), and without discharge of (i)–(iv) the "last write" on x86
   (buffered elsewhere) and in G diverge, leaving `ungelesen`
   (MaschineW.lean:160) unmappable.
9. The goal statement is NOT pre-concluded unchanged: the bridge TARGETS
   the existing legs (`GabbroZiel`, Spec.lean:2283; `GabbroZielSC`,
   Spec.lean:2306 via `gabbro_ziel_sc_aus`, BeweisAtomar.lean:470; the
   landing zone is `SchwachX`), but whether the simulation proof goes
   through without a REVIEWED `Spec.lean` diff is OPEN — candidates are
   OBS-5 (assumption (5) scope), liveness scope (§4.10), and CAS cost
   (§4.11). This lane changes no statement; the proof decides.

## CUTS

What this document does NOT prove (design only, no Lean added):

- No TSO machine definition, no access-list extraction, no lowering map,
  no simulation lemma is proved here — §5 items 1–10 are wave-B work.
- No claim about which pilot `Befehl` forms the lowering needs beyond the
  noted proposals (LOCK-prefixed ops, fences, width extensions — owned by
  lanes 269/272, not decided here).
- No decoder/encoder, image/ABI, optimiser-legality or float/time-cycle
  facts (lanes 275/276/278).
- The per-rule access completeness (O-access, ~70 rules) is estimated as
  the largest single work item; `exchange_liest_schreibt` is the only
  existing instance of the pattern.
- O-drain (as a "fence everywhere" rule) and O-spawn (as a pure flush
  placement) are SUPERSEDED by OBS-5 (§4.9) and O-cas-cost (§4.11):
  flush placement without the publication/footprint/binding proofs does
  not discharge assumption (5), and unbounded retries must not vanish
  into stuttering. Where the runtime cannot place a needed flush or
  bound, the corresponding gap is recorded OPEN (possibly towards a
  reviewed statement diff), not papered over.
- All `#print axioms` obligations, witness obligations and review gates
  apply to wave-B Lean work, not to this document.
