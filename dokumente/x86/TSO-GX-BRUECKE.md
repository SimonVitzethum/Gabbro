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
  TRANSFER on top: obligation O-time (§4.10): a per-G-rule worst-case x86
  instruction bound (including CAS-retry bounds), composed with `ZeitAbX`.
  Lane 278 owns timing; this document states the interface.
- `fortschritt : FortschrittG` (Spec.lean:1828): G steps or named stops
  (finished, waiting, flag, budget, hardware, `nieZurueck`). x86 spins
  (ticket `dreht`, CAS retries, lowering loops) are finite stutter —
  obligation O-stutter (§4.9): no infinite silent x86 trace without a G
  step; needs a hardware fairness assumption (every flushed store becomes
  visible; ticket draws are served in order — bounded waiting comes from
  the ticket discipline, already proved: `ticket_ausschluss`,
  CTicket.lean header).
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
every x86 store eventually flushes; at flush time its timestamp is
`Frisch` (strictly above the acting thread's pre-step view — holds because
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
silent x86 steps (stutter, §4.9); the successful attempt is THE RMW access
of the access list; the update computation's input reads are ordinary
accesses of the same G step (counterexample B shape — explicitly allowed).
Obligation O-cas: each CAS loop either carries a static retry bound (then
it feeds O-time) or relies on the fairness assumption (then it feeds
O-stutter only, not O-time).

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
would be stale beyond any `Lesbar` option — the one place where TSO
flushing MUST be constrained, not merely admitted.

### 4.8 Interrupts

O-irq: (i) map the lowered interrupt masking to `D.maskiert` and the
  handler roots to `P.unterbricht` (`HandlerVon`, Spec.lean:1871);
(ii) drain the interrupted thread's store buffer at handler entry (a
handler is a new x86 observer; undrained stores would let it read older
values than its W view permits); (iii) keep `KernPlan`
run-to-completion as a NAMED hardware assumption — x86 does not guarantee
it (higher-priority interrupts, NMIs, faults inside the handler);
(iv) handler accesses to `Tg` carriers are recorded accesses of a GX step
of the handler thread (they are ordinary steps, `FadenSchrittX.lauf`),
while handler interaction with devices is foreign (assumption (5)).

### 4.9 Unrecorded oracle accesses — the drain rule

Assumption (5) (Spec header): `Orakel.wirkt`, `axiomAntwort`, `O.regLies`,
`O.sichtbar` read G's memory — the LAST write — wherever the step records
nothing. On x86 these are: foreign calls (`extern`/syscall gates),
device-register reads, and the `awaits` visibility check. Obligation
O-drain: before every foreign call, every device read, and every point
where `O.sichtbar` is evaluated, the acting core's store buffer is
drained (MFENCE or equivalent), so "last write" coincides on both sides.
If a foreign callee runs concurrently on another core (DMA-style), it is
NOT covered — see §4.11. This is the second place (with O-spawn) where
the bridge constrains flushing instead of admitting it.

### 4.10 Finite / infinite stuttering and progress

Silent x86 steps (no G-step counterpart): lowering expansion
(one G rule → several instructions), ticket `dreht` spins, CAS-loop
failures, spill traffic. Finite stutter is harmless for safety legs
(`schwach` sees only access events; `rennfrei`/`sperrSicht` read access
records). For `fortschritt` (Spec.lean:1828: every thread finished,
waiting, named-stopped, or able to step) infinite silent traces must be
excluded — obligation O-stutter: (i) every lowering-expansion sequence
terminates (static bound — shared with O-time); (ii) ticket spins
terminate by the ticket discipline + hardware fairness (bounded bypass:
`ticket_ausschluss` gives exclusion; starvation-freedom is NOT proved —
name the fairness assumption: every core makes progress and every flushed
store becomes visible); (iii) CAS loops terminate under the same fairness
or a static bound (O-cas). The named stops (`flagge`, `budget`,
`hardware`, `nieZurueck`) need x86 counterparts: budget exhaustion is a
G-level counter (unaffected); `hardware` stops (faults: #GP/#PF/divide
errors) must be classified per emitted form — lane 272's witnesses plus
lane 276's image contract feed this; a fault the binary takes where G
has none is a gap, not a refinement.

### 4.11 Time

`ZeitAbX` bounds per-thread GX-step counts (`segZaehleX`) by
`kostenTief`, independent of memory answers
(`frame_schritte_beschraenktX`). The x86 transfer is multiplicative:
obligation O-time: worst-case x86 dynamic-instruction count per G rule
(including the CAS-retry bound from O-cas and spin bounds — or an
explicit statement that spinning time is unbounded and excluded, matching
`ZeitAb`'s existing weakness for waits: Spec header "`zeit` ... says
nothing about waiting"). No cycle model is claimed here; lane 278 owns
any cycle-level statement.

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
   `RufStartW`, MaschineW.lean:77). Infinite-silent-trace exclusion
   (O-stutter) for the progress-relevant reading.
9. Instantiate `SchwachX` via `schwach_ist_gX` (AtomarW.lean:279) with
   `Tg := GeteiltV P ws` — needs O-checker-Tg (`hTA`), `FussSX` from (a),
   `KoerperGutSA` from (b) is NOT needed for `schwach` itself (only
   `GutO`/footprints/views) — check the actual premise list, not this
   sentence.
10. Legs: `rennfrei` via `RennfreiBisGA` (needs O-checker-race);
    `sperrWechsel`/`sperrSicht` via O-lock linearisation points;
    `zeit` via `ZeitAbX` + O-time transfer; `fortschritt` via
    `FortschrittG` + O-stutter (+ `fortschrittFX_aus`,
    BeweisAtomar.lean:117, for the thread machine); `keinKernHalt` via
    `KernHaltEA` + O-irq; `folge` free (`folgeG_erreichbarX`);
    contracts/invariants via `ziel_ort_atomar` once GX runs exist.

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
7. Infinite stutter (livelock by CAS/spin non-termination) needs a
   hardware fairness assumption; it cannot be proved from TSO alone.
   Starvation freedom stays NOT CLAIMED (Spec header), consistent with
   this.
8. Unrecorded oracle/device reads need the drain rule (O-drain,
   assumption (5)); without it the "last write" on x86 (buffered) and in
   G diverge and `ungelesen` (MaschineW.lean:160) is unmappable.
9. The goal statement is unchanged: `GabbroZiel` (Spec.lean:2283) and
   `GabbroZielSC` (Spec.lean:2306, via `gabbro_ziel_sc_aus`,
   BeweisAtomar.lean:470) stand as is; the bridge lands in `SchwachX`.

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
- O-drain and O-spawn constrain the runtime/lowering (flush placement);
  if the runtime cannot place them, the corresponding legs keep assumption
  (5)/view-join as explicit named assumptions instead — the bridge then
  documents, not discharges, them.
- All `#print axioms` obligations, witness obligations and review gates
  apply to wave-B Lean work, not to this document.

