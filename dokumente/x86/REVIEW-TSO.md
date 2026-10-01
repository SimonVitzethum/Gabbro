# Independent review: concurrency granularity and target bridge (lane 293)

*Lane 293, wave A, 2026-10-01. Docs-only audit. No Lean file, no model
change, no goal-statement change, no diagnostic/gift/example/CLI/MARKE
numbers. All definition claims below were checked against the tree on
branch `muse/293` (base `f4958150`); file:line references are part of the
claim. Audited documents: `dokumente/x86/TSO-GX-BRUECKE.md` (lane 274),
`dokumente/x86/IMAGE-ABI.md` (lane 276), `dokumente/x86/IR-VALIDIERUNG.md`
(lane 275). Canonical vocabularies: `Gabbro.Grammatik` (source model),
`Gabbro.Grammatik.X86` (pilot target, `grammatik/Grammatik/X86/Typen.lean`).
Wave contract: `dokumente/x86/WELLE-A.md`. Lean-first plan:
`dokumente/x86/LEAN-ZUERST.md`.*

## 0. Verdict up front

1. **The claimed reuse direction is correct as stated.** The bridge
   direction `x86 behaviours ⊆ W behaviours` (per-access forward
   simulation into W), followed by `schwach_ist_gX`
   (`grammatik/Grammatik/Speichermodell/AtomarW.lean:279`), lands in the
   existing `SchwachX` leg (`grammatik/Grammatik/Zielsatz/Spec.lean:2200`),
   whose conclusion is already `RufSchrittGX ... /\ σ agrees outside Tg`.
   Both theorems exist with the premises the bridge document claims (see
   §1). No premise is invented, no conclusion is weakened in prose.
2. **The granularity finding is confirmed against the real rules.**
   One G step is multi-access (see §2); a block-atomic mapping is
   incomplete, and incompleteness is unsoundness of the validation claim.
   The per-access strategy is mandatory, not optional.
3. **Line-number audit: all load-bearing references verified exact or
   off-by-one** (table in §1; the three off-by-ones are noted there and
   are immaterial). One stale-name risk: none found — every named
   theorem/definition cited exists.
4. **New findings of this review (beyond lane 274's own CUTS):**
   (a) the pilot `Befehl` set has NO locked RMW, NO fence, and NO
   sub-64-bit access form, so the bridge's `rmw`/O-align obligations
   currently have no target instruction to attach to (§3);
   (b) the IR document's layer-B/C evidence for shared-memory motion
   depends on whole-unit effect exports plus the per-access TSO table,
   and the SCFG/O-access work lists overlap without an owner for the
   access-list extraction itself (§5);
   (c) IMAGE-ABI's external-body obligation (c) and TSO OBS-5 (i)–(iv)
   are the same hole stated twice — the binding/kernel contract supply
   — and both documents correctly refuse to paper it over (§4);
   (d) the `FortschrittG`-vs-cost separation is stated consistently in
   all three documents, with one guardrail added here (§6).
5. **No unexplained hardware/OS fairness assumption is introduced by
   any of the three documents.** Where liveness would be needed
   (CAS-cost, spawn publication, handler visibility), each document
   records OPEN rather than assuming (§6).

## 1. Reference verification (checked, not trusted)

All paths relative to the repo root. "274:" = claim in TSO-GX-BRUECKE.md.

| # | 274 claim | Found | Status |
|---|---|---|---|
| 1 | `RufSchrittG` ~70 rules, one rule per thread step | `RufMaschineG.lean:263` `inductive RufSchrittG`; rules through `dannGleit` at :1957 and beyond | CONFIRMED (rule count not recounted; granularity argument needs only the cited rules) |
| 2 | `blatt` :265 / `dannBlatt` :354, whole leaf via `execStmt` in one step | :265 `\| blatt`, :354 `\| dannBlatt`, both with `hleaf : s.istBlatt = true` | EXACT |
| 3 | `dannExchange` :1933 reads `g` + `neuE.orte`, writes `g`, one step | :1933 `\| dannExchange` | EXACT (read/write shape per rule body; `exchange_liest_schreibt` at `RMW.lean:117` inverts it — EXACT) |
| 4 | `LiestG` :522 recorded-read-only; `ZugriffG` :513; `SchreibG` :517 | `RennfreiVoll.lean:513/517/522` | EXACT (522 is `(c, false) ∈ zugriffe ...`, read-event only) |
| 5 | `SchrittW` :150 fields `lies`/`ungelesen`/`frisch`/`rmw` | `MaschineW.lean:150` `structure SchrittW`, fields at :157/:160/:162/:191 | EXACT |
| 6 | `sicht_waechst` (views only grow) | `MaschineW.lean:269` | EXACT |
| 7 | `RufStartW` :77; `w_aus_g` :586 | :77 `def RufStartW`; :586 `theorem w_aus_g` | EXACT |
| 8 | `schwach_ist_gX` at `AtomarW.lean:279`; `praesentiert_gX` :94 | :279 `theorem schwach_ist_gX`, :94 `theorem praesentiert_gX` | EXACT |
| 9 | `RufSchrittGX` at `AtomarLauf.lean:33`; `gx_ga` :55 | :33 `def RufSchrittGX`; :55 `theorem gx_ga` | EXACT |
| 10 | `gx_leer_g` at `GXMaschine.lean:48` | :48–49 `theorem gx_leer_g` | EXACT |
| 11 | `sb_erlaubt` :446 / `sb_sc_verboten` :566, `LSchrittSC` | `Sicht.lean:446` `theorem sb_erlaubt`; :566 `theorem sb_sc_verboten`; :199 `inductive LSchrittSC` | EXACT |
| 12 | `seq` modelled as release/acquire, over-approximation, :33 | `Sicht.lean:33` + `Ordnung` doc at :57–59; joins differ per order at :114–129 (`entspannt` joins `eins`, `freigabe` joins full view) | EXACT — and the O-ord warning (prove parametric, not instantiated at `freigabe`) is justified by the join difference |
| 13 | `PrueferX` :2137, `AkzeptiertSpecX` :2109, `GeteiltV` :2104, `GeteiltA` :2100 | `Spec.lean:2137/2109/2104/2100` | EXACT |
| 14 | `RennfreiBisGA` :2125, `SperrWechselGX` :2157, `SperrSichtGX` :2165, `KernHaltEA` :2188, `SchwachX` :2200, `ZeitAbX` :2210 | all at the cited lines | EXACT |
| 15 | `GabbroZiel` :2283, `GabbroZielSC` :2306, `gabbro_ziel_sc_aus` at `BeweisAtomar.lean:470` | :2283/:2306; :470 `theorem gabbro_ziel_sc_aus` | EXACT |
| 16 | `FussSX` at `AtomarReplay.lean:29` | :29 `def FussSX` | EXACT |
| 17 | `HavocA` at `AtomarSem.lean:49`; `KoerperGutSA` at `AtomarRec.lean:39`; `koerperGutSA_mono` narrowing `GeteiltV ⊆ GeteiltA` used in `zielX_aus` | :49 `def HavocA`; :39 `def KoerperGutSA`; :91 `theorem koerperGutSA_mono` | EXACT |
| 18 | `FortschrittG` verbatim (finished/waiting/named-stops-or-can-step) | `Spec.lean:1828–1831` matches the document's reading exactly | EXACT |
| 19 | `FadenSchrittX.start/kind/join` at `GXMaschine.lean:92/100/105`; `FadenInvX` :181; `segZaehleX` :288 | `FadenSchrittX` inductive at :87; `FadenInvX` at :181; `segZaehleX` at :287 | OFF-BY-ONE on two (87 vs 92; 287 vs 288) — immaterial, constructors `start/kind/join` confirmed |
| 20 | `lesesicht`/`locksicht`/`vorSicht` at `MaschineW.lean:106/112/116` | :107/:112/:116 | OFF-BY-ONE on one — immaterial |
| 21 | Orakel fields at `Semantik.lean:454` (`wirkt`, `regLies`, `sichtbar`) | :455/:457/:462 | OFF-BY-ONE — immaterial |
| 22 | `einpassen` at `Semantik.lean:425` | :426 `def einpassen` | OFF-BY-ONE — immaterial |
| 23 | `RegLokal` at `ZielOrtGeraetSem.lean:48`; `RahmenO` at `ZielOrtVollBeweis.lean:48`; `GutO` at `Satz.lean:967` | :48/:48/:967 | EXACT |
| 24 | `genommen_von`/`gegeben_von` at `DRF.lean:186/197` | :186/:197 | EXACT |
| 25 | `w_kein_verlust` at `RMW.lean:191` | :191 | EXACT |
| 26 | `fortschrittFX_aus` at `BeweisAtomar.lean:117`; `folgeG_erreichbarX` :149; `ziel_ort_atomar` at `AtomarLauf.lean:404` | :117/:149/:404 | EXACT |
| 27 | `treiber-gen-10`; template register (`tor.trampolin`, `tor.kind`, `faden.laufzeit`, `faden.modul`, `arena.dyn`, `sperre.ticket`, `tor.region`, `tor.fehlbar`, `tor.nie`, `start.nolibc`) | `treiber.rs:103` `GENERATOR_KENNUNG = "treiber-gen-10"`; `SchablonenArena/Faden/Modul/OhneLibc.lean` carry the named rows | CONFIRMED |
| 28 | Assumption (5) in the Spec header (unrecorded reads see last write, ASSUMED) | `Spec.lean:1171–1177`; `MaschineW.lean` header restates it as "a NAMED ASSUMPTION of the reading (assumption (5))" | EXACT — both ends agree it is assumed, not derived |
| 29 | No `SCFG.lean` exists (IR doc is architecture prose) | `grammatik/Grammatik/X86/` holds only `Speicher/Typen/Wort.lean`; no `*SCFG*` anywhere | CONFIRMED — §5 consequences below |
| 30 | `SchwachX` quantifies over ALL `ord` | `Spec.lean:2200–2206`: `∀ (ord : D.Glob → Ordnung) ...` | EXACT — O-ord is a real obligation |

No invented theorem, no moved line, no silent redefinition found in any
of the three documents.

## 2. Granularity: what the real rules force

### 2.1 One G step, several accesses — confirmed

`blatt`/`dannBlatt` run a whole leaf through `execStmt` in one
`RufSchrittG` step; nothing bounds a leaf to one read or one write
(a float leaf reads `a.orte ++ b.orte`, cf. `dannGleit` at
`RufMaschineG.lean:1957`). `dannExchange` reads the global AND every
carrier of the update expression, then writes the global — one step.
`W`'s own header (`MaschineW.lean`, "GRANULARITY") agrees: "A step of W
is one coarse step of G: nothing interleaves inside it." The bridge
document's decomposition requirement (D-access/O-access) therefore
follows from the rules, not from caution.

### 2.2 Trace B (interleaved lowering of one exchange) — endorsed

Source: `let x = g exchange update(h)` with `h` a second admitted
shared atomic. G: one `dannExchange` step (reads `g`, reads `h`,
writes `g`). Lowering (at least: load `h`, locked RMW on `g`):

```
T0: load h -> 0            (x86 dynamic event, TSO: own-buffer-or-memory)
T1: store h := 1; flush    (other core; TSO FIFO per core)
T0: LOCK RMW g (computed from h = 0); flush
```

W admits it: the two reads are checked independently against the
pre-step view (`lies` per carrier; `lesesicht` folds each `beitrag`).
A block-atomic mapping has no image for the interleaving. The review
adds one precision: the same hole bites ANY multi-access leaf, not
only `exchange` — e.g. a leaf writing two globals `g1, g2` while
another core writes `g2` between the two lowered stores. O-access must
therefore cover all ~70 rules, exactly as stated; `exchange` is only
the first instance of the pattern (`exchange_liest_schreibt`).

### 2.3 Trace A (store buffering) — endorsed, with the exact edge

`sb_erlaubt` (:446) vs `sb_sc_verboten` (:566): `r0 = 0` on both sides
is reachable in W, unreachable in SC. x86-TSO admits it. Any
"x86 is SC/DRF-SC" premise is refuted by this four-step trace:

```
T0: store x := 1 (buffered)    T1: store y := 1 (buffered)
T0: load y -> 0 (own buffer has no y; memory still 0)
T1: load x -> 0 (symmetric)
```

The bridge targets W, never G, for the memory part. Correct.
Sharp edge confirmed: `seq`-as-release/acquire (`Sicht.lean:33`) keeps
SB even where RC11 forbids it for `seq` — sound today (x86 shows
fewer behaviours than W admits), a gap the day a `seq` total-order
leg is added. All three documents state this; none claims the order.

### 2.4 Micro-access vs coarse-G grouping holes — the review's own list

Beyond counterexample B, the grouping proof (L-step) must survive:

1. **Spill/reload insertion inside a step's lowering.** Register
   allocation (IR §3.5) threads spills through the memory token as
   ordinary frame accesses. At x86 level these are extra dynamic
   events between the step's labelled accesses. Harmless ONLY IF the
   spill slots are proved disjoint from every `Tg` carrier and every
   recorded carrier (O-spill) — otherwise the extra events are
   unmapped accesses, and L-step fails closed (refusal, not silence).
2. **Multi-instruction lowering of one source store.** A source-width
   store wider than one `MOV` (or any future width the pilot does not
   yet have) lowers to several x86 stores; another core's load can land
   between them. Until O-align proves single-event coverage, such a
   lowering is refused — there is no partial-credit grouping.
3. **Collapsed accesses.** If the backend merges two source loads of
   one carrier into one x86 load (or CSE does at SCFG level, IR §3.3),
   the access list has two entries and the machine one event. The
   mapping needs the load-identity lemma PLUS the interleaving
   condition (ownership/lock/immutability) — single-threaded
   token-order evidence alone is insufficient, exactly as IR §3.3
   states. The two documents agree here; the proof is wave-B work.

## 3. Byte-width / tearing / RMW-order hazards (lane-293 charge)

### 3.1 The pilot has no target form for any of them — finding (a)

`Befehl` (`X86/Typen.lean:53–72`) is: `movImm64`, `movReg64`,
`add/sub/xor/cmpReg64`, `load64`, `store64`, `jump32`, `jumpIf32`,
`call32`, `push64`, `pop64`, `ret`. Consequences, each checked:

- NO locked/prefixed RMW: the bridge's L-write `rmw` mapping
  (`neu = wahl.ts + 1`, `w_kein_verlust`) has no pilot instruction to
  attach to. Lane 272 owns the extension (per WELLE-A table); until it
  lands, every `exchange` lowering is unmapped — refusal, not
  assumption.
- NO fence (`MFENCE`/locked-op barrier claim): O-irq/O-spawn drains
  and any release/acquire mapping stronger than plain MOV have no
  pilot form. On TSO plain aligned MOV already orders release/acquire,
  so the memory fragment does not need fences — but the drain
  obligations (§4) cannot even be STATED over the pilot yet.
- NO sub-64-bit access: every load/store is 64-bit. A source carrier
  narrower than 8 bytes (e.g. `u8` flag, the `sb` litmus shape, the
  byte readers of the network stack) has no exact-width pilot access.
  A 64-bit access covering a 1-byte carrier reads/writes neighbour
  bytes — that IS cross-carrier overlap (counterexample C shape).
  O-align cannot be discharged for narrow carriers until the pilot
  gains widths or a proved masking discipline. This is currently the
  sharpest byte-width hazard: most real shared atomics/flags are
  narrow.
- `Speicher` is per-BYTE (`bytes : Adresse → Byte` + three permission
  fields, `Typen.lean:41–45`) while `Speicher D` is per-CARRIER
  (`D.Tab ⊕ D.Glob` is one location per W message). The
  access-to-bytes mapping (O-align) must therefore prove, per shared
  access: natural alignment, full containment in one carrier extent,
  non-overlap with any other live carrier, and little-endian
  value-encoding agreement. None of this exists yet; lane 271 owns the
  memory relation.

### 3.2 Tearing trace (two threads, one misaligned 8-byte store)

```
Carrier layout: adjacent 4-byte carriers A (bytes 0..4), B (bytes 4..8).
T0: 8-byte store 0x1122334455667788 at byte 2 (spans A[2..4], B[0..4])
T1: load A -> 0x55660000?? (old A[0..2] ++ new A[2..4], or any split)
T2: load B -> 0x??11223344 (any other split)
```

No single W message (`histS`: ONE message carrying the whole
post-step carrier value) corresponds to T0's event: T1 and T2 observe
different halves. The bridge document's O-align refusal (unaligned or
cross-carrier shared accesses are refused by the lowering) is the only
sound response; there is no "torn message" in W to map to. Endorsed.

### 3.3 RMW order hazard

W's `rmw` field pins `neu (.inr g) = (wahl (.inr g)).ts + 1` — the
exchange writes DIRECTLY above the message it read. An x86 CAS loop
with a stale-load retry, or two overlapping LOCK RMWs where the loser
retries from an older value, must map the SUCCESSFUL attempt to the
access and treat failures as stutter. If a lowering ever committed two
writes for one source exchange (e.g. separate load then store without
LOCK), `w_kein_verlust` would be unprovable — correctly, since that
lowering is broken. The failure-as-stutter treatment is sound for the
safety legs but interacts with cost (§6).

## 4. Fences, spawn/join, interrupts, foreign/device footprints

### 4.1 Local fence limitations — endorsed and sharpened

A local drain (own buffer flushed) makes the acting core's writes
visible; it does NOT make other cores' last writes visible to an
unrecorded reader. The bridge document's OBS-5 states this exactly,
and the review confirms the mechanism: `Lesbar` is per-reader-view,
and no core can flush another core's buffer. "MFENCE everywhere" does
not discharge assumption (5). Correct — and correctly marked OPEN
rather than assumed.

### 4.2 Spawn/join and interrupt entries

`FadenSchrittX.start/kind/join` move no G memory except through the
acting thread's state (`GXMaschine.lean:87ff`); the hardware side
(clone syscall boundary as full barrier, store-buffer drain before the
child observes, view join mirroring `vorSicht`'s lock join) is a
lowering constraint, now correctly marked OPEN pending the
publication lemma (bridge §4.7 defers to §4.9 (iii) — consistent).
For interrupts: mapping masking to `D.maskiert`, draining at handler
entry, keeping `KernPlan` run-to-completion a NAMED hardware
assumption (x86 does not guarantee it: NMI/higher-priority
preemption), and treating handler `Tg` accesses as ordinary GX steps
— all four O-irq items are necessary; none invents fairness.

### 4.3 Foreign/device footprints — OBS-5 (i) verified at the definitions

Checked: `RahmenO` (`ZielOrtVollBeweis.lean:48`) constrains only what
an axiom WRITES (declared frames); `GutO` (`Satz.lean:967–983`)
constrains writes (`Rahmen`), held locks, and the trace shape — NOT
which carriers foreign code READS. `RegLokal`
(`ZielOrtGeraetSem.lean:48`) bounds `regLies`/`sichtbar` readers, but
`Orakel.wirkt`'s read footprint is indeed unbounded by the generic
model. The per-binding obligation O-foreign-foot (prove, per
`extern`/syscall gate, which carriers its result can depend on) is
therefore real and correctly placed on bindings, not on the model.

### 4.4 IMAGE-ABI obligation (c) is the same hole — finding (c)

IMAGE-ABI §11 requires, per gate/foreign-call site leaving the
validated domain: (a) checked declaration, (b) proved caller-stub
correspondence, (c) a SUPPLIED Lean-proved callee-side contract at the
actual call. With (c) unmet, the image is refused. The historical
`os_bindung_*` premises (§12) are gap records that "qualify no image
for acceptance" — consistent with AGENTS.md §3 (OS is user logic).
This is OBS-5 (iv) restated at image level. Both documents refuse
rather than assume; the review endorses the alignment and notes the
consequence: until binding contracts are supplied AND proved, every
image exercising those gates stays refused by final validation. That
includes thread start/join, arena reserve/commit, page return, and
report/exit paths — i.e. every real hosted image. The refusal is the
correct posture; its blast radius should stay visible in planning.

## 5. IR-VALIDIERUNG: what it proves, what it needs, where it overlaps

### 5.1 Architecture endorsed

One SCFG, memory-token threading, validator-recomputed (never trusted)
dataflow facts, per-rule generic lemmas over arbitrary values, ghost
call/return events for inlining (contracts hold at their place with
actual values), conditional SIMD refusal until a vector correspondence
is PROVED, three separated cost levels with the ghost source-budget
correspondence OPEN. The §2.4 soundness statement binds BOTH ends to
the full source unit `E` (`lowerOk(E, G0)`, per-step `check_C`,
`layoutOk(Gn, B, Img)`) — no free initial graph, no duty-only binding,
no assumed refinement. This closes the exact loopholes the HARD RULES
exist to catch.

### 5.2 Overlap without an owner — finding (b)

Two wave-B work lists both require "the access list of a G step":

- Bridge D-access/L-access-complete: per-`RufSchrittG`-rule access
  extraction (reads+values, writes+values, RMW flag), pattern
  `exchange_liest_schreibt`, obligation O-access (~70 rules).
- IR `LowerMap`/layer-C: source-node → SCFG-op anchors for
  memory/call/check/atomic/lock/stop, proved to preserve
  `execStmt`/`exec` (lane 277's QUELLBRUECKE).

These are adjacent but not identical (rule-indexed access lists vs
lowering anchors), and neither document owns the extraction. The
existing decision procedure both can build on is
`zugriffe`/`ereignisse` (`RennfreiVoll.lean:499–502`) with
`OrteInvG`/`schritt_ev` (every read event is a footprint carrier).
Recommendation: assign ONE owner for a proved `accessList(rule)`
function with the completeness lemma stated once; both consumers cite
it. Until then, two lanes may prove the same inversion twice or
diverge on what an access is.

### 5.3 Shared-memory motion conditions agree

IR §3.3 requires, for every load elimination/motion, ownership OR
held-lock stability (whole-unit effect exports) OR immutability —
validator-decided — and declares atomics/MMIO/volatile/foreign
ineligible without an exact per-access concurrent equivalence
theorem. This is precisely the bridge's per-access interleaving
semantics consumed at SCFG level. The dependency (IR items 3/5/9 on
lane 274's TSO table) is stated in both directions consistently.
No disagreement found; the ordering constraint (TSO table before
motion lemmas) should be enforced in scheduling.

## 6. Enabledness vs work/time — consistent, one guardrail

`FortschrittG` is per-state enabledness (verified verbatim, §1 row
18): spins/CAS-retries/lowering expansion never threaten it, and all
three documents state this. What remains is enabledness preservation
(O-enable: no fault the source has none) plus, separately, cost:

- O-cas-cost: a CAS-loop lowering is unbounded in retries while the
  source exchange is ONE G step. Shape (i) static bound (proved from
  contention structure) or shape (ii) divergence recorded per program
  (cost-bound claim refused). "No unbounded retry vanishes in
  stuttering while retaining a constant bound" — endorsed; the
  single-`LOCK`-op lowering (`atomic_fetch_*`) is correctly identified
  as the constant-cost shape, once the pilot HAS a LOCK op (§3.1).
- O-time transfers per-G-rule x86 counts only where every CAS site on
  the program's paths has shape (i); spinning/waiting excluded exactly
  as `ZeitAb` already excludes waiting. Consistent with the Spec
  header.
- Guardrail added by this review: the IR's block-stuttering ranking
  argument (§4.3: every inserted sequence straight-line and finite,
  no new back edge) must ALSO cover CAS-retry loops introduced by
  lowering — a retry loop IS a new back edge at machine level. Either
  the loop carries a shape-(i) bound (then it is bounded stutter) or
  the certificate's progress argument does not close. Do not let
  "straight-line" describe a sequence containing a retry back edge.

No fairness assumption (scheduler, buffer-drain eventuality, spin
termination) appears in any document's claims. Liveness beyond
enabledness is NOT CLAIMED anywhere — consistent with the Spec header
(starvation freedom out of scope).

## 7. Unsupported target forms (precise)

Over the CURRENT pilot (`Befehl` as listed in §3.1), the following
have no mapping and are refused until their lane closes:

1. Any `exchange`/RMW lowering (no LOCK op) — lane 272.
2. Any sub-64-bit shared access (no narrow forms) — lane 272 (+271
   masking discipline if chosen instead).
3. Any fence/drain sequence (no fence form) — lane 272.
4. Any indirect-control validation beyond `call32`/`ret` with tracked
   callers (jump-table/data-flow certificates are IR/IMAGE-ABI
   prose; decoder + semantics are lanes 272/279).
5. MMIO/UC/WC/DMA/device memory (O-mmio): outside TSO coherence,
   never in `Tg`, device interaction stays foreign under
   assumption (5) — all three documents agree.
6. FP beyond scalar SSE/SSE2 with identical rounding/traps/NaN
   behaviour (lane 278 owns the mapping); kernel-module and
   interrupt paths touching SSE state where forbidden are refused.
7. `seq_cst` total order: modelled away (`Sicht.lean:33`); sound
   today, a gap the day a leg needs it.
8. Unbounded regions without ceiling: opt-in, loses the static bound
   by design, every allocation failure handled (standing instruction).
9. Link-time/cross-unit optimisation: needs `GabbroZielVerbund`
   premises (IR §7.8 states this; no claim beyond single-unit).

## 8. Generic proof dependencies (what wave B must close, in order)

1. D-tso: x86-TSO state over the pilot (buffers, flush, LOCK
   exclusion) with per-event access records — needs 272 (execution
   semantics) + 279 (decode) + 271 (memory relation).
2. `accessList(rule)` + completeness per `RufSchrittG` rule (O-access;
   proposed single owner, §5.2) over `zugriffe`/`ereignisse`.
3. Lowering map per G rule with access-index labels (needs 272's
   LOCK/fence/width extensions, §3.1).
4. L-read/L-write/L-view/L-step/L-run (needs O-align bytes→value
   lemma, O-rely-values byte concatenation, FIFO+`sicht_waechst`).
5. Instantiate `SchwachX` via `schwach_ist_gX` with
   `Tg := GeteiltV P ws` (+ `hTA` from the lowering contract,
   `FussSX` from (a); `KoerperGutSA` NOT needed for `schwach`
   itself — premises verified at `AtomarW.lean:279–290`).
6. Legs via O-checker-race / O-lock linearisation / O-time (+O-cas-cost
   shape (i)) / O-enable / O-irq / OBS-5 (i)–(iv).
7. SCFG syntax/semantics refining to `P`/`GX` (not standalone), rule
   register, `check_C`/`lowerOk`/`layoutOk`, generic soundness
   (§2.4), spill-freshness lemma against the TSO relation, vector
   correspondence (a)–(d), ghost budget correspondence.
8. Binding/kernel contracts per §11(c)/OBS-5(iv) — the supply chain
   that unblocks every real image (§4.4).

Whether steps 5–8 go through without a REVIEWED `Spec.lean` diff is
OPEN (candidates: assumption-(5) scope, liveness scope, CAS cost) —
the bridge document states this correctly in §6.9, and this review
concurs: no pre-conclusion either way.

## CUTS

This review proves nothing in Lean: no TSO machine, no access-list
function, no lowering map, no simulation lemma, no SCFG definition, no
decoder, no cost transfer. It is source inspection of the cited files
against the three audited documents, with verdicts, two-thread traces,
and precisely stated holes. Reference table in §1 is the evidence;
§§3.1/4.4/5.2/6 are the new findings. `#print axioms` obligations apply
to wave-B Lean work, not to this document.
