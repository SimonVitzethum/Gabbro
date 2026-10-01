# Adversarial implementation audit: WEAK-MEMORY

*Lane 408, 2026-10-01. Docs-only audit: no Lean file, no model change, no
goal-statement change, no diagnostic/gift/example/CLI/MARKE numbers.
Base: branch `muse/408` at `0b3132b7`. All file:line references were read
at this HEAD and are part of the claim. Audited implementations:
`grammatik/Grammatik/X86/TSO.lean`, `Zugriffe.lean`, `AccessList.lean`,
`LockedOps.lean`, `OverlapRefusal.lean`, `SpillPrivate.lean`, against the
bridge design `TSO-GX-BRUECKE.md`, its review `REVIEW-TSO.md`, the wave plan
`WORK-ALLOCATION.md`, and the source legs (`MaschineW.lean`, `AtomarW.lean`).
In-flight but UNMERGED at this HEAD: lane 344 (FenceDrain) and lane 350
(AtomicPayload) are committed candidates pending review; lane 421
(WordAtomicity) is scheduled. This audit covers only what is in the tree;
it does not pre-judge those lanes.*

## 0. Verdict up front

1. **Every merged weak-memory module is correct within its stated claim.**
   No false theorem, no vacuous witness, no over-claim found. Each file's
   CUTS accurately describes what it does not prove. Where the bridge needs
   more, the files say OPEN rather than assuming.
2. **No DRF-SC claim and no word-atomicity-from-bytes claim exist.**
   `tso_store_buffering` (TSO.lean:414) exhibits the non-SC outcome;
   `einzelbyte_atomar` (TSO.lean:445) is width-1 only; `paket_reisst`
   (TSO.lean:459) proves a two-byte packet tears. The task's two
   must-nots are satisfied by inspection, not by trust.
3. **Eleven findings, all consumer gaps, none a bug in a proved claim.**
   Ranked F1–F11 below. The sharpest: there is NO combined TSO+LOCK step
   relation in the tree (F1); LOCK/RMW/fence are barrier-as-precondition,
   not barrier-as-effect (F2, reproduced by probe); the target footprint
   extraction does not cover the locked forms (F3); and `GetrenntK` names
   two different relations (F5), which can misroute an O-spill discharge.
4. **Three modules the bridge needs are still absent at this HEAD:**
   narrow accesses (A1, NarrowOps), the source-carrier-to-region map (C1,
   TableLayout), and the fence-drain producer (B4, FenceDrain — candidate
   pending, not merged). Narrow shared carriers remain unlowerable (F8).

## 1. What each module proves (checked, not trusted)

### 1.1 TSO.lean — byte-granularity TSO, honestly bounded

- State `TSOZustand` (TSO.lean:29): canonical `Speicher` plus per-core
  FIFO byte buffers (`TSOEintrag`, TSO.lean:22). Steps `TSOSchritt`
  (TSO.lean:92) are issue and oldest-entry flush ONLY; loads and fences
  gate without changing state. Reachability `TSOErreichbar` (TSO.lean:99)
  is target-only.
- Forwarding (`load_nach_issue`, TSO.lean:245), FIFO order
  (`fifo_reihenfolge`, TSO.lean:294), permission preservation, and the
  reached memory-changing SB witness (`tso_store_buffering`, TSO.lean:414;
  `sb_beide_laden_null`, TSO.lean:395; `sb_flush_aendert_speicher`,
  TSO.lean:406) are proved over real canonical bytes.
- Fence locality is proved as a LIMITATION: `zaunBereit_iff_leer`
  (TSO.lean:313) plus `zaun_kein_fremd_drain` (TSO.lean:350) — core 0
  fence-ready while core 1 holds a pending store. This is the OBS-5
  boundary as a theorem, not prose.
- `LockSchritt` (TSO.lean:477) is an EMPTY inductive with
  `kein_lock_schritt` (TSO.lean:480): no LOCK transition at this layer.
  Correct as stated; the locked forms live in LockedOps.lean instead.

### 1.2 Zugriffe.lean — single-owner potential footprint, all 14 forms

- `zugriff` (Zugriffe.lean:42) extracts read/write footprints plus the
  stored word from the canonical `Befehl` and the pre-state, for all 14
  pilot constructors (theorems Zugriffe.lean:64–163).
- Success linkage is proved both ways: pure/read forms mutate no memory
  (Zugriffe.lean:176–291), write forms change bytes only inside the
  extracted footprint with permissions preserved
  (`erfolg_store64_im_fuss`, Zugriffe.lean:361; push/call analogues),
  and refusals (bad length, failed permission) admit no step
  (Zugriffe.lean:467–526).
- Non-claims are empty types, not comments: `kein_atomarer_zugriff`
  (Zugriffe.lean:540), `keine_ablauf_spur` (Zugriffe.lean:548). The eight
  `Fuss` addresses are a byte set, not one atomic event — stated and
  proved. Reached store-changing witness `zugriff_lauf_zeuge`
  (Zugriffe.lean:591).

### 1.3 AccessList.lean — single-owner G-step access list (review §5.2 fix)

- `accessList` (AccessList.lean:64) extracts reads (pre-value), writes
  (post-value) and the RMW flag from the decided `zugriffe` delta plus
  endpoint memories. Completeness is stated once
  (`eintraege_liest`, AccessList.lean:83;
  `eintraege_schreibt_aufgezeichnet`, AccessList.lean:96;
  `schreibG_voll`, AccessList.lean:112; `zugriffG_voll`,
  AccessList.lean:121). `IstRMW` (AccessList.lean:71) is `ExchangeKopf`
  — no silent RMW is manufactured.
- `exchange_rmw_voll` (AccessList.lean:170) reuses
  `exchange_liest_schreibt` instead of duplicating the inversion.
  Concrete reached memory-changing witness `accessList_ta_zeuge`
  (AccessList.lean:206) on the `taP` run.

### 1.4 LockedOps.lean — LOCK RMW + fence as new target forms

- `SperrBefehl` (LockedOps.lean:23): XADD-shape RMW and MFENCE beside,
  not inside, the 14 pilot forms. `lockSchritt` (LockedOps.lean:58) and
  `casSchritt` (LockedOps.lean:84) operate directly on canonical memory
  with per-event records (`LockEreignis`, LockedOps.lean:31).
- Atomicity of one locked add (`lock_xadd_atomar`, LockedOps.lean:145),
  fence locality (`mfence_ordnung`, LockedOps.lean:175), CAS
  success/failure equations, failure-as-stutter
  (`cas_fehlschlag_stottert`, LockedOps.lean:253), proved retry
  unboundedness (`cas_schleife_unbeschraenkt`, LockedOps.lean:272), and
  the split-pair refusal (`rmw_nur_mit_lock`, LockedOps.lean:282) with a
  witness built from REAL `zugriff` footprints
  (`rmw_nur_mit_lock_zeuge`, LockedOps.lean:442).
- Non-claims are empty types: `kein_lock_nach_w` (LockedOps.lean:458),
  `keine_lock_zyklus_schranke` (LockedOps.lean:467).

### 1.5 OverlapRefusal.lean — decided O-align half, target-side

- Decided checker `zugriffOk` (OverlapRefusal.lean:44) and conservative
  policy `aliasZulassen` (OverlapRefusal.lean:95, unknown => refuse),
  with proved soundness `fussDisjunktB_klingt` (OverlapRefusal.lean:119)
  and the sequential bytes-value agreement `einzelTraeger_wertUeberein`
  (OverlapRefusal.lean:143).
- Counterexample-C shape as a decided negative probe
  (`gegenbeispielC_unbekannt`, OverlapRefusal.lean:281;
  `gegenbeispielC_verweigert`, OverlapRefusal.lean:287) plus a joint
  checker witness on one adjacent-carrier image (`zugriffOk_zeuge`,
  OverlapRefusal.lean:346).

### 1.6 SpillPrivate.lean — TSO-side spill producer half

- Freshness => disjointness => commutation over canonical vocabulary
  (`spill_fill_kommutiert`, SpillPrivate.lean:156;
  `spill_frisch_bleibt_bei_fremd_issue`, SpillPrivate.lean:225;
  `spill_bleibt_bei_fremd_flush`, SpillPrivate.lean:251) with a reached
  TSO witness where the foreign byte observably changes and spill bytes
  do not (`spill_tso_zeuge`, SpillPrivate.lean:327). Spills are ordinary
  permission-checked accesses (`spill_speichern_ist_write64`,
  SpillPrivate.lean:93). The SCFG-side application is marked WAITING,
  not invented.

## 2. Findings (prioritized, actionable)

### F1. No combined TSO+LOCK step relation — the bridge's D-tso must define it

`TSOSchritt` (TSO.lean:92) covers issue/flush only; `lockSchritt` and
`casSchritt` are standalone `Option` functions with no step inductive
and no reachability relation. No file composes them: `grep
lockSchritt/casSchritt/TSOSchritt` outside `LockedOps.lean`/`TSO.lean`
returns nothing. Consequence: the two-core LOCK witness
(`locked_add_zwei_kerne`, LockedOps.lean:344) is META-level sequential
composition, not an interleaving under one relation — no other core's
buffered store can land between the two LOCKs, and no plain issue/flush
can land inside a LOCK's read-modify-write. The target-level analogue of
`w_kein_verlust` (RMW.lean:191) — no two LOCK RMWs read one message
under interleaving — is therefore unstatable, let alone proved.
**Task:** D-tso defines the combined machine (TSO steps + LOCK steps +
fence gates) with per-event access records; L-write proves the
`neu = wahl.ts + 1` correspondence against it. Owner: whoever owns the
bridge simulation, not the LockedOps author (whose CUTS already decline
it). Until then every `exchange` lowering is unmapped — refusal, per
REVIEW-TSO §3.1, still accurate at this HEAD.

### F2. Barrier-as-precondition, not barrier-as-effect (reproduced by probe)

`lockSchritt` (LockedOps.lean:60–74), `casSchritt` (LockedOps.lean:85)
and `.mfence` (LockedOps.lean:75–78) all return `none` unless the acting
core's buffer is ALREADY empty. They never drain; they gate. Reproduced
in `.tmp/WEAK-PROBE.lean` (private, 0 errors via `./lean-probe`):
negative probes show LOCK and CAS with one pending own-buffer byte both
evaluate to `none`; the positive control shows the same LOCK on the
empty buffer succeeds. **Task:** the lowering map D-lower must schedule
an explicit drain (flush sequence) before EVERY LOCK/CAS/fence site and
prove the buffer empty at the site; a lowering that emits LOCK with
pending stores gets refusal, not silicon semantics. This is consistent
with the bridge's O-irq/O-spawn local halves but must be wired into the
access-index labelling, or L-step will meet `none` where it expects an
RMW event. Not a bug: gating is the sound posture; silent draining
would be the bug.

### F3. No unified target footprint extraction for locked forms

`zugriff` takes `Decodiert` (pilot `Befehl`); `SperrBefehl` is a
separate type with separately carried `lesen`/`schreiben` fields in
`LockEreignis`. A consumer needing "the footprint of one target step"
(dead in F1's combined machine, alive in O-spill sorting and O-align
checking) must case-split over two types with no shared interface, and
nothing checks the `LockEreignis` footprints against `read64`/`write64`
the way `erfolg_store64_im_fuss` does for `zugriff`. **Task:** extend
`zugriff` (or a sum-type wrapper owned by the D-lower author) to cover
`SperrBefehl` with the same changed-bytes-in-footprint shape. Small,
startable now, no SCFG needed.

### F4. Three alignment vocabularies with no bridge lemma

`Ausgerichtet` (`Prop`, TSO.lean:428), `ausgerichtet8` (`Bool`,
LockedOps.lean:44), `addrAusgerichtet` (parameterized `Bool`,
OverlapRefusal.lean:27). `lock_xadd_atomar` assumes `ausgerichtet8`;
`zugriffOk` checks `addrAusgerichtet`; `paketAtomarMoeglich` states
`Ausgerichtet`. No lemma relates any two. They agree today by
inspection (`decide (a.toNat % 8 = 0)` vs `a.toNat % 8 = 0`), but a
consumer discharging O-align through `zugriffOk` and consuming
atomicity through `lock_xadd_atomar` currently pastes two unrelated
predicates. **Task:** one equivalence lemma (or a single-owner
definition with the other two as corollaries). Trivial, prevents drift.

### F5. `GetrenntK` names two different relations — O-spill misrouting hazard

Source `GetrenntK P K c` (ZielOrtMehrfaden.lean:161): carrier `c` is
thread-local in the call graph — the exact premise `hlokK` of
`schwach_ist_gX` (AtomarW.lean:281). Target `X86.GetrenntK r idx fremd`
(SpillPrivate.lean:31): two byte footprints are disjoint. Same short
name, different types, different meaning. Proving `X86.GetrenntK`
discharges NOTHING of `hlokK`; the spill-to-`lok` step (spill slot is a
fresh stack slot no other thread reaches) still needs a per-lowering
proof that neither file owns yet. **Task:** rename one (e.g.
`X86.FussGetrennt`) or add a firewall doc at both sites; assign the
spill-slot-is-`lok` lemma to the lowering owner. This is the most likely
place a future lane cites the wrong theorem.

### F6. `accessList` never emits `luecke` — the refusal constructor is dead code

`accessList_kein_luecke` (AccessList.lean:145): the owner always returns
`.voll`. The `luecke` constructor and `pruefeBefund` refusal exist but
no producer can emit them, and no per-rule syntactic classification
exists (the file's own CUTS admit ~69 of ~70 rules stay open). The
generic lemmas are over trace DELTAS (`zugriffe`/`ereignisse`), so a
lowering labelled by rule syntax has no proved table from its rule to
its entries. **Task:** none for this file (its design is sound); but
consumers must not read "always voll" as "every rule classified". The
per-rule micro-event labels of D-lower remain the largest single work
item — endorsed from TSO-GX-BRUECKE §5, unchanged.

### F7. OverlapRefusal is target-only — the cross-granularity half is open

`OverlapRefusal.lean` imports only target modules (`Speicher`,
`Zugriffe`, `Regionen`, `Bild`); no source `Deklaration`, no carrier,
no `TraegerWert`. `zugriffOk` admits footprints against `Region`
extents, but nothing maps a source carrier (`D.Tab ⊕ D.Glob`) to a
`Region`, and `einzelTraeger_wertUeberein` agrees bytes with a WORD,
not with a source-carrier value. The bytes→carrier-value step of
O-rely-values and the carrier-extent half of O-align are therefore
open. **Task:** C1 TableLayout (carrier enumeration + extents, still
absent at this HEAD) is the prerequisite; then one bytes↔carrier
agreement lemma per carrier shape. Ordered after C1, before L-read.

### F8. Narrow shared carriers remain unlowerable (A1 still absent)

`Befehl` (Typen.lean:53–68) is 64-bit only — verified unchanged at this
HEAD. No `NarrowOps.lean` in the tree. A 1-byte shared flag lowered
through a 64-bit access reads/writes neighbour bytes: that IS
cross-carrier overlap (counterexample-C shape), refused by `zugriffOk`.
So every narrow shared atomic/flag is refused end-to-end until A1 lands
or a proved masking discipline is added. Most real shared atomics are
narrow; this is the sharpest lowering blocker. **Task:** A1 per
WORK-ALLOCATION (unchanged); no masking shortcut without its proof.
Endorses REVIEW-TSO §3.1; verified still true, not inherited prose.

### F9. OBS-5 stands untouched — foreign/device reads still open (i)–(iv)

Nothing merged since TSO-GX-BRUECKE §4.9 changes the four proof needs:
`mfence_ordnung` covers the local half only (and F2 shows even that is
precondition-shaped); per-binding read footprints, the publication
lemma, and binding contracts are all still open. FenceDrain (lane 344)
and AtomicPayload (lane 350) are unmerged candidates — this audit takes
no position on them. **Task:** keep every image exercising gates or
foreign calls refused by final validation until per-binding contracts
are supplied AND proved (IMAGE-ABI §11(c) / OBS-5(iv)); record the blast
radius (every real hosted image: thread start/join, arena reserve/commit,
page return, report/exit) visibly in planning rather than narrowing
assumption (5) silently. If any of (i)–(iv) resists discharge at
lowering/binding level, the fallback is a REVIEWED `Spec.lean` diff
narrowing assumption (5) — decided by the simulation proof, not here.

### F10. Word atomicity: byte helpers prove byte facts only (no over-claim)

`einzelbyte_atomar` (TSO.lean:445) is width-1 by construction;
`paket_reisst` (TSO.lean:459) proves the two-byte tear;
`lock_xadd_atomar` (LockedOps.lean:145) assumes the declared
`ausgerichtet8` guard plus an empty own buffer — a profile contract, not
a silicon proof; the silicon correspondence for widths 2/4/8 stays OPEN
(per TSO.lean's own CUTS). `paketAtomarMoeglich` (TSO.lean:433) is a
predicate with no proved correspondence. No file derives multi-byte
atomicity from per-byte lemmas, and lane 421 (WordAtomicity, scheduled)
owns that proof. Verified compliant with the lane task's "no word
atomicity from byte helpers". **Task:** lane 421 proves the aligned-word
single-copy-atomicity correspondence against the combined machine of F1;
until then O-align refuses all multi-byte shared accesses.

### F11. No DRF-SC anywhere — store buffering is exhibited, not assumed away

`tso_store_buffering` (TSO.lean:414) reaches the both-stale-reads state
over real canonical bytes; no module maps x86 runs to G runs directly,
and every simulation obligation in the bridge targets W. `grep` for
`DRF-SC`/`DRF_SC`/`drf_sc` over `grammatik/Grammatik/X86/` returns no
blanket-assumption premise; the only DRF shape is the per-carrier
agreement conclusion of `schwach_ist_gX` (outside `Tg`), which is a proof
obligation (O-checker-race), not an assumption. **Task:** none — keep
the invariant that no new module introduces an SC-shaped premise; the
merge gate should keep rejecting any "x86 behaves as SC" shortcut by
pointing at `sb_erlaubt` vs `sb_sc_verboten` (Sicht.lean:446/566).

## 3. Non-findings (checked, deliberately not filed as bugs)

- TSO FIFO issue/flush order, youngest-wins forwarding, permission
  preservation, and the SB witness are proved over real bytes; the fence
  readiness condition is exactly own-buffer-empty with the foreign-buffer
  limitation proved (`zaun_kein_fremd_drain`). No repair owed.
- `zugriff` covers all 14 pilot forms with success/refusal linkage both
  ways; the empty-type non-claims (`kein_atomarer_zugriff`,
  `keine_ablauf_spur`) are the honest posture. No repair owed.
- AccessList generic completeness over trace deltas is real; `IstRMW`
  manufactures no silent RMW; the `taP` witness is non-degenerate
  (table written, memory-changing steps). No repair owed.
- `cas_schleife_unbeschraenkt` proves retry unboundedness; failure stutter
  claims no progress; the `RmwForm` refusal uses real extracted
  footprints. The cost/shape separation matches O-cas-cost. No repair owed.
- `fussDisjunktB_klingt` soundness, the adjacent-carrier joint witness,
  and the counterexample-C refusal are proved as stated. No repair owed.
- Spill commutation and TSO-side preservation hold over the canonical
  vocabulary with a reached memory-changing witness; the SCFG-side wait
  is marked, not bypassed. No repair owed.
- REVIEW-TSO's line references were re-verified exact-or-off-by-one at
  this HEAD during this audit; no stale citation found.

## 4. Prioritized repair / missing-bridge tasks

1. Combined TSO+LOCK step machine with access records (F1) — blocks
   every `exchange` lowering; owner: bridge simulation lane.
2. D-lower drain scheduling before each LOCK/CAS/fence site (F2) —
   with the empty-buffer proof at the site; part of (1)'s consumer.
3. Unified target footprint extraction covering `SperrBefehl` (F3) —
   small, startable now.
4. `GetrenntK` rename/firewall plus spill-slot-is-`lok` lemma owner
   (F5) — cheap, prevents silent misrouting.
5. Alignment-vocabulary equivalence lemma (F4) — trivial.
6. TableLayout C1 then bytes-to-carrier agreement (F7) — order matters.
7. NarrowOps A1 (F8) — sharpest lowering blocker for real flags.
8. Binding contracts and publication lemma (F9) — refusal posture kept.
9. Word atomicity lane 421 against the F1 machine (F10); no SC
   shortcut ever (F11).

## CUTS

This audit proves nothing in Lean: no TSO machine, no access-list
function, no lowering map, no simulation lemma, no decoder, no cost
transfer. It is source inspection of the six listed implementation files
against the bridge design and its review, with verdicts, three decided
Lean probes (F2, private `.tmp/WEAK-PROBE.lean`, 0 errors), and precisely
stated holes. F2 evidence beyond source reading: with one pending
own-buffer byte, `lockSchritt` and `casSchritt` both evaluate to `none`
by `decide`, while the same LOCK on `lockStart` (empty buffers) succeeds
— barrier-as-precondition, not barrier-as-effect. `#print axioms`
obligations apply to wave-B Lean work, not to this document.
