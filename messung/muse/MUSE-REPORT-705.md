# MUSE-REPORT-705: Exact review of author 704 (generic port bus and precise IO permissions)

CANDIDATE: 704 af7ebf38f6d9e40b622ce4246f0f80ac64136d71
VERDICT: ACCEPT

## Re-review of the repaired snapshot (new pinned HEAD)

The previous verdict on `32415e09` is superseded: the integration
gate failed after that commit with `environment already contains
'Gabbro.Grammatik.X86.witFp' from
Grammatik.X86.MemoryTypeHardwareExecution` (a concurrently landing
lane claimed the flat name; nothing was merged). The author repaired
with commit `af7ebf38` ("namespace Bus704 against integration
collision") and this report re-reviews ONLY the new pinned snapshot
(HEAD `af7ebf38`, same base `dbfdc83c`, same 3 files, `clean: true`).

Delta verified line by line: the module grew 956 to 964 lines, and
the 8 added lines are exactly the lane-scope comment (6 lines),
`namespace Bus704` and `end Bus704` (module lines 34-39 and 962).
Every definition, statement and proof re-checked by spot grep is
byte-identical (`tssBitFrei`, `volleKarte` basis 0 / grenze 8192,
`archZugelassen` direct/range legs, `ordnungOk`, `latchErlaubt`,
`tabellenErlaubt`, `mmio694Adapter`, `busValOk`,
`bus_zeuge_gemeinsam`); all 31 `#print axioms` lines are present,
now `Bus704`-qualified. The umbrella diff is still one additive
import line; PATCH still touches only the 3 registered files.
Forbidden-token word grep on the new module is clean; the new
BUILD-EVIDENCE honestly records the failed intermediate namespace
attempt, then `./lean-probe` `0 error(s)` with
`Gabbro.Grammatik.X86.Bus704.*` axiom names and `./lean-bau`
`Build completed successfully (472 jobs).` Axioms remain within
`[propext]` / `[propext, Quot.sound]`.

The repair ends the flat-name collision class (no declaration of
this module remains at flat `X86` scope), weakens no guarantee, and
changes no claim: consumers qualify names (`Bus704.bus660Schritt`,
`Bus704.bus_zeuge_gemeinsam`, ...). All findings and bounded notes
below, established on the prior snapshot, were re-confirmed
unchanged on the new one. No live build was run in this lane (live
tree at `4e1b256a` contains neither the candidate nor the colliding
lane; this lane owns only this report).

## What was done

Report-only exact review of the pinned author-704 snapshot
(`.tmp/review/author-704/`, HEAD `af7ebf38`, base `dbfdc83c`,
files `MUSE-REPORT-704.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/DeviceBusHardwareExecution.lean`, 956 lines).
Inspected in full sequential ranges: the complete new module
(lines 1-956), the PATCH diff (1073 lines), OWNER-TASK.md, the full
MUSE-REPORT-704.md, and BUILD-EVIDENCE.json (all 30 probe/build
entries). Independently checked every acceptance criterion from the
owner task against the snapshot code, the live-tree dependencies
(`DeviceHardwareForms`, `TSO`, `HardwareFaults`, `ScalarFloat`),
and the official local reference snapshot
(`.tmp/HARDWARE-REFERENCES/`, Intel SDM 325462-093US, sha256
`a4a62e6a…f9168ee599f321`, verified 2026-10-02T18:40:25Z).

## Findings (each review criterion, with evidence)

1. **Generic device, not a hardcoded latch.** The interface is
   `BusAntwort (D : Type) := D -> IoDir -> IoBreite -> Nat -> Nat ->
   D -> Nat -> Prop`, keyed by actual port, direction, width and
   driven value; `BusSchritt` carries an arbitrary `erlaubt` relation
   and all frame theorems (`busSchritt_speicher/flags/spur_waechst/
   perm/rip`) quantify over every relation. The old latch survives
   only as the explicit instance `latchErlaubt` with soundness
   (`latch_aus/ein_sound`) and old-step lifts
   (`latch_aus/ein_lift`). Generality is established by the SECOND
   instance `tabellenErlaubt` (per-port register file) with
   `tabelle_unterscheidet` (ports 96/97 answer differently from one
   start) plus the proved latch limit `latch_unterscheidet_nicht`.
   No single-latch masquerade.
2. **Whole-width bitmap checks.** `tssBereichAux/Frei` checks every
   byte `port..port+nbytes-1` with `ioBreiteBytes` 1/2/4; range-end
   (`wit_breite_16_an_96_verweigert` vs `wit_breite_8_an_96_frei`),
   past-65535 (`port_raum_ende_verweigert`) and missing-map
   (`karte_fehlt_verweigert`) bytes all deny. Not start-port-only.
3. **Compiler admission separated from silicon.** The old
   conjunction is kept ONLY as `compilerZugelassen` with
   `compiler_sound` (admitted implies `archZugelassen`) and the
   `compiler_unvollstaendig` witness (CPL 0/IOPL 3 admits port 96
   through the direct leg while the profile refuses on the same set
   bit). Refusal is never presented as a fault; denial faults as
   `ArchFehler.gp` only through `busFehler` on the architectural
   rule. No `schalter`/OS-ready Bool in the silicon path; the map is
   checked data (`TssKarte` with basis/limit/bits).
4. **Ordering exposed, not faked.** `ordnungOk` (own TSO buffer
   drained, both directions) is an explicit gate with
   `ordnung_braucht_leeren_puffer` and
   `ordnung_verweigert_bei_vollem_puffer`; nothing derives a drain
   from a no-race proof. CPU vs device completion are distinct
   constructors (`BusFertig.cpu/geraet`, `fertig_getrennt`) with the
   posted-OUT obligation (`brauchtGeraetVollendung`). Combined only
   in the three-sided `busValOk` with `busValOk_heisst`.
5. **Architecture, not just green.** Reuses the single accepted
   decoder/fetch (`fetchIo`, `fetchIo_erfolg`) and helpers
   (`portVon`, `ausGabe`, `einMische`) — no second opcode/register
   arithmetic; OUT reads the accumulator implicitly
   (`wit_aus_liest_rax`), IN merges with width discipline including
   32-bit zero-extension (`wit_p32_loescht_oben`); flags preserved
   ("Flags Affected: None"), RIP advances past valid lengths, memory
   untouched for every relation, FP/XMM preserved in `bus660Schritt`
   over reached steps. Denial is the absence of a step (no silent
   skip, no pre-fault state change).
6. **Witnesses and mutations.** `bus_zeuge_gemeinsam` jointly
   instantiates reached IN then OUT (device `0x1234` to 52, two
   observations, accumulator 52, RIP 4100) beside the accepted
   memory-changing pilot store (`ioWit_dritter_speichert` 0 to 52),
   flags/RAM/FP frames, width-boundary split, wrong-privilege #GP,
   admitting map mutation, malformed-byte fetch refusal and the
   order-gate mutation. Non-degenerate (changed device AND reached
   RAM store). Closed table witness `tabelle_unterscheidet_zeuge`.
7. **Mechanical gates.** Word-boundary grep for
   `sorry/admit/native_decide/axiom/unsafe` on the snapshot module
   is clean (only English "admits" substrings). Axioms per
   BUILD-EVIDENCE are within `[propext]` / `[propext, Quot.sound]`,
   a subset of the `gabbro_ziel` axioms. Final entry:
   `./lean-bau` → `Build completed successfully (472 jobs).`
   (Intermediate reds — a `witStart` umbrella collision and draft
   errors — were repaired before the pinned commit; the collision
   rename to `busWitStart` is recorded.) PATCH scope is clean: one
   new module, one additive umbrella import line, the report; no
   source/emitter/Spec/checker or friend-reserved changes.
8. **Manual provenance verified, not trusted.** Cited txt ranges
   resolve under standard (`grep`/`sed`) numbering: 58368 IN entry,
   72010 OUT opcode table, 24391 20.5 heading, 24538 Table 20-1
   inside 24500-24553 (my first Python `splitlines` numbering
   disagreed because it also splits on bare CR bytes; `sed -n`
   confirms the author's numbers). Intel-profile evidence only;
   AMD unavailability disclosed; no silicon claim.

## Bounded acceptance (explicit bounds, not defects)

- Raw `BusSchritt` trusts its decoded argument; fetched admission
  lives in the proved selection theorems (`busSchritt_aus/ein_fetch`).
  Declared in CUTS; same shape as the accepted `ioSchritt`.
- The 660 adapter is instantiated at the latch; the fully generic-D
  adapter and the per-access target-to-W/GX simulation stay open and
  are named in CUTS with the drain obligation the bridge must
  discharge. MMIO/DMA refuse (`mmio694_verweigert_*`) with
  obligations explicit.
- `bus660Schritt` takes the reached-step evidence `h` as a
  caller-side requirement token (one advisory unused-variable lint,
  disclosed in the author report); the claim is reachability-gated,
  not vacuous.
- TSS limit uses an exclusive-bound convention (internally
  consistent; `volleKarte` spans exactly 8192 bytes); `ordnungOk`
  collapses the Table 20-1 current/pending distinction to the
  pre-access drained gate, as the cited rows require.

## What remains open

Per CUTS, unchanged by this review: hardware correspondence beyond
the cited SDM entries; MMIO/DMA execution; INS/OUTS, REP, LOCK-on-IO,
virtual-8086, timing; the TSO bridge simulation; source/ABI/image/
entry/budget and lane-672 trap scope.

## Last build result

No live build was run in this lane: the live clone at `f2ef4878`
does not contain the candidate module, and this lane owns only this
report (no source changes, tree verified clean). Evidence is the
pinned BUILD-EVIDENCE.json final entry: `./lean-bau` →
`Build completed successfully (472 jobs).`, and `./lean-probe`
on the module → `0 error(s)` with the axiom block as listed.

## Task remarks

Nothing in the owner task turned out wrong. One clarification for
the record: "694" has no accepted module in this tree, so the
refusing `mmio694Adapter` stub with explicit obligations is the
correct bounded export, as the author states. The lane-705 prompt's
"Own only MUSE-REPORT-693.md" is a numbering typo; this lane owns
MUSE-REPORT-705.md only, per LANE.md.
