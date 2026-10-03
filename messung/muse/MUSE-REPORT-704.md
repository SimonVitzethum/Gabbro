# MUSE-REPORT-704: Generic port bus and precise architectural IO permissions

## What was done

New module `grammatik/Grammatik/X86/DeviceBusHardwareExecution.lean`
(~955 lines) plus one additive umbrella line
(`import Grammatik.X86.DeviceBusHardwareExecution` in
`grammatik/Grammatik.lean`). No source/emitter/Spec/checker change, no
second IN/OUT interpreter: the accepted `decodeIo`/`fetchIo`,
`portVon`/`ausGabe`/`einMische`, `ioWit*` image, `ArchFehler`,
`TSOZustand`/`zaunBereit`, `FpZustand`/`kontextReset` are reused
throughout.

1. **Precise TSS checks** (`TssKarte`, `tssBitFrei`, `tssBereichAux`,
   `tssBereichFrei`): every byte covered by 8/16/32-bit widths is
   checked; unspanned, past-65535 and missing-map bytes deny
   (`karte_fehlt_verweigert`, `port_raum_ende_verweigert`).
2. **Selected long-mode rule** (`IoBerechtigung`, `archZugelassen`):
   CPL<=IOPL admits with no bitmap consult (`arch_direkt`), else the
   range decides (`arch_bitmap`); denial is #GP via `busFehler` in the
   accepted fault vocabulary.
3. **Compiler admission split** (`CompilerProfil`,
   `compilerZugelassen`): the old conjunction kept as sufficient-only
   profile, with `compiler_sound` and the `compiler_unvollstaendig`
   witness (direct leg admits what the profile refuses).
4. **Generic interface** (`BusAntwort`, `BusZustand`, `BusSchritt` with
   `aus`/`ein`): arbitrary device state plus an allowed read/write
   relation keyed by port/direction/width/driven-value. IN truncation
   and OUT implicit source go through `einMische`/`ausGabe`; frames
   (`busSchritt_speicher/flags/spur_waechst/perm/rip`) hold for every
   relation; fetched selection (`busSchritt_aus/ein_fetch`) goes through
   the accepted `fetchIo` (`fetchIo_erfolg`).
5. **Ordering/completion** (`ordnungOk`,
   `ordnung_braucht_leeren_puffer`,
   `ordnung_verweigert_bei_vollem_puffer`, `BusFertig`,
   `fertig_getrennt`, `brauchtGeraetVollendung`): Table 20-1 exposed as
   a gate (own buffer drained, both directions), never derived from a
   no-race proof; CPU/device completions are distinct constructors with
   the posted-OUT obligation.
6. **Two instances**: the old latch as `latchErlaubt` with
   `latch_aus/ein_sound` and both old-step lifts (`latch_aus/ein_lift`
   via `ioSchritt_aus/ein_erfolg` + `ioZugelassen_heisst_alle`); the
   port-distinguishing `TabellenGeraet`/`tabellenErlaubt` with
   `tabelle_unterscheidet` (+ closed `tabelle_unterscheidet_zeuge`)
   and the proved latch limit `latch_unterscheidet_nicht`.
7. **Adapters**: `bus660Schritt` with XMM/FP/memory frames;
   refusing `mmio694Adapter` stub; three-sided `busValOk` with
   `busValOk_heisst`.
8. **Joint witness** (`bus_zeuge_gemeinsam`): reached generic IN/OUT
   (`wit_schritt1/2`, device `0x1234` to 52, accumulator to 52, RIP at
   4100, memory/flags/FP frames) beside the accepted memory-changing
   pilot store (`ioWit_dritter_speichert` from a zeroed cell),
   width-boundary split, wrong-privilege #GP, map mutation,
   malformed-byte fetch refusal and order-gate mutation.

## Exact new names

Types: `TssKarte`, `IoBerechtigung`, `CompilerProfil`, `BusAntwort`,
`BusZustand`, `BusSchritt`, `BusFertig`, `TabellenGeraet`,
`GeraetZustand` reused. Key defs/theorems: see `#print axioms` block at
the file end (31 prints). Joint witness: `bus_zeuge_gemeinsam`.

## Last build result

`./lean-bau`: `Build completed successfully (472 jobs).`
`./lean-probe grammatik/Grammatik/X86/DeviceBusHardwareExecution.lean`:
`0 error(s)`; all axioms within `[propext]` / `[propext, Quot.sound]`
(subset of the `gabbro_ziel` axioms). One advisory linter hint remains
(`h` unused in the `bus660Schritt` body: the reached-step evidence is a
caller-side requirement token, kept deliberately).

## What remains open

In CUTS: hardware correspondence beyond cited SDM entries; MMIO/DMA
execution; INS/OUTS, REP, LOCK-on-IO, virtual-8086, timing; the
per-access target-to-W/GX simulation (the ordering gate is the
obligation the TSO bridge must discharge); source/ABI/image/entry/
budget links; lane-672 trap scope. Raw `BusSchritt` trusts its decoded
argument; fetched admission lives in the selection theorems.

## Task remarks

- Nothing in the task turned out wrong; one clarification: "694" has
  no accepted module in this tree, so the device/MMIO side is exported
  as the refusing `mmio694Adapter` stub with explicit obligations
  rather than a link against a producer interface.
- `witStart` collided with `FlagDependencies.witStart` at umbrella
  build time (per-file probes stay green); renamed to `busWitStart`.
- Two `lean-probe` runs exceeded their timeouts under machine load
  with no output; both passed on retry with a larger budget. No proof
  change was needed.
- Manual provenance recorded in the file header: Intel SDM
  325462-093US (Sep 2026), txt lines 58368-58460 (IN),
  72010-72100 (OUT), 24391-24498 (20.5.x), 24500-24553 (20.6/Table
  20-1). Intel-profile evidence only; AMD retrieval failed upstream
  and no AMD claim is made.

## Integration repair (failed gate, no merge)

The integration gate failed with: `environment already contains
'Gabbro.Grammatik.X86.witFp' from
Grammatik.X86.MemoryTypeHardwareExecution`. A lane that landed after
my base defined the flat `X86.witFp`, colliding with my witness
extended state of the same name. Nothing was merged; no guarantee was
weakened to fix it.

Repair: every declaration of the module now lives in the nested
lane-unique namespace `Bus704`
(`Gabbro.Grammatik.X86.Bus704.*`), via two added lines
(`namespace Bus704` / `end Bus704`) plus a plain comment. No
definition, statement, or proof changed; all 31 `#print axioms`
outputs are identical except for the qualified names. This ends the
whole flat-name collision class against concurrently landing lanes,
not just the one reported `witFp` (a single rename would have left
the next collision to the next gate round).

Re-verified after the repair: `./lean-probe
grammatik/Grammatik/X86/DeviceBusHardwareExecution.lean` reports `0
error(s)`; `./lean-bau` reports `Build completed successfully (472
jobs)`. Consumers must qualify names (`Bus704.bus660Schritt`,
`Bus704.bus_zeuge_gemeinsam`, ...). A fresh independent review of the
changed commit is still required; acceptance of the full
source/binary chain is not claimed.
