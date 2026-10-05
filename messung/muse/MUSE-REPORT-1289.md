# MUSE-REPORT-1289: Capstone steps — reached union steps for the six equation-only tags

## What was done

New file `grammatik/Grammatik/X86/HwKapsteinSteps.lean` (610 lines) plus one
`import Grammatik.X86.HwKapsteinSteps` line appended to `grammatik/Grammatik.lean`.
No other existing file touched. Every accepted definition is reused unchanged
(lifted, never redefined); no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`
(checked by grep: only comment substrings like "admitted").

**Port witness machine (new, §1):** `kapPortBytes`, `kapPortMem`, `kapPortKern`,
`kapPortStart` — two cores, empty buffers, full silicon; core 0 fetches
`OUT 0x60, AL` (`E6 60`) at `0x1000`. `kapPortStart_wf`, `kapPort_fetch`
(fetch equation closed by `decide`), `kapPortDec`, `kapPortEv`
(OUT under direct CPL<=IOPL admission, full-map card, empty log).

**Six plug equations + six union steps (one per equation-only tag):**
- `kapPlug_port` (via `HwDev1133.portAdapter_aus_fetch`) / `kapStep_port`
- `kapPlug_nested` (via `nestVerschachtelt` + `nestV_rip`) / `kapStep_nested`
- `kapPlug_int` (via `witNmi_erfolg_ex`) / `kapStep_int`
- `kapPlug_system` (via `sysWit_cli_if` + `adapterSystem_ok`) / `kapStep_system`
- `kapPlug_bild` (via `inst_schritt_muldiv` + `adapterBild_vereinbarung`) / `kapStep_bild`
- `kapPlug_instanzen` (via `inst_schritt_vec` + `adapterInstanzen_vereinbarung`) / `kapStep_instanzen`

**Extended-union properties:**
- `kapSteps_wf` — every exhibited step preserves `HwWf` through the capstone's `kap_wf`.
- `kapSteps_embedded` — every exhibited union step returns its plug equation
  through the six capstone iffs (both directions exercised on the exhibited steps).
- `kapSteps_tags_disjoint` — the six tags pairwise distinct (15 pairs, via `kapTag`).

**Plug-less family coverage (§8):**
- `familien_plug_gleich : adapterBild = adapterInstanzen` (one plug, two tags —
  no third plug exists for `HwBildFamilien` to tag).
- `kapFamilie_muldiv/shift/setcc/cmov/fp` — all six `HwBildFamilien` rows step
  through the instanzen tag on the families' own `stepExt` successes.
- `kapFamilie_feature_tor` — the `HwFeatureStep` admitted vector step executes
  exactly as the tor arm (via `hwStepTor_verbindung_zeuge` + `kap_tor_embedded`).

**Refusals + joint witness:** `kapSys_frei`, `kapPort_falschDecodiert_verweigert`
(forged IN decode), and `kapSteps_zeuge` — all six steps, the tor-arm refinement
step, well-formedness of every start machine, planted refusals
(`witNmi_maskiert_verweigert`, `nestDritt_verweigert`), and shared non-degeneracy
(owner-only forwarding and drains changing actual shared memory 0 to 42 observed
from both cores on three machines; the NMI frame observably changes memory).

CUTS block plus `#print axioms` for every theorem: all depend only on
`[propext, Quot.sound]` or subsets (fetch equation and tags-disjoint use fewer);
no `Classical.choice` anywhere.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed successfully (677 jobs)`.
`./lean-probe grammatik/Grammatik/X86/HwKapsteinSteps.lean`: `== 0 error(s)`.

## What remains open (see CUTS)

- No hardware correspondence beyond self-consistency; OUT opcode bytes are the
  accepted canonical subset, not silicon truth.
- No W/GX bridge; no source/checker/contract/entry/ABI/loader/budget claim.
- UC-load leg still refuses on the bare machine; device continuity rides the
  extended relation.
- Async/nested snapshots ride in the events; no independent control-state model.

## What I believe is wrong in the task

Nothing blocking. Two notes: (1) "joined into the capstone's non-degenerate
two-core state" reads as one shared machine, but the capstone itself witnesses
per-family machines — this lane follows that shape (per-family two-core machines
plus one joint conjunction), which is the faithful reading. (2) The system-plug
proof needs the snapshot equation in `sysSnapSchritt` form while the family
witness speaks `sysAusfuehren`; the bridge is a three-way case split with the
two failure legs contradicting `sysWit_cli_if` — no new witness was needed.

No family witness failed to lift: no FINDING to report.
