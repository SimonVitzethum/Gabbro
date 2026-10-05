# MUSE-REPORT-1149: Capstone — one coherent machine over all accepted families

## What was done

New file `grammatik/Grammatik/X86/HwKapstein.lean` (1023 lines) plus one
`import Grammatik.X86.HwKapstein` line appended to `grammatik/Grammatik.lean`.
No other existing file touched. Every accepted definition is reused unchanged
(lifted, never redefined); no `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe` (checked by grep: only comment substrings).

**Definitions:**
- `KapEreignis` — union event type, 21 tags: `basis` plus one per merged
  family step (`lockRmw`, `wort`, `stapel`, `isa`, `addr`, `muldiv`,
  `lockFetch`, `uc`, `port`, `fp`, `fehler`, `tor`, `vec`, `drain`,
  `fwd`, `nested`, `int`, `system`, `bild`, `instanzen`).
- `HwVollSchritt` — the single composed machine step: one constructor per
  tag, each carrying the family's accepted adapter equation or step
  relation (`HwSchritt`, `adapterLockRmw`, `adapterWort1147`,
  `stapelAdapter`, `adapterIsa`, `adapterAddr`, `adapterMulDivWidth`,
  `adapterLockFetch`, `HwDev1133.adapterUc1133`,
  `HwDev1133.adapterPort1133`, `FpCtrlSchritt`, `HwFehlerSchritt`,
  `HwTorSchritt`, `HwVecSchritt`, `drainAdapter`, `fwdAdapter`,
  `adapterVerschachtelt`, `adapterInterrupt1125`, `adapterSystem`,
  `adapterBild`, `adapterInstanzen`).
- `kapTag` — union tag function (0–20), the disjointness interface.

**Theorems:**
- `kap_wf` — every union step preserves `HwWf` (via each family's accepted
  lemma; helpers `kap_adapterAddr_wf`, `kap_adapterInterrupt_wf`
  (via `asyncSchritt_wf_allgemein`), `kap_adapterInteger666_wf`,
  `kap_adapterSystem_wf`).
- 21 exact embedding iffs `kap_*_embedded` (equation/relation ↔ union step).
- `kap_verweigert` — DMA, fault-as-state-step, ISA/addressed refusal events,
  bare LOCK stay refused.
- `kap_interrupt_sync` — extended-machine sync steps embed via the union base.
- `kap_tags_disjoint` — base tag vs all 20 family tags (constructor
  discrimination; axiom-free); `kapTag` extends the argument to families.
- `kap_decode_prioritaet` — width dispatcher defers to the unified chain.
- 15 exhibited union steps `kap_step_lock/stapel/wort/isa/fp/basis/addr/
  fehler/lockFetch/muldiv/tor/uc/vec/drain/fwd` (closed equations, decided
  or extracted from the families' own reached witnesses).
- `kap_zeuge` — joint witness: the 15 steps, decoder pins
  (`pin_wdHw_wdmul32`, `pin_wdHw_ext_mul64`), refusal instances, wf facts,
  and shared non-degeneracy (two cores, locked word 10→15, owner-only
  forwarding, drains 0→42 observed from both cores).
- CUTS block plus `#print axioms` for every main theorem: all depend only
  on `[propext, Quot.sound]` (subset of the goal standard; `kap_tags_disjoint`
  is axiom-free).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s)`, `Build completed successfully
(644 jobs)`. `./lean-probe grammatik/Grammatik/X86/HwKapstein.lean`:
`== 0 error(s)`. (Two earlier probe timeouts were build-slot contention;
retries passed unchanged.)

## What remains open (see CUTS)

- `port`, `nested`, `int`, `system`, `bild`, `instanzen` tags are embedded
  by equation only; their successes live in the family files, not
  re-exhibited as union steps here.
- `HwBildFamilien` (fetch/decoder lemmas) and `HwFeatureStep` (tor-gate
  refinements) add no step plug and have no tag.
- Byte-decoder disjointness beyond width-vs-unified stays open (LOCK fetch
  vs unified fetch is family-local); no unhandled overlap was found.
- No hardware correspondence beyond self-consistency; no W/GX bridge; no
  source/checker/contract/entry/budget claim.

## What I believe is wrong in the task

1. The named family lanes (1119–1141) do not match the merged modules: the
   tree holds a wider, differently numbered set (`HwLockRmw`, `HwWordAtomicity`,
   `HwStackCalls`, `HwIsaFamilies`, `HwAddressed`, `HwMulDivWidth`,
   `HwLockFetch`, `HwDevices`, `HwFpControl`, `HwFaults`, `HwFeatureGates`,
   `HwVector`, `HwSystemForms`, `HwNestedInterrupts`, `HwDrainGeneric`,
   `HwForwardingGeneric`, `HwLoadedImage`, `HwBildInstanzen`, …). The union
   covers all merged `HwMaschine` plugs found by grep, which is a superset
   of the listed lanes; nothing was assumed about unmerged lanes.
2. "The union is disjoint on the decoder" is only partially dischargeable at
   capstone level: proved for tags by construction and for width-vs-unified
   bytes by the accepted priority lemma; the rest is stated open in CUTS.
3. Async interrupt delivery cannot be a closed `HwMaschine` step without its
   control snapshot; the union carries the snapshot in the event (accepted
   shape) and proves the sync embedding separately — this is a boundary,
   not a gap in the union.
