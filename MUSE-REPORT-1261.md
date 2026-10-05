# MUSE-REPORT-1261: Pipeline over TSO — store instructions on the issue/drain path

## What was done

New file `grammatik/Grammatik/X86/PipelineTsoStore.lean` (plus one import line
in `grammatik/Grammatik.lean`), proving the store case on the TSO issue/drain
path. A lowered 64-bit store is eight byte issues into the acting core's TSO
buffer (`tsoStoreIssue`, reusing the accepted `hwWortAusgabe`, never the SC
word effect), each issue one `HwSchritt.gibAus` event, followed by
oldest-entry drains; after an exclusion-checked drain the shared-memory
footprint equals the sequential `write64` shadow with read-back.

Exact new definitions/theorems (namespace `Gabbro.Grammatik.X86`):

- `tsoStoreIssue`, `tsoStoreValid` (lowering + recomputing validator)
- `tsoStore_puffer`, `tsoStore_kein_speicher`, `tsoStore_valid`,
  `tsoStore_stern` (issue path: exact eight entries, no shared-memory change
  until drain, eight `HwSchritt` store-issue events over accepted
  `issueListe_stern`)
- `pipeline_correct_tsoStore` (main theorem: empty acting buffer + issue +
  exclusion-checked drain = sequential `write64` footprint with read-back,
  via accepted `drainGleichWrite64`; the `write64` equation is the same
  sequential shadow `Pipeline.worldRep_store` uses — no second source
  interpreter)
- `pipeline_refuses_tsoStore_guard`, `pipeline_refuses_tsoStore_leer`,
  `pipeline_refuses_tsoStore_dunkel` (refusals: guard store, empty drain,
  dark observation)
- `tsoStoreGiftWache`, `tsoStoreGiftLeer`, `tsoStoreGiftDunkel` (poison
  probes: each refusal fired on a concrete witness machine)
- `grpWitM0`, `grpWitM1`, `grpWit_wf`, `grpWit_fold`, `grpWit_issue`,
  `grpWit_leer0`, `grpWit_valid`
- `pipeline_correct_tsoStore_zeuge` (joint non-degenerate `_zeuge`: the
  witnessed issue reaches exactly the accepted grouped drain start, the
  validator accepts it, the drain installs the `write64` footprint,
  owner-only forwarding of 42 with the foreign core reading zero, a drain
  changing shared memory 0 to 42 observed from both cores, beside the three
  refusal probes)

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineTsoStore.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (644 jobs).`
- `#print axioms`: every new theorem depends at most on `[propext,
  Quot.sound]` (subset of the required `propext, Classical.choice,
  Quot.sound`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No existing file was changed except appending the import to
  `grammatik/Grammatik.lean`; `OptimizationRules.lean` /
  `OptimizationWitnesses.lean` untouched; no new `N`/`gift`/example numbers
  needed (Rust out of scope, probes are Lean witness theorems).

## What remains open (see CUTS in the file)

- No `store64` fetch/decode/execute leg: the lowered store is the eight TSO
  byte issues, not a fetched `Befehl.store64` run. Relating
  `Pipeline.senkStmt` slot stores (register/address setup, `WorldRep`) to
  `tsoStoreIssue` stays OPEN.
- No silicon correspondence, no LOCK/RMW/fault/interrupt/fence/FP/SIMD path,
  no target-to-W/GX simulation.

## What I believe is wrong in the task

- The task states this is a "FOLLOW-UP of lane 1169 (`PipelineTso.lean`)"
  whose `pipeHw_reg_einbettung` excludes stores. **There is no
  `PipelineTso.lean` in this snapshot** (no `PipelineTso*`, no
  `pipeHw_reg_einbettung` anywhere in `grammatik/`), so no lift onto it
  could be stated. The file builds on the accepted pieces directly
  (`HardwareExecution`, `WordAccessGrouping`, `HwStackCalls`,
  `HwDrainGeneric`) and records this in CUTS. If lane 1169 lands, a small
  follow-up can state the register-path embedding against it.
- Repair note (for reviewers): the first witness attempt (`grpWit_issue`
  by `rfl`) failed because nested `pufferSetze` layers are not definitionally
  equal to the flat buffer lambda. The accepted fix proves the fold equation
  propositionally (`grpWit_fold`: decided `isSome` + `issueListe_haengt_an`
  / `issueListe_anderer_kern` / `issueListe_kein_speicher` /
  `issueListe_erhaelt_berechtigungen` + `funext`), following the precedent of
  `concIssue_b64_gruppe`.
