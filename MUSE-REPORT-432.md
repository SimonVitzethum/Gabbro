# MUSE-REPORT-432: Finite pairwise separation checker (RegionSeparation)

## Task
Create ONLY `grammatik/Grammatik/X86/RegionSeparation.lean` plus one additive
X86 import at end of umbrella. Prove a generic finite pairwise separation
checker sound for actual target regions/layout and byte footprints. Reuse
existing range/permission definitions; prove positive multi-region actual
store frame and overlap/wrap negative witnesses. No number-to-pointer,
freshness or source region identity conjured. Source/linker/loader
correspondence OPEN.

## What was done
New module `grammatik/Grammatik/X86/RegionSeparation.lean` (~470 lines),
built in small incremental `./lean-probe` steps (skeleton -> soundness ->
frames -> layout bridge -> witnesses -> CUTS/axioms), every step probe-green.
One additive import line at end of `grammatik/Grammatik.lean`.

### Definitions (all reused vocabulary, no new model)
- `allePaareDisjunkt : List Region -> Bool` — quadratic decided pairwise
  `regionDisjunkt` check (Regionen.lean).
- `keinUmbruchR / alleOhneUmbruch` — explicit `basis + len <= 2 ^ 64`
  no-wrap bound (Nat addition never wraps; the bound is the check).
- `trennungOk` — `alleOhneUmbruch && allePaareDisjunkt`.
- `abschnittAlsRegion (bias) (s : Abschnitt) : Region` — image section as
  target region (Bild.lean).

### Theorems (every premise used by its proof; no `sorry/admit/axiom/native_decide/unsafe`)
- `regionDisjunkt_symm`, `allePaareDisjunkt_mem` (pairwise soundness:
  verdict + membership + inequality -> disjoint), `alleOhneUmbruch_mem`,
  `trennungOk_paare`, `trennungOk_ohne`, `trennungMitglied_ohneUmbruch`.
- `regionDisjunkt_fuss_disjunkt` — bridge to `Disjunkt` via
  `disjunkt_von_intervallen` (explicit `OhneUmbruch` on both sides).
- `trennung_schreibt_rahmen` (read64 preservation), `trennung_schreibt_bytes`
  (per-byte frame), `trennung_rahmen_mehrere`, `trennung_bytes_mehrere`
  (multi-region verdict-level frames over `write64_rahmen`/`read64_rahmen`).
  Per-byte TSO is not multi-byte atomicity: footprints are byte sets.
- `virtReich_regionDisjunkt`, `paarweise_virt_trennung` — accepted image
  intervals re-read in region vocabulary (validator stays the decider).

### Witnesses (decided + real memory-changing execution)
- ACCEPTED: `trennung_zeugen_ok` (three regions 8192/8, 8200/8, 65536/16).
- REFUSED: `trennUeberlapp_verweigert` (overlap), `trennUmbruch_verweigert`
  + `trennUmbruch_trennung_verweigert` (wrap fails one leg and the verdict).
- `rahmen_zeugen_schreibt`: real `write64` of 42 at 8192 goes through,
  `read64` at 8200 preserved with value `some 0` (`trennLiest8200`), byte at
  8200 unchanged, byte at 8192 observably changed — through the generic lemmas.
- `trennBild_*`: accepted 3-section profile-48 image feeds the checker
  (`trennBild_trennung` via the generic bridge).
- JOINT `trennung_zeuge`: verdict + source writer fact (`zeugenU_schreibt`:
  table `konto` written by `setze`, non-degenerate) + reached run memory
  change (`zeuge_speicher_aendert_sich`: byte 42 at 8192) + real store frame.
- `trennung_rahmen_zeugen`, `trennung_bytes_zeugen`: verdict-level frame
  consumers with decided membership/inequality.

### Checks
- `./lean-probe grammatik/Grammatik/X86/RegionSeparation.lean`:
  `0 error(s)`; all `#print axioms` standard (subset of
  `propext, Classical.choice, Quot.sound`; decides axiom-free).
- `./lean-bau`: module `Grammatik.X86.RegionSeparation` olean BUILT (step
  393/395); final umbrella step `Grammatik` (394/395) fails with
  `libc++abi: ... failed to create thread` (exit 134) — machine thread
  exhaustion under ~40 concurrent lane builds (74 lean threads observed),
  no Lean error. Retried 4x with backoff; same failure.
- CONTROL EXPERIMENT: stashed my 1-line umbrella change and probed the
  PRISTINE umbrella — identical `failed to create thread` (exit 134).
  The block is content-independent and machine-wide (even untouched master
  cannot link the umbrella right now); small files probe green.
  The change is purely additive (new leaf + 1 import line), touching
  no goal/checker/emitter file, so `gabbro_ziel` axioms are unaffected —
  but the full-build + `gabbro_ziel` axiom re-check could not run in this
  turn for the same environmental reason (PENDING, not claimed; the merge
  script rebuilds `grammatik/` before committing, so master stays gated).

## What remains open
- Full `./lean-bau` green + `#print axioms gabbro_ziel` re-check when the
  machine is quiet (merge gate will re-run both anyway).
- CUTS in file: no source lowering, no freshness from numbers, no loader
  contract, no concurrency/TSO claim, no decoder/ABI/cost/progress claim.
  Consumer: shared-IR validator skeleton (C5 / `valX86_sound`).
- Friend paths untouched; no-go areas (Spec, checker, Rust, emitter,
  Typen/execution/codec) untouched.

## Anything believed wrong in the task
Nothing. The scope (generic checker + soundness + witnesses, correspondence
OPEN) matches exactly what the existing helpers were missing: Regionen had
pairwise facts but no finite-list verdict; Bild had `paarweise` but no
region-vocabulary re-reading; frames existed per-address but not per-verdict.
