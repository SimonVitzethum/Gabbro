# MUSE-REPORT-310: Call-log obligations for source inlining

Lane 310, branch `muse/310`, model opencode-go/muse-spark-1.3-contributor.
Owned files only: `grammatik/Grammatik/X86/AufrufOpt.lean`,
one umbrella import line in `grammatik/Grammatik.lean`,
this report. No Rust, no source/Spec/goal changes, no counters/MARKE.

## What was done

Formalised the ghost-event correspondence obligation for selective
inlining (IR-VALIDIERUNG.md §3.4) over the REAL source model -- machine-G
call logs (`RufEreignisF` with actual rho/v/s0/s1), `rufAt`,
`RufSchrittG`, order `FolgeLog` -- with no fake IR and no new syntax.
A full executable body-splice rewrite was NOT attempted: without the
phase-B source-to-SCFG lowering there is nothing to splice into, so per
the task I defined checked reconstruction and pinned exactly what
remains (see CUTS in the file).

New definitions (namespace `Gabbro.Grammatik.X86`):

- `GeistAntwort D g` -- ghost answer: `ok v s1` | `grund r s1`.
- `geistPaar g rho s0 : GeistAntwort D g -> List (RufEreignisF D)` --
  the pair to re-emit, newest first (return over entry).
- `InlinePflicht P caller g Lambda` -- the inline obligation as checked
  data: `hp : RufPasst` (lock/resource discipline, carried not weakened),
  `hr : gruende = 0`, actual `rho/s0/s1/val`, `vorOk` (requires over
  actual args at entry), `nachOk` (ensures over actual result, `rufAt`
  shapes).

New theorems, all generic over arbitrary `D`:

- `geistPaar_laenge` -- the pair has exactly 2 events.
- `geistRekon_folge` -- splicing the value-channel ghost pair over a
  physical log preserves `FolgeLog` under the computed armed side
  conditions. No trace equality assumed: premises are `Pflichtig` /
  `Armiert` Bools and the physical `FolgeLog`.
- `geistRekon_folge_grund` -- same for the reason channel.
- `rufSchrittG_logSchritt` -- EVERY `RufSchrittG` constructor leaves the
  acting thread log unchanged or pushes exactly one `eintritt` /
  `rueck` / `grund` event with actual values (case analysis over the real
  step relation; silent unfold/leaf steps need no ghost data).
- `rufAt_ok_vorOk` -- a successful `rufAt` outcome carries true
  `requires` over the actual arguments (the ghost-entry check).
- `geistRekon_zeuge` -- joint witness on `eP` (writes table `konto`):
  reached 5-step run, `konto[0]` 0 at start / 5 at `pruefe` entry, real
  logged pair equals `geistPaar`, `Pflichtig`/`Armiert` true by `rfl`,
  `FolgeLog` by `folgeG_erreichbar`.

## Build results

- `./lean-probe grammatik/Grammatik/X86/AufrufOpt.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (372 jobs).`
- Axioms: `geistPaar_laenge`, `geistRekon_folge`,
  `geistRekon_folge_grund`: `[propext]`; `rufSchrittG_logSchritt`,
  `rufAt_ok_vorOk`, `geistRekon_zeuge`:
  `[propext, Classical.choice, Quot.sound]` (standard goal set).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the file.

## Open (CUTS in file)

1. No body-splice simulation (needs phase-B QUELLBRUECKE lowering).
2. `nachOk` extraction from `rufAt` not proved (only entry half).
3. `hp` carried, not discharged against caller writes/lock floor.
4. No indirect-call (`callInd`) ghost form.
5. Bounds/depth/budget timing untouched (separate obligations).
6. No SCFG/target bridge (source-side only by design).

## Task assessment

Nothing in the task appears wrong. The fallback it names (checked
reconstruction when no full rewrite is provable) is what was delivered;
the "useful generic reconstruction lemma" requirement is met by
`rufSchrittG_logSchritt` (tied to actual steps) plus the two
`geistRekon_folge` lemmas (tied to actual log shapes), jointly
inhabited by `geistRekon_zeuge`.
