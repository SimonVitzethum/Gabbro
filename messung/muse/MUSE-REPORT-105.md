# MUSE-REPORT-105 (lane 105, D9: stability without invariant form)

## What was done

New file `grammatik/Grammatik/StabilBewacht.lean` (imported at the end of
`grammatik/Grammatik.lean`), closing the D9 non-invariant fragment with the
standard rely/guarantee argument at chain grain.

**Main theorems:**

- `stabil_ohne_form` — the TARGET, proved in exactly the tasked shape
  (only elaboration detail: the `g = f` case goes through `heq ▸ hg`
  instead of `subst`, since `subst` eliminates the fixed thread).
  Induction on the chain index: head validity (`hKopf`), own steps
  (`hEigen`), foreign steps (`hStabil`, one direction only). No invariant
  form, no `HaengtAb`, no discipline — pure chain folding.
- `stabil_aus_bewachung` — the corollary connecting `hStabil` to the
  checker. Premises: slot-level dependence `hDep` (read-set `Sf`,
  global frame `Gf`); static guarantee `hWacheT`/`hWacheG` (every foreign
  write to a carrier `Q f` reads happens only under a guard both threads
  hold — `Bewacht` / `TraegerSchreibt` / `D.haelt`); per-step rely
  `hRelyT`/`hRelyG` (guarded foreign writes leave `Q f`'s slots alone —
  memory-level, checker-comparable). Proof: per slot, either the writer
  never touches the table (chain frame `hSchritt` agrees) or the guard
  fires and the rely agrees; the assembled agreement feeds `hDep`.
- `haengtAb_aus_slotDep` — companion: slot dependence plus footprint
  coverage give table-level `HaengtAb` (the shape downstream
  `InterferenceFree` machinery consumes).

**Witnesses (rule 13, both on the reference fixture `refD`):**

- Two-thread chain `zbJ` (`NbW`: both threads declared; `codeW`: thread 0
  runs `lies`, thread 1 runs `einzahlen`; worlds `[zbW0, zbW1]`;
  `schrittFaden = [1]`; empty run): the single step writes only slot 5
  (`0 → 7`). `Q` (`zbQ`: `slot 0 = slot 1`, "my slot equals my local
  counter") reads slots 0 and 1 — not a whole-table invariant, yet stable
  here because the foreign write goes elsewhere under the co-held guard.
- `stabil_ohne_form_zeuge` — `hKopf`/`hEigen`/`hStabil` proved jointly
  (`zbKopf`, `zbEigen`, `zbStabil`) plus non-degeneracy (`zbSchreibt`:
  `einzahlen` writes `konto`; `zbMemMoved`: slot 5 `0 → 7`).
- `stabil_aus_bewachung_zeuge` — `hDep`/`hWacheT`/`hWacheG`/`hRelyT`/
  `hRelyG` proved jointly (`zbDep`, `zbWacheT`, `zbWacheG`, `zbRelyT`,
  `zbRelyG`) plus the derived `HaengtAb` leg (uses `zbCover`) and the same
  non-degeneracy facts.

Supporting definitions/lemmas: `zbV0`, `zbV7`, `zbW0`, `zbW1`, `zbWE`,
`zbNb`, `zbCode`, `zbEintritt`, `zbQ`, `zbSf`, `zbGf`, `zbWf`,
`zbWE_haelt`, `zbSchritt_rahmen`, `zbJ`, `zbJ_welten`, `zbJ_schritt`,
`zbJ_faeden`, `zbQ_W0`, `zbQ_W1`, `zbHaelt`, `zbSchreibtEin`,
`zbSchreibtLies`, `zbW1_slot5`, `zbW0_slot5`, `zbMemMoved`, `zbSchreibt`,
`zbCover`.

## Last `./lean-bau` result line

`Build completed successfully (54 jobs).` — all five theorems
(`stabil_ohne_form`, `stabil_aus_bewachung`, `haengtAb_aus_slotDep`,
both `_zeuge`) depend only on `[propext, Classical.choice,
Quot.sound]`; `./lean-probe` reports 0 errors, no warnings.

## What remains open (also booked as CUTS in the file)

- S1 (finding): table-level `HaengtAb` alone is PROVABLY insufficient for
  `hStabil` — a foreign write to another slot of the same table breaks
  table-level frame agreement while preserving `Q`. The slot read-set and
  slot-level premises are the unavoidable extra; table `HaengtAb` is
  derived, not assumed.
- S2: no mutual exclusion is derived — the rely arrives per step
  (`LesenStabil` L1 carries over). The theorem removes assertion-level
  per-step reasoning, not memory-level per-step facts.
- S3/S4: one direction only; `hEigen` still assumed (G7, another lane).
- S5: non-invariant-form of the witness `Q` documented by shape, not
  proved as a negation over all `TraegerInv`.

## What I believe is wrong (or underspecified) in the task

1. "hStabil holds automatically" overstates what the guard story alone
   delivers: without slot information (or equivalent per-step memory
   facts) the conclusion does not follow — see S1. The corollary as built
   makes the exact boundary explicit instead of pretending.
2. The witness spec ("other thread writes only a different slot") forces
   slot granularity, which table-level `HaengtAb`/`TraegerSchreibt` cannot
   express — hence the `Sf` read-set. This is consistent with the spec but
   means the corollary's dependence premise is slot-level, with `HaengtAb`
   derived alongside.
3. Witness premise-proofs discharge by computation on concrete worlds, so
   some carried hypotheses (the `Q`-assumptions, disequalities, slot
   indices) contribute no proof step; they are named, never `intro _`'d,
   and the shapes match the theorems exactly — that is what the witness
   checks.
