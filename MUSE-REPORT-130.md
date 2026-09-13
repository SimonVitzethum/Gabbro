# MUSE-REPORT-130: data-race freedom on the call machine G

## What was done

New file `grammatik/Grammatik/RennfreiG.lean` (registered in
`grammatik/Grammatik.lean`), proving data-race freedom on machine G in
holder-plus-exclusivity form. The proof reuses the merged one-step rely
instead of a 70-constructor case analysis.

New definitions/theorems (all in `Gabbro.Grammatik`):

- `zugriffVon (e : Ereignis D) : Option ((D.Tab ⊕ D.Glob) × Bool)` --
  one event as a (carrier, is-write) access.
- `zugriffe (M M' : RufMaschineG D) (f : Faden) : List ((D.Tab ⊕ D.Glob) × Bool)` --
  the access set of one step, from the events the step prepended to the
  thread's trace (trace delta, newest first). Choice documented in the
  file header: access set from the trace; the race CLAIM from the step's
  memory footprint (`TraegerGleich`), which is what `schritt_traeger`
  makes provable.
- `zugriffe_anders` -- a step of `f` records nothing on other threads
  (`zugriffe M M' g = []` for `g ≠ f`); uses both premises.
- `SchreibRasse (M M' M'' : RufMaschineG D) (f g : Faden) (c : D.Tab ⊕ D.Glob)` --
  adjacent double write by different threads to one carrier that has a
  guard lock and is neither atomic (`AtomarAusgenommen`) nor a published
  payload (`PaarungAusgenommen`); the lock-free disciplines are excluded
  by their declared discipline `D.atomar` / `D.nutzlast`.
- `rennfrei_g` (TARGET): on every run reachable from `RufStartG P sp init`,
  a step changing a guarded carrier `c` holds every guard of `c` before
  the step (contrapositive of `schritt_traeger`) and excludes every other
  thread from that guard after the step (`exklusivG` over untouched other
  threads). Premises: `GutO`, `StartExklusiv`, reachability, the step, the
  guard fact, the memory change -- each used by the proof.
- `rennfrei_g_nah`: no `SchreibRasse` on reachable adjacent steps (two
  applications of `rennfrei_g`).
- `hBz`: `konto` of `zD` is watched by the one lock.
- `rennfrei_g_zeuge` (ZEUGE): joint instantiation of ALL `rennfrei_g`
  premises on `zP`/`zO`/`zSp`/`zInit` -- reached `M7`, writing step `s8`
  (thread 1, `konto[0] := 100`, memory `0 -> 100`), guard fact, memory
  change, plus the concluded holder facts. Non-degenerate: table `konto`
  written by `einzahlen`, memory-changing reached step.

Axioms: all three main theorems depend only on
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Last `./lean-bau` result line

`Build completed successfully (75 jobs).` with
`== 0 error line(s) in the COMPLETE output`.

## What remains open (also in the file's CUTS block)

- Actor-side `zugriffe` characterization per rule (only `zugriffe_anders`
  proved); a read/write formulation over `zugriffe` membership; explicit
  release events for non-adjacent races.
- Unguarded carriers are classified, not covered: atomic/published are
  allowed races by design (excluded in `SchreibRasse`); unshared carriers
  stay checker duty (`PCUnsharedSep`, SATZKARTE D2) plus the `W5` leg.

## Task remarks

- Nothing in the task was wrong. One scoping decision worth recording:
  the "accessor holds every guard at each step" form is proved only for
  steps that CHANGE the carrier (via `schritt_traeger`), not for pure
  reads -- reads record `lese` events without a `darf` obligation, so a
  read-side holder claim would be false in general. The race is therefore
  stated over writes (each changing memory), which is also what the rely
  protects.
- `rennfrei_g_nah` does not need the atomic/published exclusion conjuncts
  in its proof (the guarded double write is already impossible); they are
  kept in `SchreibRasse` because the task requires the exclusion to be
  explicit in the race definition.
