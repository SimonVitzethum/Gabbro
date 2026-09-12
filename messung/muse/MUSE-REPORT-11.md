# MUSE-REPORT-11: Chain from the run for several threads (attempt C)

## What was done

New file `grammatik/Grammatik/KetteMehrfadenC.lean` (wired into
`grammatik/Grammatik.lean`), proving the two-thread case of the lane-11
task: a joint run constructed from a `PCReach` run, with the
`ziel_nutzer_last_aus_pc_Q` premises `hJw : J.welten = M.welten` and
`hJsf : J.schrittFaden = tr` derived as theorems, never assumed.

New definitions:
- `LockSchrittGedecktBei prog M pc f0 M' pc'` — one lock machine step
  (`nimmt`/`gibt`, never `leaf`) with successor equations, actor-explicit.
- `LockSchrittGedeckt prog M pc mem M' pc'` — same, actor in `mem`.
- `KettenSpurDeckung P O passes prog sp Nb code mem` — the exact extra
  premise the N-thread case needs: at every reachable prefix machine with
  its thread trace, some chain tracks worlds, run, and step threads.

New theorems (all green, see axioms below):
- `kette_zwei_start` — two-thread seed over `GenStart sp` (worlds/run by
  construction, `faeden = [f, g]`, code identity).
- `zwei_lauf_mitgliedschaft` — counter routing from program texts: with
  `hforeign : ∀ g0 ≠ f, ≠ g → prog g0 = []`, every reachable run step is
  `f`'s or `g`'s (induction over `PCReach`; foreign actors die at `hpc`
  against the empty text).
- `kette_zwei_schritt` — one threading step for either member along a
  lock step. Frame by `rfl` (lock worlds keep `M.speicher`); `Gesittet`
  from read-only `pc_gesittet` (W4 via `PCMarkSep`, W5 via
  `PCUnsharedSep`); `BeschraenkteVerschraenkung` from the `Nb` pair legs
  plus run membership routed through the chain run (`hJl` used).
- `kette_zwei_aus_lauf` — whole-run induction over `PCSpur` for lock-only
  two-thread programs (`hforeign` + `hlock_prog`). Concludes
  `J.welten = M.welten`, `J.l = M.lauf`, `J.faeden = [f, g]`,
  `J.code = code`, and `J.schrittFaden = tr` for the run's trace.
- `kette_aus_deckung` — the N-thread conclusion follows from
  `KettenSpurDeckung` alone by direct application (names the general-case
  premise exactly).
- `deckung_strikt_schwaecher` — rule-4a certificate: the two-thread seed
  satisfies the deckung shape while breaking both equations on nonempty
  runs, so the premise is strictly weaker than `hJw`/`hJsf`, not a rename.

## Last `./lean-bau` result line

`Build completed successfully (30 jobs).` — including
`[28/30] Built Grammatik.KetteMehrfadenC` and `[29/30] Built Grammatik`.
`#print axioms` for all six theorems: only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## What remains open (see `CUTS:` in the file)

1. `blatt` steps for either thread (needs `blatt_rahmen_schritt` frame +
   per-step contract-to-code wiring); hence `hlock_prog` restricts to
   lock atoms.
2. No `SerialLink` witnesses yet (worlds/run/members/trace only).
3. N-thread discharge of `KettenSpurDeckung` beyond two lock-only threads.
4. The strictness certificate shows the seed breaking both equations while
   a different chain discharges the deckung; it does not exhibit one chain
   doing both at the same machine (existential-weakness direction only).

## What I believe is wrong in the task (or worth flagging)

- Nothing wrong with the task itself, but one methodological trap cost
  real time: `./lean-probe` pipes output through `tail -60`, which hid all
  errors above the cutoff for a long file. I diagnosed a "bullet that
  never runs" for ~30 minutes before realizing the bullet-2 errors were
  cut off. Recommendation: probe with the slot wrapper directly
  (`lake env lean $F | grep error`) when a file exceeds ~60 output lines.
- The `refine ⟨struct, rfl, rfl, by rw [hJsf], …⟩` motive failure: `rw`
  inside an anonymous-constructor component rewrote inside the already
  elaborated structure term. `congrArg (· ++ [f0]) hJsf` avoids it.
- `subst hgf` with `hgf : g0 = f` eliminates the theorem parameter `f`
  from context; carrying the equation and rewriting targeted hypotheses
  is the robust form.
