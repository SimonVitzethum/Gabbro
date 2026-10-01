# MUSE-REPORT-429: Code-window preservation under disjoint stores

Lane 429, branch `muse/429`, clone `/home/simon/Dokumente/gabbro-muse/a429`.
Task: prove that actual memory writes disjoint from the certified
instruction-byte window preserve the fetched/decode result and code bytes,
from the accepted byte step and memory permissions. No assumption of the
desired code invariant as conclusion; disjoint memory-changing store plus
overlapping-write counterexample; wrap/range correctness; whole-source
self-modifying-code refusal stays separate.

## Starting state

No preserved work existed in the clone (no `MUSE-REPORT-429.md`, no
`CodeImmutability.lean`, clean `git status`). Built the module fresh.

## What was done

NEW file `grammatik/Grammatik/X86/CodeImmutability.lean` (~300 lines),
plus one additive import line in `grammatik/Grammatik.lean`. Reuses the
accepted helpers, duplicates nothing: fetch/decay from `Byteschritt.lean`
(`geholt`, `fetchDekodiert`, `ausfuehrbarN`, `holeFetchAux`), memory from
`Speicher.lean` (`write64`, `write64_rahmen`,
`write64_erhaelt_berechtigungen`, `addrOff`), footprint hit from
`SpeicherKommutation.lean` (`write64_trifft`, new import, no second
register), witnesses from `Byteschritt.lean` (`ketteStart`, `ketteReg`,
`witnessFlags`, `natByte`). No touch of source checker, Spec, goal,
Rust, emitter, Typen, Codec, or the friend-owned optimiser files.

Exact new names:

- `CodeFremd (s : Zustand) (a : Adresse) : Prop` — the 8-byte store
  footprint at `a` is disjoint from the WHOLE possible 15-byte fetch
  range at `rip` (whole cap, so no length bookkeeping in the induction).
- `ausfuehrbarN_nach_schreiben` — execute permission agrees before/after
  a successful `write64` (a store only replaces `bytes`).
- `holeFetchAux_nach_fremd` — the executable-prefix fetch agrees
  before/after a foreign store; induction over the cap.
- `geholt_nach_fremd_schreiben` — FETCH PRESERVED (main).
- `fetchDekodiert_nach_fremd_schreiben` — DECODE PRESERVED (main): the
  checked outcome the byte step runs is unchanged; the decoder is never
  re-trusted.
- `codeBytes_bleiben` — every fetched code byte reads as before.
- `codeFremd_von_intervallen` — RANGE TO FOREIGNNESS: Nat-interval
  disjointness plus explicit no-wrap on both sides gives `CodeFremd`.
- `umbruch_alias` — WRAP ALIASES (`addrOff (2^64-2) 2 = addrOff 0 0`):
  the reason the no-wrap hypotheses are stated, never assumed away.
- `wFremd` — the accepted chain memory at 4096 is foreign to the data
  cell at 8192, through the interval bridge.
- `fremd_schreiben_zeuge` — JOINT WITNESS: real nonzero `write64` at
  8192 reaches, is foreign, preserves `geholt` AND `fetchDekodiert`,
  and observably changes the data byte (0 -> 42).
- `wOverlappSpeicher`, `wOverlappStart` — `ret` byte at 4096 that is
  executable AND writable (model permits; loaded images never do).
- `ueberlapp_nicht_fremd` — the overlapping footprint is provably not
  foreign (byte zero of the window is byte zero of the store).
- `ueberlapp_geaendert_zeuge` — OVERLAP COUNTEREXAMPLE (joint): real
  store onto the code byte reaches, changes the code byte (195 -> 42)
  and changes `geholt`.

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. Every theorem uses
all its premises. `#print axioms` for all 11 names: `propext` and/or
`Quot.sound` only, `umbruch_alias` axiom-free — standard subset, no new
axioms.

## Check results (last lines)

- `./lean-probe grammatik/Grammatik/X86/CodeImmutability.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (module GREEN).
- `./lean-bau` (full project): RED at the final umbrella step, but NOT
  from this lane. Failure: `Building Grammatik [392/393]` crashes with
  `libc++abi: terminating ... failed to create thread`, Lean exit 134.
  No Lean type error anywhere (the only "error" lines are the crash
  report itself). CONTROL: with my `Grammatik.lean` edit stashed
  (module unreferenced), the identical crash recurs at the same step;
  `./lean-probe grammatik/Grammatik.lean` crashes the same way. This is
  a pre-existing environment/threading failure of the whole-project
  check on this machine, independent of this lane.
- `gabbro_ziel` axiom check: not runnable here — it needs the same
  umbrella build that the environment crashes on. Untouched by this
  lane by construction (new X86 module + one import line; the goal
  statement, Spec and checker are not modified).

## What remains open (see CUTS in the file)

- Whole-source self-modifying-code refusal: separate work, not claimed.
- No `byteschritt`-outcome preservation (correctly so: `schritt` may
  read data memory, so a disjoint data store can change the successor
  while the fetch is identical). Only fetch, decode and code bytes.
- No concurrency/coherence claim; sequential over one model `Speicher`.
- Only 64-bit `write64` covered; 1/2/4-byte instances not stated
  (same `writeBytesN` shape, mechanical follow-up).
- Project-level `./lean-bau` green is blocked on the pre-existing
  umbrella thread-creation crash; the merge gate will need a working
  full build to confirm the one-line umbrella import.

## Task feedback

The task is sound as stated: nothing requested turned out to need an
extra premise or a weaker conclusion. The one surprise is environmental
(the umbrella crash above), not in the task. `write64_trifft` already
existed in `SpeicherKommutation.lean` — imported, not duplicated.
