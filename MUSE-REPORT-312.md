# Muse report 312: checked target regions and allocation ceiling

## What was done

New file `grammatik/Grammatik/X86/Regionen.lean` (namespace
`Gabbro.Grammatik.X86`), built only over the canonical
`Typen`/`Speicher` vocabulary (no second word/memory model, no
source/Spec/goal edit):

- Region handles with declared extents/rights: `Region`
  (`basis/len/lesbar/schreibbar/ausfuehrbar`), finite supplied range
  `Vorrat` (`lo/umfang`), checked containment `innerhalb` (inside the
  range, `basis + len ≤ 2 ^ 64`), `regionDisjunkt`, alignment rounding
  `ausricht` (zero alignment refuses via `none`).
- Deterministic checked bump allocator `reserviere` over the supplied
  range: refuses empty (`len = 0`) and unaligned requests, aligns the
  cursor, refuses over-ceiling/wrapping requests with `none`
  (refuse-on-full), else hands a fresh capability and advances
  deterministically. Proved: extent/rights carried
  (`reserviere_ausmass`), containment (`reserviere_innerhalb`), ceiling
  (`reserviere_decke`: cursor monotone, never past `lo + umfang` or
  `2 ^ 64`), freshness (`reserviere_frisch`), over-ceiling refusal
  (`reserviere_voll_verweigert`), freshness-disjointness against all
  regions below the old cursor (`reserviere_disjunkt_unten`) and cursor
  invariant preservation (`reserviere_haelt_unten`, `alleUnten`).
- Canonical `Speicher` initialisation `initialisiere`: zeroes the extent
  bytes and installs the declared rights, touching nothing else.
  Proved: byte/permission frames outside the extent, declared rights
  and zero bytes inside, plus the bridge to the canonical checks:
  `initialisiere_schreibbar8`/`initialisiere_lesbar8` (an eight-byte
  region with the right answers `schreibbar8`/`lesbar8` through the
  shared checks, via `natAdresse_addrs`).
- Opt-in ceiling-free model `FreiStand`/`freiReserviere` (no `Vorrat`,
  only the physical `≤ 2 ^ 64` check; external `scheitert` flag models
  the runtime/OS answer point): still refuses (`freiReserviere_kann_scheitern`,
  `freiReserviere_leer_verweigert`) and provably loses the static bound
  below the physical width (`freiReserviere_ohne_statik_gebunden`: every
  `B < 2 ^ 64` is exceeded by some success). No physical
  unbounded-address claim: every extent still satisfies
  `basis + len ≤ 2 ^ 64`.
- Real probes (all `decide`): `zeugenReserviere_erfolg` (8 bytes handed
  at `0x10000`, cursor to `65544`), `zeugenReserviere_voll` (8 KiB
  against a 4 KiB range refused), `zeugenSchreibschutz_verweigert`
  (read-only region answers no write permission), and the joint
  memory-changing witness `region_schreibLese_zeuge` (nonzero `write64`
  into the initialised region reads back through `read64` and changes
  the byte from 0 to 42).

One umbrella import line added at the end of `grammatik/Grammatik.lean`
(`import Grammatik.X86.Regionen`). No other file touched.

## Exact names

Definitions: `Region`, `Vorrat`, `regionEnde`, `vorratEnde`,
`innerhalb`, `ausgerichtet`, `regionDisjunkt`, `ausricht`,
`Reservierer`, `reserviere`, `natAdresse`, `inRegion`,
`initialisiere`, `alleUnten`, `FreiStand`, `freiReserviere`,
`zeugenVorrat`, `zeugenStart`, `zeugenRegion`, `zeugenSpeicherR`.
Theorems: `ausricht_monoton`, `ausricht_eins`,
`ausricht_null_verweigert`, `reserviere_leer_verweigert`,
`reserviere_ausr_null_verweigert`, `reserviere_ausmass`,
`reserviere_innerhalb`, `reserviere_decke`, `reserviere_frisch`,
`reserviere_voll_verweigert`, `initialisiere_rahmen_bytes`,
`initialisiere_rahmen_rechte`, `initialisiere_ausmass_rechte`,
`initialisiere_ausmass_null`, `alleUnten_leer`,
`reserviere_disjunkt_unten`, `reserviere_haelt_unten`,
`reserviere_belegt`, `reserviere_haelt_alleUnten`,
`natAdresse_addrs`, `inRegion_natAdresse`,
`initialisiere_schreibbar8`, `initialisiere_lesbar8`,
`freiReserviere_kann_scheitern`, `freiReserviere_leer_verweigert`,
`freiReserviere_ausmass`, `freiReserviere_ohne_statik_gebunden`,
`zeugenReserviere_erfolg`, `zeugenReserviere_voll`,
`zeugenSchreibschutz_verweigert`, `region_schreibLese_zeuge`.

## Repair pass after independent review 316 (VERDICT: REPAIR)

Both required findings resolved without weakening any guarantee:

- F1 (unused `_hq` premise in `reserviere_disjunkt_unten`, HARD RULE 3):
  applied the preferred variant. The theorem now takes
  `(hinv : alleUnten s) (q : Region) (hq : q ∈ s.belegt)` and derives
  `hunter := hinv q hq` in the proof; every premise is used
  (`h` via `reserviere_frisch`/`reserviere_ausmass`, `hinv`/`hq` via
  `hunter`, all others in the calls and the goal). The statement is now
  about tracked regions and is otherwise unchanged.
- F2 (`reserviere_haelt_unten` covered old entries only): added the
  corollary `reserviere_haelt_alleUnten : alleUnten s'` (new region ends
  exactly at the new cursor via `reserviere_frisch`, old entries below
  it via `reserviere_haelt_unten`), plus the small helper
  `reserviere_belegt` (`s'.belegt = r :: s.belegt`). The report's
  "cursor invariant preservation" claim now matches a proved theorem
  exactly.

No assumption invented, no source/binary chain claimed, CUTS unchanged
(both fixes are inside the already-claimed allocator scope).

## Last build result

`./lean-bau`: `Build completed successfully (372 jobs).`
`./lean-probe grammatik/Grammatik/X86/Regionen.lean`: 0 errors; every
`#print axioms` is standard (no axioms at all, or a subset of
`propext, Classical.choice, Quot.sound`). No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`; every premise is used.

## What remains open (see file CUTS)

Source dynamic-region/allocator-template correspondence; any
`Zielsatz/Spec` coverage; runtime/OS allocation contracts (user logic,
with the `scheitert` flag as the answer point only); TSO/concurrency
refinement of disjointness; `Bild`/loader/entry/relocation
integration; decoder/ABI/cost/final-image acceptance. The ceiling-free
model loses the static bound below `2 ^ 64` only.

## Task fidelity note

Nothing in the task was weakened: all requested properties
(fresh/disjoint/frame/extent/ceiling/refusal, nonzero
memory-changing success/failure witnesses, failure-allowing
ceiling-free model with explicit static-bound loss, no
number-to-pointer casts, no new word/memory model) are proved above.
No INHABITATION `_zeuge` companion was needed: no theorem quantifies
universally over source syntax (`Vertrag`/`Stmt`/`Endblock`/
`ErgExpr`/`Expr`/`Args`); target helpers carry real memory/operand
probes (`decide` facts plus `region_schreibLese_zeuge`) instead.
