# MUSE-REPORT-41: per-thread mark instances (attempt A of 2)

Lane 41 answers SATZKARTE.md flag B8: `PCMarkSep` (Maschine.lean:1309)
separates static marks across threads, so two threads running the same
function (same `progAus` text) cannot discharge W4 through
`pc_discharge_einfaedig`. A mark occurrence in thread `f`'s text denotes
the instance `(f, m)`: per-thread codes `codeI f m` separate owners even
when the static texts coincide.

## What I did

New file `grammatik/Grammatik/MarkenInstanzA.lean` (wired into
`grammatik/Grammatik.lean`), mirroring the `PCMarkSep` discharge chain at
the instance level:

- §1 defs: `InstanzCode` (`Faden → D.Marke → Nat`), per-owner projection
  `instMarkenProj` / `instEreignisProj` / `instSchrittProj` /
  `laufProjInstanz` (each step through its owner's code), instance
  separation `PCMarkSepInstanz` (each side mapped through its owner's
  code), instance invariant `PCMarkInvInstanz`.
- §2: `PerThreadCode` (equal instance codes come from the same thread) and
  `pcMarkSepInstanz_aus_perThread`: owner-faithful codes separate EVERY
  program text, in particular same-function texts.
- §3: projection facts `laufProjInstanz_get`, `instMarkenProj_mem`,
  `instMarkenProj_marke`, `instMarkenProj_held_absurd` (mirrors of
  `laufProj_get`, `markenProj_mem`, `markenProj_marke`,
  `markenProj_held_absurd` with the owner carried along).
- §4: `pc_discharge_einfaedig_instanz`: the exact W4 conclusion that
  `pc_discharge_einfaedig` gives (`Marken.Einfaedig` over the projected
  run), over `laufProjInstanz`, from `PCMarkInvInstanz` +
  `PCMarkSepInstanz`. Same proof skeleton as the static original; every
  premise fires.
- §5: `pcReach_markInvInstanz` (static `pcReach_markInv` feeds the instance
  invariant) and `pc_discharge_einfaedig_instanz_aus_lauf` (W4 for
  instances in generated `PCReach` runs).
- §6: `progMarks_gleich_fn` (same function, same static text),
  `pcMarkSep_scheitert_gleich_fn` (static separation fails for every
  genuine same-function `progAus` text naming one mark).
- §7: concrete two-thread example `beispiel_zwei_faeden_eine_funktion`:
  `beispielProg m0` (both threads name static mark `m0`) with
  `beispielCode` (`fun f _ => f`): `¬ PCMarkSep code` holds AND
  `PCMarkSepInstanz` holds, in one conjunction.
- CUTS block and `#print axioms` for all 18 theorems.

Theorem list: `pcMarkSepInstanz_aus_perThread`, `instanzText_aus_statik`,
`markInvInstanz_aus_markInv`, `laufProjInstanz_get`,
`instMarkenProj_mem`, `instMarkenProj_marke`,
`instMarkenProj_held_absurd`, `pc_discharge_einfaedig_instanz`,
`pcReach_markInvInstanz`, `pc_discharge_einfaedig_instanz_aus_lauf`,
`progMarks_gleich_fn`, `pcMarkSep_scheitert_gleich_fn`,
`pcMarkSepInstanz_gleich_fn`, `beispielProg_mark`,
`beispiel_statik_scheitert`, `beispielCode_perThread`,
`beispiel_instanz_haelt`, `beispiel_zwei_faeden_eine_funktion`.

## Last `./lean-bau` result line

`Build completed successfully (34 jobs).` with
`== 0 error line(s) in the COMPLETE output`.
All `#print axioms` report only `[propext, Classical.choice, Quot.sound]`
(no `sorry`/`axiom`/`native_decide`/`unsafe` anywhere; no `Prop`-typed
premises; every premise used).

## What remains open

- The example text `beispielProg` is hand-built, not a `progAus`
  extraction of a real body (booked in CUTS; the `progAus` failure shape
  itself is proved generally in §6).
- The example code is the owner identity, not a pairing of tag with static
  base code: this toolchain has no `Nat.pair`/`Nat.unpair`, so no canonical
  pairing family is built.
- No `PCSchritt` firing in the example: it compares the two separations
  over program text; run discharge is the separate §5 theorem.
- Attempt B (lane 42) may take the complementary route (e.g. instance
 -indexed `Marken.Einfaedig` or extraction-side instances).

## What I believe is wrong in the task

Nothing load-bearing. One elaboration note: the task says instances are
"automatically true for two threads running the same function when their
marks are per-thread instances" -- in this formalization that step is
`PerThreadCode`, an explicit code premise, not automatic: the separation
holds for every text only once the code is assumed owner-faithful. The
assumption is about the code function, not about the program, so it does
not reintroduce a per-program text check; but it is a premise, stated as
one. No target statement was weakened: the W4 conclusion is proved
verbatim over the per-owner projection.
