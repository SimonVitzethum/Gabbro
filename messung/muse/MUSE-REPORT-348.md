# MUSE-REPORT-348: Reviewed organisation plan C4 — EntryState

Lane 348, branch `muse/348`, reviewer 386.
Delivers the IMAGE-ABI section 5 entry predicates as checked validator
admission `Bool`s over the canonical vocabularies. No claim beyond what
is proved below; full final-byte/source/hardware correspondence stays OPEN.

## Owned paths (and nothing else)

- NEW `grammatik/Grammatik/X86/EntryState.lean` (551 lines)
- One additive import at END of `grammatik/Grammatik.lean`
- This report `MUSE-REPORT-348.md`

`git status` before commit shows exactly these three paths. No source,
checker, Spec, goal, central canonical, Rust, emitter, docs or friend
path was touched.

## Sources read (no behaviour invented)

- `dokumente/x86/WORK-ALLOCATION.md` row C4, `grammatik/OPTIMIZER.md`,
  `DIRECT-COMPILER-DESIGN.md`, `dokumente/x86/BYTE-PILOT.md`,
  `dokumente/x86/IMAGE-ABI.md` sections 5/8/11
- Actual definitions in `Grammatik/X86/Typen.lean` (`Zustand`), `Speicher.lean`
  (`lesbar8`/`schreibbar8`/`read64`/`write64`/`writeBytes`/`writeBytesN_hit`/
  `addrOff_null`/`read64_nach_write64`), `Bild.lean` (`Bild`/`Profil`/
  `wohlgeformt`/`eintragEnthalten`/`ladenAusfuehrbar`/`ladenLesbar`/
  `ladenSchreibbar`/`zeugenBild`), `Stapel.lean` (`ausgerichtet16`),
  `Gleitprofil.lean` (`MXCSR`/`mxcsrGueltig`)
- No second IR, no second evaluator, no renamed correctness premises.
  No `schritt` duplication (no new instruction semantics at all).

## What was built

`EintrittArt` (8 kinds: `hostedMain`, `nolibcMain`, `modulInit`,
`modulExit`, `metallStart`, `fadenWurzel`, `klonKind`, `trapRueck`),
`EintrittZustand` (canonical `Zustand` + `MXCSR` + `xmmBeruehrt` +
`mxcsrGesichert` + `ifBit` + `guardOk`), `ifErwartet`, `guardErforderlich`,
`eintrittRsp`, `stapelOk` (canonical `ausgerichtet16`), `mxcsrOk`,
`ifOk`, `guardOk`, `schutzSeiteOk` (single-probe guard check),
`stapelRW` (one word below top, `lesbar8`+`schreibbar8`),
`eintragGelisted`, `eintrittOk` (well-formed image + listed entry +
loaded executable byte at RIP + aligned RW stack + guard + MXCSR + IF),
`externZielOk` (listed entry in executable section only), `trapRueckOk`
(validated-bytes flag + IF + MXCSR), `KernAntwort` (named-only kernel
behaviour: `kindLauf`/`unbekannt`, nothing derived).

Witness memory `zeugenSpeicherE` = loaded `zeugenBild` permissions plus
a readable/writable stack window `[0x7000, 0x8000)` (stack never
executable); `zeugenStapelTop` = `0x8000`, `zeugenStapelBasis` = top-8,
`zeugenWache` = `0x6000` (unmapped probe).

## Theorems (every premise used; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`)

Acceptance on the concrete loaded image prefix:

- `zeugenEintrittHosted_ok`, `zeugenEintrittFaden_ok`,
  `zeugenEintrittNolibc_ok`, `zeugenEintrittModul_ok`,
  `zeugenEintrittModulExit_ok`, `zeugenEintrittMetall_ok`,
  `zeugenEintrittKlon_ok`, `zeugenTrapRueck_ok` — all by `decide`
- `zeugenStapel_lesbar`, `zeugenStapel_schreibbar`, `zeugenWache_ok`
- `eintritt_zeuge` — JOINT WITNESS: accepted entry AND a nonzero stack
  write (`write64` 42 at `zeugenStapelBasis`) that reads back via
  `read64_nach_write64` and observably changes the byte (via
  `writeBytesN_hit` + `addrOff_null`), reusing the shared byte memory ops

Generic discipline lemmas (premises all used):

- `mxcsr_verweigert_ohne_sicherung`, `guard_verweigert_ohne_seite`,
  `if_verweigert_bei_abweichung`, `eintritt_verweigert_mxcsr`,
  `eintritt_verweigert_guard`, `eintritt_verweigert_if`,
  `eintritt_verweigert_stapel`, `eintritt_verweigert_unlisted`,
  `trapRueck_verweigert_ohne_bytes`, `externZiel_verweigert_unlisted`

Concrete refusals (all by `decide`, i.e. proved, not merely written):

- `zeugenXmm_verweigert` (XMM touched, no save)
- `zeugenGuard_verweigert` (thread root, guard missing)
- `zeugenExtern_verweigert` (`externZielOk zeugenBild 0 0x5000 = false`)
- `zeugenTrapManifest_verweigert` (manifest row, no validated bytes)
- `zeugenIF_verweigert` (hosted entry, IF clear)
- `zeugenStapelSchief_verweigert` (RSP `0x8001`)
- `zeugenRipFremd_verweigert` (RIP `0x5000`, unlisted)

## Verification

- `./lean-probe` after every increment: final `0 error(s)`.
- Full `./lean-bau`: `exit 0`, `0 error line(s)`, `Build completed
  successfully (386 jobs)`, last line `Built Grammatik (1.4s)`.
- Axiom probe: `gabbro_ziel` still depends on exactly
  `[propext, Classical.choice, Quot.sound]` (checked via a scratch
  `#print axioms` run from `grammatik/`, scratch file removed).
- Own-file axioms: every main theorem depends at most on
  `[propext]` (several on nothing); `eintritt_zeuge` on
  `[propext, Quot.sound]` (inherited from the shared byte-memory
  lemmas, same as the `Bild`/`Stapel` witnesses). No new axiom.

## What remains OPEN (also in the file's CUTS block)

Guard is a single probe (no 4096-byte sweep); stack covers one word
below top (no whole-frame/red-zone/per-CPU model); save/guard/bytes
flags are validator findings, not validated byte sequences; XMM file
unmodelled; kernel behaviour named only; no decoder, no indirect-target
certificates, no source correspondence, no TSO bridge, no cost/budget
transfer, no final-byte closure. Refusals are predicate-level admission,
never hardware faults; 16-alignment is the declared call-boundary
contract only, unaligned ordinary accesses are not modelled as faults.
Shared-IR consumer (lane 287) pending; no substitute invented.

## Notes on the task (nothing believed wrong)

- The lane direction names a `_zeuge` for target theorems; since this
  module quantifies over no source syntax (`Vertrag`/`Stmt`/…), the
  strict HARD-RULE-13 trigger does not fire, but `eintritt_zeuge` is
  still provided as the joint non-degenerate witness the safety
  corrections demand (accepted entry + real memory-changing write/read).
- `trapRueck_verweigert_ohne_bytes` binds its `Bool` subject explicitly;
  no auto-bound implicits, no `Prop`-typed premise anywhere.
- No semantic mismatch found in plan symbols: `Bild`, `Modus`,
  `eintraege`, `ausgerichtet16` all resolve to the actual definitions
  and are reused, not redefined.
