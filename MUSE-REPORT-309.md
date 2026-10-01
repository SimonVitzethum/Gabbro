# MUSE-REPORT-309: Stack frames and ABI memory obligations

Lane 309, branch `muse/309`, model `opencode-go/muse-spark-1.3-contributor`.
Owned files only: `grammatik/Grammatik/X86/Stapel.lean` (new),
one umbrella import line in `grammatik/Grammatik.lean`, this report.

## What was done

New Lean module `Gabbro.Grammatik.X86.Stapel` modelling checked stack-frame
extents/layout, 16-byte call-boundary alignment, fresh/disjoint
spill/callee-save slots and argument/result carriage over the actual
canonical `Speicher` (`Grammatik.X86.Typen` / `Speicher`), using the shared
`write64`/`read64`. No second register, instruction, state or memory model
was created; `schritt` semantics is never duplicated; no Linux-specific
mechanism (stack sizes, guard pages, clone flags, syscall numbers) appears.

- §1 extents/alignment: `Rahmen` (Nat `basis` + `tiefe`, so no-wrap is
  arithmetic, not a wrap hypothesis), `spitzeNat`, `schlitzZahl`,
  `schlitzNat`, `schlitzAddr`, `spitzeWort`, `ausgerichtet16`, `rahmenOk`
  (nonzero depth, depth % 16 == 0, top inside 64 bits, 16-aligned base);
  `schlitzNat_schranke`, `schlitz_toNat`, `spitze_ausgerichtet`.
- §2 single-slot save/restore: `sichereWort`, `ladeWort`;
  `sichere_lade_rundreise`, `sichereWort_ausserhalb` (bounds refusal),
  `sichereWort_verweigert` (permission refusal),
  `sichereWort_erhaelt_berechtigungen`, `sichereWort_rahmen`,
  `ladeWort_rahmen`.
- §3 disjointness: `schlitz_disjunkt` (via `OhneUmbruch` +
  `disjunkt_von_intervallen`), `RahmenGetrennt`,
  `rahmen_getrennt_von_intervallen` (caller/callee Nat-interval separation).
- §4 layout: `Belegung` (spill / callee-save / stack-arg counts), `braucht`,
  `passt`, `gerettetIdx`, `stapelArgIdx` (spills live at bare indices below
  `b.spill`, so no offset function exists for them); `bereich_getrennt`
  (generic non-overlapping index ranges name disjoint slots),
  `spill_gerettet_getrennt`, `gerettet_stapel_getrennt`.
- §5 carriage: `argReg` (System V order `rdi rsi rdx rcx r8 r9`, `none`
  beyond), `argReg_sonde_rdi`, `argReg_sonde_r9`, `argReg_verschieden`
  (all 15 pairs, by `decide`), `argReg_ab_sechs`, `argStapelIdx`,
  `argStapel_schranke`, `sichereErgebnis` / `ladeErgebnis`,
  `sichere_lade_ergebnis_rundreise`, `ergebnis_bleibt_vor_rahmen`
  (caller result slot survives a frame-disjoint save).
- §6 regions: `sichereListe`, `ladeListe`, `sichereListe_leer`,
  `ladeListe_null`, `sichereListe_rahmen_fremd` (region write preserves a
  read it never touches), `sichereListe_ladeListe_rundreise` (whole-region
  round-trip by induction, using slot disjointness for head/tail framing
  and permission preservation for readability).
- §7 witnesses/probes: `rahmenZeuge` (`0x2000`, 32 bytes, 4 slots),
  `speicherZeuge` (zeroed, fully readable/writable), `rahmenZeuge_ok`,
  `rahmenZeuge_ausgerichtet`, `rahmenZeuge_schlitze`, `zeuge_lesbar8`,
  `zeuge_schreibbar8`, `rahmen_schreibLese_zeuge` (nonzero word 42 saves,
  reads back, observably changes the byte), `zeuge_ausserhalb_verweigert`
  (slot 4 of 4 refuses), `rahmen_unaligned_verweigert` (base `0x2001`
  refuses), `zeuge_liste_probe` (`[11, 22]` round-trip through the generic
  region theorem).

No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. Every theorem uses
every premise (bounds, permissions, disjointness and writes are all
consumed; readability is stated separately because read/write permissions
are independent fields, as in `Speicher.lean`). No source-syntax
(`Vertrag`/`Stmt`/...) premises occur, so no joint source/table witness
was required; target helpers carry real memory/operand probes instead.
`#print axioms` for every theorem: at most `[propext, Quot.sound]`, many
with no axioms at all.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (372 jobs)`.
`./lean-probe grammatik/Grammatik/X86/Stapel.lean`: `0 error(s)`.
Umbrella `Grammatik.lean` builds as part of the same green build.

## What remains open (CUTS, also at the file end)

No instruction execution/decoder, no TSO bridge (all facts sequential over
one `Speicher`), no source correspondence (no int-to-pointer anywhere),
no assumed correct caller (every op refuses with `none`), callee-save/entry
contracts and external ABI byte correspondence (which registers survive a
call, what bytes a foreign stub needs), no image/loader/cost/final-image
claims. Helpers are built to be consumed by later execution/IR/ABI proof.

## Task remarks

Nothing in the task looked wrong. Two deliberate choices, both inside the
task: (1) frames are Nat `(basis, tiefe)` with `ofNat` addresses rather
than BitVec subtraction, so no-wrap is arithmetic and every frame fact
states its bound explicitly, matching `Speicher.lean` §3; (2) the six
argument registers are an if-chain `Nat -> Option Register` rather than
`Fin 6 -> Register`, because `Function.Injective` over `Fin 6` has no
`Decidable` instance in this toolchain (no mathlib) while the 15-pair
`decide` statement proves the same distinctness.
