# MUSE-REPORT-427: Canonical register reads/writes + fail-closed interference certificates

Lane 427 (continuous Lean proof reserve: RegisterInterference).
Clone `/home/simon/Dokumente/gabbro-muse/a427`, branch `muse/427` — verified.

## What was done

Built `grammatik/Grammatik/X86/RegisterInterference.lean` (428 lines, new module;
one additive import `Grammatik.X86.RegisterInterference` at the end of
`grammatik/Grammatik.lean`, already present from the skeleton commit) over the
canonical `Befehl`/`Zustand`/`schritt` vocabulary only (`Typen`, `Ausfuehrung`,
`Zugriffe`). No second IR, no inferred liveness, no new executor.

1. **Canonical register reads/writes (§1):** `regLiest`, `regSchreibt` for all
   14 pilot constructors (stack/control forms read/write `rsp`; `cmp`/jumps
   write none), each with a per-form equation theorem (`reg_movImm64` … `reg_ret`).
2. **Fail-closed certificate check (§2):** `Wert := Nat` (declared-live ids),
   `RegBelegung := Wert → Option Register`, `reserviertReg` (`rsp` only),
   `kanteOk` / `bindungOk` / `lebtOk` / `belegungOk`. Anything missing or
   conflicting is `false`.
3. **Refusal + positive probes (§3, all `decide`):** empty assignment, conflicting
   edge, `rsp` allocation and broken binding refuse; one distinct-register
   assignment with kept binding passes (`belegungOk_positiv`).
4. **Check-implies facts (§4):** `belegungOk_kante_verschieden` (distinct registers
   with both witnesses), `belegungOk_lebt_zugeteilt`, `belegungOk_ohne_reserviert`
   (never `rsp`), `belegungOk_bindung_haelt`, via three `_alle` conjunct helpers.
5. **Allocator-consumer preservation (§5):** `regSet_vert_kommutiert`,
   headline `belegung_schreibt_ohne_clobber` (passing check + declared edge ⇒
   writing one slot through the actual `regSet` preserves the other register),
   `schrittRegister_erhaelt_fremd`, `reg_schritt_schreibt_nur` (a `movImm64`
   step clobbers exactly `regSchreibt`), `reserviert_rsp` / `nicht_reserviert_rax`.
6. **Joint execution witness (§6):** `belegung_zeuge_null/eins` tie the positively
   checked assignment to `rax`/`rcx`; `probe_belegung_unabhaengig` runs two real
   `schritt` steps (`rax:=7`, `rcx:=9`) and observes both values intact.

## Verification

- `./lean-probe grammatik/Grammatik/X86/RegisterInterference.lean`:
  `0 error(s)`, exit 0.
- `./lean-bau`: green — `Build completed successfully (393 jobs)`, including
  the umbrella `Grammatik` re-export (final line `✔ [392/393] Built Grammatik`).
  (During the session the umbrella step transiently crashed several times with
  `failed to create thread`, exit 134 — machine thread/resource exhaustion also
  hitting other lanes and the main checkout at the same time. A clean-tree
  control build (Lean changes reverted) crashed identically, proving it was
  environmental; after recovery the unchanged work built green. Work restored
  byte-identical, md5-verified.)
- `#print axioms`: every main theorem depends only on `[propext]` or
  `[propext, Quot.sound]` (subset of the `gabbro_ziel` standard set); three
  helpers depend on nothing. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
  every premise is used; no `Prop`-typed premises; no syntax quantification
  (hence no `_zeuge` obligation under the inhabitation rule — concrete
  positive/negative `decide` witnesses are given anyway).
- Name collision found and fixed: `Stapel.Belegung` (spill-frame layout) already
  owns `Belegung`; this module's assignment type is `RegBelegung`, documented
  at its definition.

## Open / CUTS (also at the file end)

- Only the 14 pilot constructors are covered; narrower widths, RMW/LOCK/fence
  forms and future instructions are refused by absence.
- Liveness/edges/bindings are DECLARED inputs. The future accepted IR must supply
  `lebendig`/`kanten`/`bindung` per program point; validating the liveness itself
  is not proved here. Actual source allocation refinement stays OPEN.
- Only `rsp` is pinned; a future ABI must extend the pinned set, never shrink it.
- No source lowering, simulation, cost, contract, timing, concurrency (W/GX),
  TSO bridge or whole-image claim.

## Task fidelity note

Nothing in the task was weakened; the one thing narrower than the headline is
stated in CUTS (liveness is checked, not validated). No mini-machine, no
correctness assumption, no new IR.
