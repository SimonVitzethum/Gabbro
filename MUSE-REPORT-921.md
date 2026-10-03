# MUSE-REPORT-921 — Exact review of author 771 (16-byte call alignment)

Lane 921, clone `/home/simon/Dokumente/gabbro-muse/a921`, branch `muse/921`.
Owned file only: this report. No source, no live controls touched.

CANDIDATE: 771 f225b5a5bb42984f396f8ccf310f0a6047b8857a

VERDICT: ACCEPT (bounded; see §5 limits)

## 1. What was reviewed

Exact pinned snapshot from `.tmp/review/`: base `56537272a31df3de5d9b7898bbade91c3de817b8`,
three files (`MUSE-REPORT-771.md`, `grammatik/Grammatik.lean` one import line,
`grammatik/Grammatik/X86/CallAlign16.lean` new, 466 lines). I read the full
`PATCH.diff` (559 lines), `OWNER-TASK.md`, `MUSE-REPORT-771.md`,
`BUILD-EVIDENCE.json`, and verified every claimed dependency against this
clone's accepted tree (`Typen`, `Stapel`, `Ausfuehrung`, `Byteschritt`,
`StackUnwind`, `.tmp/HARDWARE-REFERENCES/REFERENCES.json`).

## 2. Architecture findings

- Gate, not a machine: `rufAlignOk` reuses accepted `Stapel.ausgerichtet16`
  (`decide (a.toNat % 16 = 0)`, verified `Stapel.lean:40`); `callGeprueft`
  refuses misaligned call sites with `none` and is the accepted `schritt`
  otherwise; `rufByteschritt` lifts the gate to fetched bytes via accepted
  `fetchDekodiert`. No new machine, decoder row, or source interpreter.
- Coverage is complete: canonical `Befehl` (`Typen.lean:53-68`) has exactly
  one call form (`.call32`) and one return (`.ret`), so `istRuf` matching
  only `.call32` leaves no unchecked neighbour. The non-call passthrough
  (`callGeprueft_durchlass`) is therefore sound, not a hole.
- Offset arithmetic is real: `rsp8_versatz8` goes through
  `BitVec.sub_add_cancel` + `BitVec.toNat_add` + `omega`, not prose.
- `CallAlign16_verbindung` reuses accepted `schritt_call32_erfolg` and
  `StackUnwind.call_ret_wiederhergestellt` (signature verified
  `StackUnwind.lean:84-98`). I traced all 10 premises: each pins one guard
  of the two steps, the read-back, or the alignment — none discarded, no
  `Prop`-typed premise, no `intro _` / `have _ :=`.
- Full PATCH read: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
  conclusion is not a premise restated; no contract quantification games;
  no new semantics without memory effects.

## 3. Witness and negative side

`CallAlign16_verbindung_zeuge` is joint and non-degenerate: accepted image
(`alignBild_wohlgeformt` by `decide`, profile `.p48`), fetch decodes the
call from loaded bytes (`alignS0_fetch`), `lauf [call, ret]` reaches the
restored state, memory observably changes (zero becomes return word
`0x1005` at `alignOben`, via `geladenByte_bss` + `writeBytesN_hit`), rsp is
restored — plus a misaligned twin (`alignSmis_fehlalign`) the gate loudly
refuses. Byte-level refusal theorems cover fetched misaligned calls and
fetched aligned steps. Rule 13's "table" wording is source-syntax; the X86
analogue (memory-changing reached run, as the ZEUGE line itself requires)
is delivered and the author discloses the reading. Axioms are a subset of
`[propext, Quot.sound]` — within the `gabbro_ziel` standard.

## 4. No overclaim

Hardware honesty holds: a misaligned `call` does NOT fault on silicon — the
16-byte rule is an ABI-style obligation enforced here as a checked refusal,
and the author leaves silicon correspondence, faulting SSE transfer,
TSO/concurrency, source/cost/handler claims and entry-rsp alignment OPEN in
CUTS. Provenance header cites edition 325462-093US, sha256
`a4a62e6a…f321` — verified byte-identical against local `REFERENCES.json`.
"Per image" is discharged as uniformity over loaded memory plus a
one-image witness; disclosed in the report, accepted as bounded.

## 5. Limits of this review (honest)

- `./lean-bau` / `./lean-probe` could NOT be re-run from this session: the
  shell tool call was permission-denied. The green evidence is the author's
  `BUILD-EVIDENCE.json` (final `./lean-bau` exit 0, `Build completed
  successfully (485 jobs)`; final `lean-probe` 0 errors; axiom prints) plus
  my exact line-level PATCH inspection. Merger must re-run the standard
  gate; do not treat this ACCEPT as a build result.
- `gabbro_ziel` axiom re-print stayed blocked by apparatus (`failed to
  create thread`, transient olean reads); the module is outside that file's
  import closure and adds no axioms — noted, not a blocker.

## 6. Minimal repairs

None. No source change requested.
