# MUSE-REPORT-235 — never/never-asm lowering (TODO §-1 wave C)

Lane 235. Scope: `crates/gabbro-check/src/emit.rs` (one narrowed arm) +
`crates/gabbro-check/tests/never_lowering.rs` (new, 11 tests) +
`beispiele/gift/1066-*` (rewritten + renamed, same number) + this report.
No checker, no Lean, no `MARKE_EMIT*`, no new codes, no gift/example numbers,
no OS surface.

## 0. Read first (done)

- MUSE-REPORT-225: checker acceptance is sentences + probes, zero behavior
  change; N321 byte-identical; the handoff is exactly the never-`asm`
  without `out` shape (`gift/1066`, emitter `C001` at the `hat_ergebnis` arm).
- MUSE-REPORT-231 (`Zielsatz/Divergenz.lean`, read, not edited): the
  divergence side (`forever_noexit_divergiert`, `asm_never_kein_ok`) is proved
  in Lean; this lane discharges nothing there — it lowers what 225 accepted.
- MUSE-REPORT-227 (switch lowering) + MUSE-REPORT-252 (traverse exits): the
  measured-lowering pattern (snippet tests, `cc -fsyntax-only` as the C-level
  proof, no corpus files, `MARKE_EMIT` delta 0).
- `pruefe-cformen.py`: the new emission uses only existing rows (`stmt:asm`
  assumption `AxCorr`, `stmt:forever` lemma `scorr_forever`, `stmt:goto` /
  `stmt:label`, plain calls) — no new C form, so no row added, nothing silent.

## 1. Measured before building (scratch `.tmp/s235/`, git-ignored)

| shape | checker today | emitter today |
|---|---|---|
| never-`asm`, no `out` (225's handoff) | 0 errors | **C001** `hat_ergebnis` arm |
| never-`asm`, `in`-only | 0 errors | **C001** same arm |
| never-`asm`, `out { w }` (non-`result`, names a param) | **0 errors** (silence) | **C001** same arm |
| never-`asm`, `out { result }` | **N321** | **C001** N321 arm |
| never + `forever` (bounded `per_pass`, diverging watchdog, no total costs) | 0 errors | lowers, `cc` clean |
| never + tail call to a `-> never` routine | 0 errors | lowers (once the callee lowers), `cc` clean |
| never-`asm`, `or R` channel | 0 errors | **C001** `return type` (channel path calls `ctyp(Never)` = none) |
| never-`Block`, `or R` channel | **N034** | (never reached clean) |

Three findings that shaped the fix:

- **F-a.** A non-`result` `out` on a never-`asm` is checker-*silent*. Naively
  counting `never` as "no result" would have emitted `[w] "=a" (w)` — an
  output into a by-value parameter that dies with the call (and a duplicate
  symbolic name beside the `in`). So the fix refuses any `out` on never by
  name instead of lowering it.
- **F-b.** `-> never or R` is checker-silent for `asm` bodies but refuses at
  the channel path before any stub is written (`bool` vs `_Noreturn`
  contradict). No change needed; pinned.
- **F-c.** The `forever`/tail-call shapes needed no repair (225 measured
  `cc`-clean; re-measured here). Pinned, not repaired.

## 2. What was built

- `emit.rs`, `funktion`, `asm` arm only (+22 lines, comment included):
  `ist_nie` (`ergebnis is Never`) counts as "no result" — no `result` local,
  no `return`; a never body with ANY `out` operand is refused with its own
  narrowed `C001` sentence (no result slot; output into a by-value parameter
  dies with the call). The N321 arm above and the old `hat_ergebnis` arm
  below are byte-identical. Lowered shape for the handoff program:
  ```c
  static _Noreturn void halt(void) __attribute__((unused));
  static _Noreturn void halt(void) {
      __asm__ __volatile__(
          "hlt\n"
          : 
          : 
          : "memory");
  }
  ```
  (`_Noreturn` from the untouched `prototyp_kern`; no attribute from the
  untouched `wirkungsattribut`, which already returns `""` for never.)
- `tests/never_lowering.rs` (new, 11 tests): positives lower + carry the
  C-level noreturn proof (`cc -std=c11 -Wall -Wextra -Werror -fsyntax-only`
  over the emitted unit — a `_Noreturn` body that returned would fail there):
  never-`asm` without `out`, never-`asm` `in`-only, never-`forever` WITH a
  table write inside the loop (non-degenerate), never tail-call. Refusals
  pinned exact-code: never+non-`result`-`out` → `[C001]`, never+`result` →
  checker `[N321]` + emitter `[C001]`, never+`or R` → `[C001]`,
  non-never `u64`-`asm` without `out` → `[C001]` (narrowing guard: the old
  arm still fires), K003/S006/S009 → exact (checker, untouched).
- `beispiele/gift/1066-never-asm-ohne-out.gab` → renamed to
  `1066-never-asm-mit-out-ohne-result.gab` (same number 1066, `git mv`) and
  rewritten: the handoff body is consumed (it now lowers — keeping the old
  pin would be a lie the suite catches), so the number now pins the narrowed
  boundary (F-a shape: `-- erwartet: C001`, checker silent). The lowered
  shape's positivity lives in `never_lowering.rs` + `cc`. Header records the
  lineage. No new gift number taken.

## 3. Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (incl. the 11 new tests and
  the converted 1066 through `jedes_gift_faellt_mit_seinem_code`).
- `./emission-pruef`: `== EMISSION: ALL PASS -- 37 durchgestochen, 288 von
  288 uebersetzen, 2 umgekehrte Probe(n) ==`, exit 0. (288, not 252's 286:
  lane 242's two emitting demos merged after 252's run — not mine.)
- `python3 instrumente/pruefe-cformen.py`: exit 1 with ONLY the pre-existing
  single unclassified line (lane-221 `140-atomic-array-counter.gab` CAS
  fragment, same as lanes 227/252) — 0 new uncovered, 0 missing lemmas,
  0 missing assumptions. No row added: no new C form emitted anywhere.
- `python3 instrumente/pruefe-saetze.py`: exit 0 (425 Kennungen, 176 Saetze).
  `pruefe-englisch.py`: exit 0.
- `./lean-bau`: `Build completed successfully (280 jobs).` (no Lean inputs
  changed.)
- **MARKE_EMIT delta: 0** on all counters — no corpus/gift file added or
  turned emitting; 1066 still refuses. Untouched, as ordered.

Rule-13 note (Rust lane): no Lean theorems added, no `ZEUGE:` target in the
task, so no `_zeuge` is owed. The witness analogue is the positive rows —
the `forever` positive writes a table slot inside the lowered loop
(checker-clean, emitted, `cc`-clean); the refusal pins reuse K003/S006/S009
and the narrowed C001, the same split lanes 227/252 shipped.

## 4. Per shape: what lowers, what refuses, why

- **Lowers:** never-`asm` without `out` (bare `__asm__` under `_Noreturn`,
  `cc`-proved); never-`asm` with `in`-only (inputs read parameters —
  well-defined); never-`forever` with bounded pass + diverging watchdog
  (`for (;;)`, pre-existing); never tail-call (the call, pre-existing).
- **Refuses:** never + any `out` (`result` → N321 + C001; other → narrowed
  C001 — F-a: an output into a by-value parameter dies with the call);
  never + `or R` (C001 at the channel path — F-b: `bool` vs `_Noreturn`);
  K003/S006/S009 forever ends (checker, untouched).
- **Noreturn honesty:** for `forever`/tail-call the non-return is structural
  (`for (;;)` / callee diverges). For `asm` the instruction text is
  unchecked BY CONSTRUCTION (`asm_versiegelt`) — the C-level `_Noreturn` is
  earned by the CHECKED declaration (`arch`/`effects`/`costs` + `-> never`,
  lanes 225/231), not by reading the text. A lying `hlt`-shaped body is user
  logic misdeclared, same class as a lying `effects` clause — refused
  nowhere, assumed everywhere. Stated plainly so no one reads "proof" as
  "verified instruction".

## 5. Handoff + scope notes

- `emit.rs` is free after this merges: the delta is one narrowed arm plus
  comments, no open edits. Lane 248 (reserve/commit arm, queued behind 235):
  the `asm` arm it will sit beside is unchanged except the `ist_nie` early
  block; no trap.
- No N codes used (lowering lane, as planned — refusals reuse N321/C001/
  K003/S006/S009/N034). No gift numbers taken (1066 reused); no example
  numbers taken. Nothing to return, nothing owed.
- Preamble conflict, same ruling as lanes 227/252 §5.1: the wave-5 preamble
  ("INDEPENDENT REVIEWER: do not change any existing file") contradicts this
  task's scope box (`emit.rs` is "YOURS alone"). The task wins; recorded here.
- Stale-but-untouchable: `namen.rs` (N321 arm comment) and `saetze.rs` (two
  `gemessen_an` texts) still say `gift/1066` "pins the handoff" / "emitter
  still refusing". Both files are read-only for this lane (225 merged); the
  number still pins the 235 boundary, and 1066's own header records the
  lineage. A wording touch-up is a one-line follow-up for whoever owns those
  files next — not this lane.
- `Spec.lean` NOT-CLAIMED list: untouched, correctly — nothing claimed here
  moves it (no termination, no new hardware assumption; `_Noreturn` is the
  checker's accepted declaration reflected, not a discharged premise).

## 6. Commits on `muse/235`

1. `emit.rs` narrowing + `tests/never_lowering.rs` (11 tests).
2. Gift 1066 rename + rewrite to the narrowed pin (+ comment touch-ups).
3. Forever positive strengthened with the table write.
4. This report.

Each committed green (`cargo-pruef` exit 0 before every commit).
