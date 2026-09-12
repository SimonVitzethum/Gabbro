# MUSE-REPORT-71: `_Noreturn` on a function-pointer variable (emitter repair)

Lane 71, Rust emitter. This lane is a Rust lane, so there is no Lean work, no
`grammatik/` change, no `ZEUGE` obligation, and no new Lean theorems to list.

## What was done

1. **Root cause** (`crates/gabbro-check/src/emit.rs`, `bezugnahme`):
   - `beispiele/07-eintritt-und-boot.gab` dispatches its boot path to
     `rust_eintritt`, an `extern fn ... -> never`.
   - `prototyp_kern` lowers `-> never` to the core `_Noreturn void`, and
     `bezugnahme` spelled the checked dispatch reference with that same core:
     `static _Noreturn void (*const gabbro_boot_multiboot1_dispatch)(void)
     __attribute__((unused)) = rust_eintritt;`
   - C11 has no pointer-to-noreturn type: `_Noreturn` applies only to function
     declarations. Measured here (gcc 13.3.0, clang 18.1.3): gcc refuses with
     `declared '_Noreturn'`, clang with `'_Noreturn' can only appear on
     functions`. A typedef for a noreturn function type fails identically in
     both compilers, so "typedef it" is not an alternative.
2. **Fix** (`crates/gabbro-check/src/emit.rs`, `bezugnahme` only):
   - The reference strips one leading `_Noreturn ` from the core before
     spelling the pointer: `static void (*const
     gabbro_boot_multiboot1_dispatch)(void) __attribute__((unused)) =
     rust_eintritt;`
   - The noreturn guarantee is kept where both compilers read it: the
     function's own prototype, written by the same lowering, still reads
     `_Noreturn void rust_eintritt(void);`.
   - The fallback arm (`__typeof__`) is untouched: it is only reached where
     prototype emission already refused the same name, so the unit already
     carries that refusal.
3. **Regression test**
   (`crates/gabbro-check/tests/rechenwerk.rs`,
   `ein_bezug_auf_never_ist_ein_schlichter_zeiger`): poison direction (no
   `_Noreturn void (*const` in the emission of a boot dispatch to a `-> never`
   target, reference line verbatim), positive direction (prototype still
   `_Noreturn void ziel(void);`), and entry-dispatch control (returning target
   reference unchanged).

## Verification (exact)

- `./target/debug/gabbro emit beispiele/07-eintritt-und-boot.gab | cc -std=c11
  -Wall -Wextra -Werror -c -o /dev/null -x c -`: OK (exit 0, no output).
- Same pipeline with `clang`: OK (exit 0, no output).
- Corpus before/after sweep (832 `.gab` under `beispiele/ messung/ sonden/`,
  213 emit on both runs): exactly one file differs,
  `beispiele/07-eintritt-und-boot.gab`, and the diff is exactly the one line
  above (minus `_Noreturn `). No other emission changed byte-wise.
- `./cargo-pruef`: `== exit 0; failing tests: 0` (all suites green, including
  the new test).
- `./emission-pruef` (full log `.tmp/emission.log`, 453 lines): stage 9 no
  longer lists `beispiele/07-eintritt-und-boot.gab` anywhere -- `grep 07
  emission.log` is empty, and the `UEBERSETZT NICHT` list holds no `07` entry.
  `202 von 220 emittierenden Dateien uebersetzen` (was fewer before only
  because 07 fell); `201 von 202, die cc annimmt, nimmt auch clang an`.

## Still red in stage 9 (other lanes' -- not touched)

- `beispiele/66-transport-rueckgabe.gab`: clang-only refusal
  (`-Wfor-loop-analysis`, `bereit` not modified in loop body); cc accepts.
- `beispiele/gift/776-v003-hint-await-only-hull.gab`: `return` with a value in
  a void function.
- `messung/proben/absenkung/probe-absenkung-*.gab` (17 files): intentional
  lowering probes (e.g. `probe-absenkung-zuweisung.gab` emits `static uint32_t
  main(...)`, refused by `-Werror=main`).
- Plus count-mark findings unrelated to C acceptance (`FUND: 71 statt 70`,
  `133 statt 73`, gift-cover `9 statt 2`, 8 new emitting roots): booked
  numbers, not compile failures.

## Notes / weaker-than-asked

- Nothing here is weaker than the task: the line compiles under both
  compilers, the guarantee is kept on the declaration, and the emitter's
  single-register property (`bezugnahme` still reads the one `prototyp_kern`
  core, never a second spelling) is preserved.
- `python3 instrumente/pruefe-englisch.py` was already red on this tree before
  my change (baseline via `git stash`: same three `RATSCHE GEBROCHEN` lines;
  my two added German words in one test assert message were rewritten to
  English, remaining deltas are pre-existing comment-count ratchets: 7905 vs
  7881 booked in the checker, 1085 vs 1069 in the instruments, 1 vs 0 German
  message at a sink in `main.rs:713`). Not my lane; reported, not touched.

## Files changed

- `crates/gabbro-check/src/emit.rs` (comment + one `strip_prefix` line in
  `bezugnahme`)
- `crates/gabbro-check/tests/rechenwerk.rs` (new test
  `ein_bezug_auf_never_ist_ein_schlichter_zeiger`)
