# MUSE-REPORT-417: Reserve register-only conditional select (ConditionalMove)

## Task

Lane 417 (continuous Lean proof reserve): create ONLY
`grammatik/Grammatik/X86/ConditionalMove.lean` plus one additive X86 import
at the end of the umbrella. Model and prove register-only conditional select
from the canonical condition/flags/registers; preserve unaffected registers
and flags; prove the chosen operand. Show safe optional-lowering premises and
a real target-execution consumer. Never invent a second machine/IR; reuse the
accepted pilot vocabulary (`Ausfuehrung`, `FlagBeweis`, `Typen`,
`ControlFlow`). Keep codec/source/full-hardware correspondence OPEN
(CMOVcc has no native pilot encoding: `EMITTER-INVENTAR` lists NO
setcc/cmovcc, `Befehl` has no cmov constructor).

## What was done

New module `grammatik/Grammatik/X86/ConditionalMove.lean` (318 lines),
imported as the last line of `grammatik/Grammatik.lean`. No existing file
touched otherwise; no new machine, instruction, decoder row, memory model,
or source claim. Everything is proved over the REUSED definitions
`ControlFlow.cmovAnwenden`, `cmovSchritt`, `cmovMemSchritt` and the reused
witness states `witTrue`/`witFalse`.

Definitions (1):

- `cmovLowerOk (d : Decodiert) (flagsNachCmp flagsVorCmov : Flags) : Bool`
  — safe optional-lowering admission: checked decoded length
  (`laengeOk d.laenge`) AND flag identity between compare and select
  (`decide (flagsNachCmp = flagsVorCmov)`). Register-only by construction
  (the reused `cmovAnwenden` takes no memory operand). Validator admission,
  never a hardware fault.

Theorems (17), every premise used in its proof:

- `cmovAnwenden_nicht_wert` — untaken select keeps the destination word.
- `cmovAnwenden_genommen_wert` — taken select takes the source word.
- `cmovAnwenden_fremd` — every register except `dst` is preserved.
  (Flags/memory framing of the pure application is reused from
  `cmovAnwenden_flags` / `cmovAnwenden_speicher`, not restated.)
- `cmovSchritt_nicht_genommen` — untaken decoded step (complements the
  reused taken-only `cmovSchritt_genommen`).
- `cmovSchritt_verweigert` — bad decoded length refuses (`none`).
- `cmovSchritt_flags` / `cmovSchritt_speicher` / `cmovSchritt_rip` —
  per-step framing of a successful select step.
- `cmovLowerOk_garantiert` — admission implies good length AND flag
  identity (both conjuncts from the single `Bool` premise).
- `cmovLowerOk_laenge_verweigert` (length 0, concrete `decide`),
  `cmovLowerOk_flags_verweigert` (flag clobber, concrete `decide`),
  `cmovLowerOk_akzeptiert` (good length + identical flags, concrete).
- `cmov_store_verbraucher` — REAL pilot consumer: the taken select value
  is stored by the CANONICAL pilot `schritt` store64 (reused
  `schritt_store64_erfolg`); conclusion pins the full successor state and
  the selected word. Uses all five premises (`hbed` rewrites the word,
  `hne` keeps the store address, `h`/`hok` drive the store equation).
- Joint witnesses with concrete ALL-premise instantiation on the reused
  non-degenerate states plus the reused memory-changing run
  `cmov_speicher_zeuge` (word 20 stored at 8192, byte observably changed
  from zero; taken/untaken split reused from
  `cmov_witness_unterscheidet`):
  `cmovSchritt_nicht_genommen_zeuge`, `cmovSchritt_verweigert_zeuge`,
  `cmovLowerOk_garantiert_zeuge`, `cmov_store_verbraucher_zeuge`
  (stored word reads back as `some 20` through the real `schritt` store).
- No-speculation for the memory form is reused from
  `cmovMem_feheler_bleibt` (fault kept on the untaken path), not restated.

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` (grep: only the
English word "admitted" in two prose comments). No `Prop`-typed premise,
no discarded premise, no premise-free existential of a premise.

## Check results (measured, this clone)

- `./lean-probe grammatik/Grammatik/X86/ConditionalMove.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. All 17 `#print axioms`
  standard: value/framing/guarantee theorems depend on `[propext]` or
  nothing; the consumer and all four witnesses on `[propext, Quot.sound]`
  (via the reused store equation and witness run). Subset of the allowed
  triple everywhere.
- `gabbro_ziel` axiom check (scratch probe of `BeweisAtomar`):
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged, exit 0.
- `./lean-bau`: 392/393 targets build, INCLUDING this module (its 17
  axiom lines print in the build log); the final umbrella step
  (`Grammatik.lean`, the import-all file) aborts with
  `libc++abi: terminating ... failed to create thread`, exit 134.
  PROVEN ENVIRONMENTAL, not caused by this lane: with my umbrella
  one-liner stashed (`git stash push grammatik/Grammatik.lean`), the
  identical umbrella step fails identically; the change was restored
  afterwards (`git stash pop`, diff verified: exactly the 1-line import).
  Cause is machine resource exhaustion (many concurrent lanes; swap full).
  The merger/integration only needs to re-run `./lean-bau` on a quiet
  machine; no Lean content change is indicated.

## Open / CUTS (also at the end of the file)

- No `Befehl` constructor, `Codec` row, or bytes for CMOVcc: no codec,
  source, or emitted-native-ISA claim by design (pilot subset).
- No hardware correspondence: flag readings reuse `bedingung`, faults are
  the permission-checked `read64`/`write64` outcomes, not silicon.
- No TSO/GX, concurrency, cost, time, termination, or timing claim.
- 32-bit narrow clearing (upper32 zeroing) is not modelled — only the
  64-bit register select is stated.

## Task feedback

Nothing in the task as written is wrong. One note for future reserve
lanes: under current machine load the umbrella `Grammatik.lean` step is
the fragile one (`-j2` thread spawn aborts); module-level `./lean-probe`
stays reliable and should remain the primary gate, with `./lean-bau`
re-run at integration.
