# MUSE-REPORT-1124: Independent exact review of candidate 1123

## Scope and identity

- Reviewer clone verified: `/home/simon/Dokumente/gabbro-muse/a1124`, branch `muse/1124`.
- Candidate reviewed from the pinned snapshot only
  (`.tmp/review/author-1123/`, `SNAPSHOT.json`):
  author 1123, HEAD `6aaaecf8f8e0e8f3b55c75ee63b9a4397bd6ba01`,
  base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`, clean.
- Candidate file list (from `PATCH.diff`): exactly three files —
  `MUSE-REPORT-1123.md` (new), `grammatik/Grammatik.lean` (one added line),
  `grammatik/Grammatik/X86/HwFaults.lean` (new, 476 lines).
  No other existing file is touched. The `Grammatik.lean` hunk adds only
  `import Grammatik.X86.HwFaults` after the `ISARelaxWitnesses` line.
- This lane owns only this report file. No `grammatik/` file was modified
  in the reviewer clone.

## Checks performed

1. **Forbidden tactics.** Grepped the candidate file for
   `sorry`, `native_decide`, `unsafe`, `sorryAx`: zero matches.
   Grepped for `axiom`: zero matches (no declarations).
   Grepped for `admit`: the only hit is English prose inside a `/--`
   doc comment ("faults admit no state step"), not the Lean tactic.
   PASS.
2. **`#print axioms` coverage and standard.** The file ends with 35
   `#print axioms` lines, one per definition/theorem, plus a `CUTS:` block.
   Per the author's recorded `lean-probe` output in `BUILD-EVIDENCE.json`,
   every main theorem depends only on `[propext]` or `[propext, Quot.sound]`
   (several depend on no axioms at all) — a subset of the goal standard
   (`propext`, `Classical.choice`, `Quot.sound`), no `sorryAx`. PASS.
3. **Existing files untouched except one import line.** Confirmed from
   `PATCH.diff` hunks: `Grammatik.lean` gains exactly the one import line;
   all other diffs are the two new files. PASS.
4. **Every premise used; no `Prop`-typed premise; rule 4 clean.**
   Priority lifts forward every stage-quietness hypothesis to the accepted
   dominance theorems. Buffer-discipline theorems consume their
   non-writability/non-readability hypotheses via `simp`/`rw`.
   `hwFehlerSchritt_wf` consumes both premises (`h` by `cases`,
   `hwf` by `exact` in each branch); the unpacked fault-descriptor fields
   in the self-loop branch are constructor data, not discarded Prop premises.
   No conclusion restates a premise, no contract quantification is weakened
   (no contracts involved), no new "semantics" is claimed beyond embedding
   `HwSchritt` plus self-loop fault steps. One judgment call, documented:
   `fehler_ist_vorzstand` proves `∃ vor, ...` with witness `m` itself; this is
   data-level (the fault outcome carries the pre-state with unchanged
   memory/buffers), not an existential restatement of a Prop premise, and it
   is exactly the "fault outcome IS the pre-state" property the task asks for.
   PASS with that note.
5. **Accepted evaluator lifted, not copied.** The file imports only
   `Grammatik.X86.HardwareExecution` and
   `Grammatik.X86.ExceptionPriorityHardware` and applies the accepted
   definitions by name. Spot-checked in the reviewer tree (all present):
   `kandidatenReihe`, `ersteWahl`, `abruf_schlaegt_alles`,
   `urteil_halt_ist_teilung`, `vektor_pf_vierzehn`, `hwSchritt_wf`,
   `verweigertAdapter`, `hwWit_laden_code_verweigert`,
   `fehlbyte_kein_stiller_ud`. No decoder row, machine, or priority order
   is redefined. PASS.
6. **Planted refusals really refuse.** All five refusal shapes go through
   accepted equations by name: illegal byte (`fehlbyte_kein_stiller_ud`),
   LOCK (`hwLock_verweigert`), code-cell load/store
   (`hwWit_laden_code_verweigert`, `hwWit_ausgabe_code_verweigert`),
   zero-divisor divide IS `#DE` (via `fehler_div_null_haelt_zeuge.1` + `rfl`).
   The oracle-#UD theorem requires oracle-stated illegality and does not
   claim #UD from bare refusal. PASS.
7. **Witness non-degenerate.** `hwFehler_zeuge` joins `HwWf hwWitStart`
   (a `hwFehlerSchritt_wf` premise) with the reached fault step
   `hwFehler_wit_schritt` on core 1 (fetch `#PF` via `decide`), beside the
   accepted two-core TSO facts: owner-only forwarding (owner sees 42,
   other core sees 0) and a memory-changing drain (0 becomes 42, observed
   from both cores), plus code-cell refusals and divide-#DE. Two cores, a
   memory-changing step, owner-only forwarding. PASS.
8. **Silicon facts.** Vectors 0 (`#DE`) and 14 (`#PF`) and the
   fetch-first priority order are inherited from the accepted
   `vektor_de_null` / `vektor_pf_vierzehn` / dominance theorems by name,
   which carry the 660/670 manual provenance; the candidate states
   Table 6-1 / Table 7-2 / §3.3.7.1 as the source. The Intel SDM snapshot
   metadata (edition 325462-093US, September 2026, SHA-pinned) is recorded
   in `.tmp/HARDWARE-REFERENCES/REFERENCES.json`. The candidate performs
   no silicon re-verification and says so in CUTS. For a connection lane
   this is the correct posture. PASS.
9. **CUTS honest, no oversized claim.** The CUTS block lists exactly what is
   proved and explicitly disclaims hardware verification, #UD-from-refusal,
   unmasked `#XM`/`#AC`/`#NM`, fault delivery (stays with lane 672),
   per-access target-to-W/GX simulation, whole-word atomicity beyond the
   accepted guard, and source/time transfer. No hardware-correspondence or
   W/GX bridge is claimed. The report's claims match the file. PASS.
10. **Builds.** Author evidence (`BUILD-EVIDENCE.json`): final
    `./lean-probe grammatik/Grammatik/X86/HwFaults.lean` reports
    `0 error(s)`, and `./lean-bau` ends
    `Build completed successfully (601 jobs).`
    Reviewer run on the clean base in this clone:
    `./lean-bau` ends `Build completed successfully (600 jobs).`
    (600 = base without the candidate's one new module; consistent.)

## What remains open (not a defect)

- Fault delivery (IDT/stack/handler/error code) stays with lane 672, as stated.
- Per-access target-to-W/GX simulation, whole-word atomicity beyond the
  accepted guard, and source/time transfer are untouched, as stated.

## Task fidelity notes

- Nothing in the lane task appears wrong. There were no `ZEUGE:` target lines;
  the joint `hwFehler_zeuge` satisfies the task's non-degeneracy asks.
- The byte-granularity statement of the store/load discipline matches the
  level the coherent machine stores at; the report explains why the 8-byte
  refusal does not transfer. No weakening.

## Verdict

CANDIDATE: 1123 6aaaecf8f8e0e8f3b55c75ee63b9a4397bd6ba01
VERDICT: ACCEPT

Exact candidate, no premise smuggling, no weakened guarantee, no fake closure.
