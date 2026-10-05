# MUSE-REPORT-1123: Architectural faults as outcomes of the coherent machine

## What was done

New file `grammatik/Grammatik/X86/HwFaults.lean` (474 lines, commit
`b1bc0901`), plus the one permitted `import Grammatik.X86.HwFaults`
line in `grammatik/Grammatik.lean`. No other existing file touched;
no model copied -- every fact lifts an accepted definition by name.

- **§1-§2 machine choice + SDM priority.** `hwFehlerWahl` runs the
  accepted ordered candidate row (`kandidatenReihe`/`ersteWahl` from
  `ExceptionPriorityHardware.lean`) on the core projection
  (`projFp m c`). `hwFehlerWahl_reihenkopf` (rfl) plus four priority
  lifts: fetch beats all, address beats access/divide/control,
  access beats divide/control, divide beats control.
- **§3-§4 faults as outcomes.** `HwFehlerAusgang` extends
  `HwRegAusgang` with `fehler : HwMaschine → PrioritaetsFehler → ...`
  (pre-state machine + ordered stage/class, never an
  `Option`-plugged successor). `einbettenReg` embeds constructor by
  constructor (`einbettenReg_kein_fehler`: never a fault;
  `fehler_ist_vorzstand`: the fault outcome IS the pre-state).
  `adapterFehler1123 : HwAdapter PrioritaetsFehler` refuses
  everything (a fault admits no successor state).
- **§5-§6 extended steps + evaluator agreement.** `HwFehlerSchritt`
  embeds every `HwSchritt` under `.alt` with the EXACT two-way
  embedding (`hwFehlerSchritt_einbettung_vor/zurueck`); fault steps
  are self-loops (`hwFehlerSchritt_fehler_still`); all steps preserve
  `HwWf` (`hwFehlerSchritt_wf`). Binder equations reused by name:
  success keeps its successor, halt IS divide #DE, refusal is never
  a fault; vectors 0 (#DE) and 14 (#PF).
- **§7 buffer discipline.** Faulting store: `issueByte` refuses at a
  non-writable cell, hence NO machine store step exists there
  (`hwFehler_schreibfehler_kein_puffer`) -- nothing enters any
  buffer. Faulting load: `loadByte` refuses at a non-readable cell
  and every load step is a self-loop
  (`hwFehler_lade_aendert_nichts`). Oracle-stated illegality IS the
  #UD candidate (`hwFehler_orakel_ud`).
- **§8 planted refusals.** Illegal byte (no silent #UD), LOCK,
  code-cell load/store on the witness machine, zero-divisor #DE on
  real execution -- all through accepted equations.
- **§9 joint witness `hwFehler_zeuge`.** Core 1 (non-executable RIP)
  takes the fetch #PF (`hwFehler_wit_abruf` by `decide`,
  `hwFehler_wit_wahl`, `hwFehler_wit_schritt`); beside it the
  accepted two-core TSO run: owner-only forwarding (core 0 sees 42,
  core 1 sees 0), drain changes ACTUAL shared memory 0 -> 42
  observed from both cores. Joins the premises of
  `hwFehlerSchritt_wf` (`HwWf hwWitStart` + the fault step).

## Exact names

Defs: `hwFehlerWahl`, `HwFehlerAusgang`, `einbettenReg`,
`fehler_ist_vorzstand` (thm), `adapterFehler1123`,
`HwFehlerEreignis`, `HwFehlerSchritt`, `hwFehlerZLeer`,
`hwFehlerPgDunkel`. Theorems: see the 34 `#print axioms` lines at
the file end; main ones `hwFehler_zeuge`, `hwFehlerSchritt_wf`,
`hwFehler_schreibfehler_kein_puffer`,
`hwFehler_lade_aendert_nichts`, the four priority lifts, the two-way
embedding pair.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwFaults.lean`: 0 errors.
- `./lean-bau` last line: `Build completed successfully (601 jobs).`
- Axioms: every main theorem depends only on `[propext]` or
  `[propext, Quot.sound]` (subset of the goal standard; no
  `Classical.choice` needed, no `sorryAx`). No `sorry`/`admit`/
  `axiom`/`native_decide`/`unsafe` in the file.
- No premise has type `Prop` itself; every premise is used
  (priority lifts consume all stage-quietness hypotheses).

## Open / not claimed

Per the CUTS block: no hardware verification (classes/vectors/order
name the accepted 660/670 manual entries, nothing re-verified
against silicon here); no #UD membership from refusal alone; no
unmasked #XM/#AC/#NM; no fault delivery (stays with lane 672); no
per-access target-to-W/GX simulation; no source/time transfer.

## Task fidelity notes

- The task asked for a faulting store/load discipline "where the
  family touches memory": byte-granularity TSO (`issueByte`/
  `loadByte` check single-cell permissions) is the exact level the
  coherent machine stores at; the 8-byte `read64`/`write64` refusal
  does not imply a single-byte TSO refusal, so the theorems are
  stated at the byte level the machine uses. Nothing is weakened:
  a refused byte store provably admits no machine store step.
- No `ZEUGE:` target lines were given; `hwFehler_zeuge` joins the
  `hwFehlerSchritt_wf` premises and the task's non-degeneracy asks
  (two cores, memory-changing step, owner-only forwarding).
