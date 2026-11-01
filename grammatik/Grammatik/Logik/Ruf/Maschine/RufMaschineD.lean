/-
  File:      Grammatik/RufMaschineD.lean
  Subject:   THE CALL MACHINE (attempt D) -- threads with a FRAME STACK over
             shared memory, call entry and return events with the ACTUAL
             parameter environment, result, and entry world.

  Why: the PC machine (`PCAtom`: leaf/take/rel, Maschine.lean) executes
  footprints, never calls; leaves run with `keinRuf`. Contracts can therefore
  not be checked at their place in a concurrent run, and the goal theorem had
  to fall back to `QRequires`/`QEnsures` (proved degenerate, `QLeer.lean`).
  `VertragOrtB.lean` has the right contract shape (`ReqAmEintritt`,
  `EnsAmRueck` with the actual rho, v and the entry world s0) but its runs
  (`ContrLauf`) are free data. This file generates the runs: a thread state
  with a frame stack, a step relation through `execStmt` (so memory moves on
  writes by construction), call/return events recorded in a per-thread log,
  and reachability generated from a start state.

  Design notes:
  - Frames hold real `Endblock` residues of the callee contract
    (`vertragVon`), so leaf steps run through `execStmt` with `keinRuf`
    (leaves never consult the call handler). Compounds (`ite`, `locks`
    bodies, ...) have no unfold step: the machine is partial there, and the
    adequacy fragment covers only straight-line `ret` bodies (see CUTS).
  - `locks` take/release are standalone scheduler steps (`nimmt`/`gibt`)
    with the `GenSchritt` rule (take only while nobody else holds the lock).
    The machine never gates on contracts: `VertragAmOrtMaschineD` is a
    predicate ON generated runs, not a firing condition.
  - The `rueck` event carries the return world `s1` next to the entry world
    `s0`, so `EnsAmRueck` (which needs both) is stated per event.

  REVIEWER NOTE (merge 2026-09-12, read before building on this file):
  - Frames carry NO local environment. `blatt`, `ruf` and `rueck` each take a
    free `ρ : Env D Γ`, so a step may run under ANY values of the locals:
    the machine over-approximates the program. A contract theorem over its
    runs cannot follow from the body's proof until the frame carries the
    environment of its current context and `blatt` threads it (lane 28's
    `rho : Env D ctx` field is the shape).
  - `RufLogPasstD` is proved to imply return fidelity, but its preservation
    along `RufErreichbarD` is NOT proved. The invariant as stated compares
    whole frames including `rest`, which `blatt` changes; it must be taken
    up to the residue (function, rho, s0) before it can be preserved.
  - The CUTS note "`blatt` never advances the residue" is stale: it does.
-/
module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil1
public import Grammatik.Logik.Ruf.Maschine.RufMaschineD.Teil2
