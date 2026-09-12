# MUSE-REPORT-14 (lane 14): counterexample to hBlattAll for writing leaves

## What was done

New file `grammatik/Grammatik/BlattGegenbeispiel.lean` (namespace
`Gabbro.Grammatik.BG`), wired via `import Grammatik.BlattGegenbeispiel` at the
end of `grammatik/Grammatik.lean`. It builds a concrete small declaration and
program plus a writing leaf whose execution changes the truth of the thread's
own `QEnsures`, and proves the goal theorem's `hBlattAll` premise false for it.

Construction:

- `D1 : Deklaration` — `Tab = Unit` (one table), one field `()` of type
  `.bool`, `count = 1`; `Fn = Unit` (one function) with `schreibt = true`;
  unguarded (`braucht = []`); unshared (`geteilt = false`) so the declaration
  proof obligations stay trivial; no globals, locks, marks, axioms, registers.
- `V1 : Vertrag D1` — the contract of the only function.
- `i0`, `slotE`, `negE` — index `0`, slot read, negated slot read.
- `writeLeaf : Stmt D1 V1 false [] [] []` — `assignSlot () () i0 negE`, i.e.
  `T.slots[0] := not T.slots[0]`. Proved a leaf (`writeLeaf_blatt`) and not
  memory-preserving (`writeLeaf_nicht_fest`).
- `P1 : Programm D1` — `requires = .wahr`, `ensures = slot read`.
- `O1 : Orakel D1` — empty oracle (no axioms/registers/globals).
- `weltB b tr` — world with slot `b` and trace `tr`.

## New definitions and theorems (exact names)

- `BG.D1`, `BG.V1`, `BG.i0`, `BG.slotE`, `BG.negE`, `BG.writeLeaf`,
  `BG.P1`, `BG.O1`, `BG.weltB`, `BG.Jcode0`
- `BG.writeLeaf_blatt : writeLeaf.istBlatt = true`
- `BG.writeLeaf_nicht_fest : writeLeaf.speicherfest = false`
- `BG.qensures_ist_slot : QEnsures P1 () σ ↔ σ.slots () 0 () = true`
- `BG.qrequires_immer : QRequires P1 () σ`
- `BG.feuerung_schreibt : (execStmt O passes keinRuf writeLeaf σ ρ).welt = some σ' → σ'.slots () 0 () = !b` (given incoming value `b`)
- `BG.hblatt_post_falsch : ¬ (QEnsures P1 () σ ↔ QEnsures P1 () σ')` for the firing from a `false` slot
- `BG.hblatt_konj_falsch : ¬ ((QRequires … ↔ QRequires …) ∧ (QEnsures … ↔ QEnsures …))`
- `BG.hblattall_falsch_schreibend : ¬ ∀ (M₀ : GenMaschine D1) (pc₀ : PCStand), PCReach … → … → (QRequires … ↔ …) ∧ (QEnsures … ↔ …)` — the `hBlattAll`-shaped universal (thread code fixed to the constant `Jcode0`, the only function) is false, instantiated at the start machine with `writeLeaf`.

Every premise of every theorem is used by its proof (no discards, no bare
`Prop` slots, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`).

## Last ./lean-bau result

`Build completed successfully (30 jobs).`, including
`[28/30] Built Grammatik.BlattGegenbeispiel` and `[29/30] Built Grammatik`.
`#print axioms` for the four main theorems shows only
`[propext, Classical.choice, Quot.sound]`.

## What remains open

- The `J.code g` wrapper of the real `hBlattAll` is mirrored by the constant
  `Jcode0`; falsity is proved for that instantiation, not for an arbitrary
  `GemeinsamerLauf` code map.
- The leaf is fired directly through `execStmt`, not through a full `PCReach`
  derivation ending at the firing machine (the firing fact holds at every
  machine, reachable or not, so reachability is named but not discharged).
- `QRequires` survives the write (it is `.wahr`); only the `QEnsures` leg and
  hence the conjunction is refuted.

## Proposed replacement premise (report part of the task)

Once contracts are checked at call entry/return instead of at every world,
`hBlattAll` (per-leaf preservation of the thread's own `QRequires`/`QEnsures`
at every firing) should be replaced by a per-call boundary premise:

- `hBlattCall (g)`: for every call step of thread `g` (firing of
  `Stmt.call`/`Stmt.callInd` or the corresponding `PCSchritt` through
  `keinRuf`-free handler `R`), the callee's `QRequires` holds at the entry
  world (caller obligation, with actual argument values and actual parameter
  environment — no `forall rho` quantification away), and at the matching
  return world the callee's `QEnsures` holds (with the actual return value).
- Intermediate leaves of the body — including writing leaves like `writeLeaf`
  above — owe nothing to the contract predicates between entry and return;
  only the frame duty (`Rahmen` over the declared writes) and the trace duty
  (`Brav`) still apply per step.
- Concretely, in `SpecTriple` terms: keep `requiresHead`/`ensuresHead` as
  entry/return obligations at the call boundary and drop the
  `requiresEigen`/`ensuresEigen` per-firing iffs for non-call leaves; call
  leaves take a one-sided implication (entry `Pre` implies return `Post`)
  instead of a per-step iff.

This keeps contracts at their place (entry with actual parameters, return
with the actual value) and stops demanding that a body preserve its own
contract while it is still establishing it — which is exactly what the
counterexample above shows to be unprovable.

## What in the task I believe is wrong

Nothing material. One note: the task says `hBlattAll` "is discharged only for
memory-preserving leaves (`hBlattAll_speicherfest_aus_feuerung`)" — that
matches `Maschine.lean` section 22, but the discharge needs `SpeicherVertrag`
(mffine `Pre`/`Post` read only live memory) beside the firing evidence; it is
not firing-evidence-alone. The counterexample respects that boundary: `Q`
here is memory-only (`speicherVertrag_aus_Q` applies), yet the `Post` iff
still fails because the write changes memory itself.
