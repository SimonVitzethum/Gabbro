# MUSE-REPORT-250 — D.klon exporter fill (TODO §-1 O-1 remainder)

Branch `muse/250`. Scope kept: only `crates/gabbro-check/src/lean_g.rs` and
`crates/gabbro-check/tests/lean_g.rs`. No checker pass, no `emit.rs`, no Lean
file, no `MARKE_EMIT*`, no new N/C/LG codes, no gift/example numbers.

## 1. Finding: the fill as specified is unbuildable in this tree

O-1 item 3 asks for the exporter to fill `D.klon` from source — one
`(gate Ax, entry Fn)` pair per `stack`-carrying gate. Three facts, each
verified in the tree, block it:

1. **This tree's `Deklaration` has no `klon` field.** `D.klon : List (Ax × Fn)`
   exists only on the parked review branch `opus/clone-handoff` (commit
   `cde18e25`, read via `git show`, never checked out or merged — the merge
   `a4461b6b` deliberately took only the Rust half). Emitting `klon := …`
   into a generated file would print a field Lean rejects, i.e. an export
   that does not elaborate — exactly what `pruefe-exportlean.py` calls a
   refusal the exporter failed to make. Lean files are read-only for this
   lane, so the field cannot be created here.
2. **The exporter writes `Ax := Empty` and refuses every foreign body**
   (`syscall`, `extern fn`, `axiom`, `entrust`) with LG001 at collect time.
   There are no `Ax` entries to pair with, and exporting them is a separate
   lane's work (foreign-body export), not a fill.
3. **The child entry is an inline block, not a named `Fn`.** Pairing it would
   require outlining the `child { … }` block into a function the source never
   declares — inventing program structure, against the exporter's no-silent,
   no-invented-guard rule (cf. the `alloc`-without-`else` decision).

So no shape can be mapped today. Per the brief ("unmapped shapes keep a NAMED
refusal, narrowed LG004, never silent") the deliverable is the narrowed
refusal: each arm now enumerates the exact gate list the model needs, by name,
wherever the information exists.

## 2. What changed (code)

`crates/gabbro-check/src/lean_g.rs`:

- **New `ItemArt::Syscall(s) if !s.stapel.is_empty()` arm (LG001)** ahead of
  the foreign-body catch-all. Names the gate (`s.name.text`) and the handed
  register(s), and states the pair it would become: one `D.klon` entry
  (gate `Ax`, entry `Fn`) with the function its `child` path runs — blocked
  because the export writes `Ax := Empty` over a `Deklaration` with no `klon`
  field. Gates WITHOUT `stack` keep the old foreign-body message byte for
  byte (proven by the third leg of the new test).
- **Narrowed `StmtArt::Child` arm (LG004).** Names the enclosing function
  (the entry half of the pair) and the same pair shape/blocker; the gate arm
  above names the gate (the `Ax` half). Both arms still return `Err`
  unconditionally — the accept set is unchanged by construction (see §4).

`crates/gabbro-check/tests/lean_g.rs`: new test
`refuses_child_carrying_gate_by_name` — gate snippet refuses LG001 naming
gate + register + `D.klon`; `child` snippet refuses LG004 naming statement +
entry function + `D.klon`; stack-less gate keeps the `D.Ax` message.

No new definitions/theorems (Rust lane; Lean untouched, so rules 6/13 need
no witness — there is no new Lean statement and no new accepted behavior).

## 3. Gate-list format (deliverable 2)

Per gate with a `stack` clause, the model needs one `D.klon` pair
`(gate Ax, entry Fn)` — the Ax entry for the syscall gate, the Fn entry for
the function whose `child` path runs (the reviewer-branch shape, `cde18e25`
`Syntax.lean` diff; `CloneHandoff.lean` §1/§4 for the legs). What still
refuses: everything — all gates at the narrowed LG001, all child blocks at
the narrowed LG004, plus the pre-existing earlier walls (checker N446–N450,
emitter C185, LG001 for `assume` items, which is what 155/156/1112 actually
hit first in walk order).

## 4. Verification

- `./cargo-pruef`: 52/52 `test result: ok`, 0 non-ok; `tests/lean_g.rs`
  88/88 incl. the new test. Zero failures.
- `./lean-bau`: `Build completed successfully (280 jobs).` (no Lean files
  touched; axioms untouched).
- `pruefe-genlean.py --binary target/debug/gabbro`: **2 BEFUNDE** —
  pre-existing, unrelated: both are `obligations --g` drift on
  `GenOblig104/108.lean` (committed files miss a `-- RELEASE OBLIGATION`
  trailer the generator now writes). Neither input is in my diff
  (`obligations_g.rs` and both committed files untouched — `git status`
  shows only my two files), so the mismatch predates this lane. Left for the
  obligations owner; not smuggled into this commit.
- **Export census** (`gabbro lean-g` over all 125 `beispiele/*.gab`):
  15 accept / 110 refuse — before and after identical by construction (the
  diff touches only two `Err` message strings; both arms still refuse
  unconditionally). Movement: 0, as required (a fill that cannot map must
  move nothing upward). Child-carrying programs, each listed, all still
  refused: 155 + 156 at LG001 (`assume` item, walk order), 1112 at LG001
  (`assume` item), 1109 at checker N448, 1110 at N449, 1111 at N450
  (`lean-g` runs the checker first; gifts never reach the exporter).

## 5. What I believe is wrong in this task

- **"One positive export test" is unbuildable.** No child-carrying program
  can export while `D.klon` has no field and `Ax := Empty` holds; a passing
  export test would have to invent the field or the Ax entries. The refusal
  test above is the honest lock: it fails the day a shape stops being
  refused, which is exactly when the real fill (with the Lean field) lands.
- **"Which entry Fn" is ambiguous in the O-1 model.** The branch docstring
  says "the function its `child` path runs" — for 155 that reads as the
  enclosing `starter` (the child runs inline in the caller's frame context),
  not the `arbeiter` it calls. The narrowed messages name the enclosing
  function; the fill lane that creates the field should pin this reading.
- Minor: the brief's READ-FIRST points at `ref-wip` (stale 2026-09-11 base,
  no klon) and `ZielOrt*.lean`/`ziel_ort` (absent from this tree); the
  binding klon shape is on `opus/clone-handoff` (`cde18e25`), readable via
  `git show` from this clone.

## 6. Branch state

`muse/250`: this report + the two-file diff, to commit. No remote, nothing
pushed. `MARKE_EMIT*` untouched. Scratch probe under `.tmp/` (private, not
committed).
