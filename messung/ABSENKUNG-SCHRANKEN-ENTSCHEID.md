# Lowering-bound decision — widen to measured max plus one headroom

Date: `2026-09-10`. Base: `c7dcd69`. Lane: `lane-53`.

Fact on the table: `messung/ABSENKUNG-MESSUNG.md` measures a maximum of
`17` C statements per Gabbro primitive (static count over the emitter
source, `crates/gabbro-check/src/emit.rs`, `11708` lines), against the
assumed carrier bound `8` in `grammatik/Grammatik/Ziel.lean`. `17`
exceeds `8`.

## Verdict: option (a) — widen the bound

The structure bound moves `8` to `18` (measured maximum `17` plus one
headroom); the witness moves `4` to `17` (the measured maximum fills
`proPrimitiv`, exactly as the procedure in
`messung/ABSENKUNG-ZAEHLUNG.md` section `2` prescribes — the bound
beside it stays as the check the maximum fits):

```
structure Absenkung where
  proPrimitiv : Nat
  begrenzt : proPrimitiv ≤ 18
def absenkung : Absenkung := ⟨17, by decide⟩
```

`17 ≤ 18` still closes with `by decide`; the self-check output stands
in section `3`.

## Recount — option (c) attempted and dropped

The `17` was recounted statement by statement from
`emit.rs:8523-8560` (`fn nachfahren`), same lexer as the measurement
(one `;` in emitted C text is one statement; loop-header separators,
comments, and refusal strings excluded; nested body statements booked
on the body, not on the row):

| Emitted fragment | Statements |
|---|---|
| root, cursor, flag declarations (`const uint32_t _r`, `uint32_t _k`, `bool _h`) | `3` |
| cursor advance with flag reset plus `continue;` | `3` |
| loop-exit `break;` | `1` |
| successor word declarations (`uint32_t _w; bool _w_hoch;`) | `2` |
| successor selection, both branches (`_w = …; _w_hoch = …;` twice) | `4` |
| binder declaration plus void silencer (`const uint32_t v = _k; (void)v;`) | `2` |
| cursor writeback (`_k = _w; _h = _w_hoch;`) | `2` |
| Total | `17` |

`3 + 3 + 1 + 2 + 4 + 2 + 2 = 17`. The count stands; there is nothing to
dispute.

## Why not option (b) — the emission is not narrowed

Every one of the `17` statements carries the stackless post-order walk:
cursor, flag, successor selection, and writeback are what make the walk
return up the tree without a stack. Removing any of them changes what
the walk visits, so no narrowing is trivially safe. `emit.rs` was NOT
touched.

## 3. Self-check

`lake env lean Grammatik/Ziel.lean`, run in `grammatik/`
(no full build, no `cargo`). The bare command cannot resolve the
`Grammatik` imports — the worktree carries no `.lake` build and building
one is out of scope (`unknown module prefix 'Grammatik'`). The green run
below is the same command with `LEAN_PATH` pointed, read-only, at the
existing build of the base commit in the main tree:

```
'Gabbro.Grammatik.ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_rahmen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_spur' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_wettlauf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_wettlauf_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ordnung' depends on axioms: [propext, Classical.choice, Quot.sound]
```
exit `0`. (The imports — `Grammatik.Wettlauf`, `Grammatik.Zucker` —
were read from the main-tree oleans, whose sources are byte-identical
to the worktree's; only `Ziel.lean` differs, and only at the constant
above. No build was started and no binary was produced.)

## 4. What stays open

- The runtime half of `messung/ABSENKUNG-ZAEHLUNG.md` section `2`
  (minimal units, real `emit` outputs, one lexer) is still missing. It
  can only confirm the maximum or raise it, never lower it below `17`.
  The `+1` headroom absorbs a rise to `18`; a rise past `18` moves the
  bound again.
- Finding `W7` is half closed: the static half of its search path is
  now walked and booked; the runtime half is not.
- Scope kept: only `grammatik/Grammatik/Ziel.lean` edited, only this
  file created. No Lean sentence, no fragment file, and no checker
  source changed.
