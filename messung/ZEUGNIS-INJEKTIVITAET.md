# Zeugnis injectivity beyond the traversal domains (Lane O, 2026-09-10)

## The question (OB3)

Since `e5e555d` the certificate is injective over the nine traversal domains:
36 pairs measured (`crates/gabbro-check/tests/zeugnis_injektiv.rs`), not all programs.
The open question stands one level up:

> **A certificate that vouches for an equivalence class vouches for no program.**
> Every plan that leads translation validation through the certificate rests on
> this one property: does the certificate identify the PROGRAM, or only the
> SHAPE of what the translation rests on?

This file measures exactly that. It changes nothing.

## How it was measured

26 program pairs, each differing in exactly ONE construct, each rendered under the
SAME file name (`probe.gab` -- the header cannot tell them apart, same rule as the
36-pair test). Both sides pass `gabbro check` with `0 errors` (an unchecked pair is
`UNGUELTIG`, a probe fault, never a verdict). Harness: `/tmp/lane-o/zinj.py`
(scratch, not in the tree); binary `target/debug/gabbro` was newer than all of
`crates/` at the time of the run.

- `INJEKTIV` -- the certificates differ; the Zeugnis sees the difference.
- `KOLLISION` -- byte-identical certificates for two different programs.
- `STABIL` -- the same program twice gives the same certificate (counter-direction:
  without it a timestamp would count as "injective").

Result: **3 INJEKTIV, 22 KOLLISION, 0 UNGUELTIG, 1 STABIL.**

## Verdict per domain

The certificate counts MARKS (`assignment 1x`, `const 1x`, `table.absenkung 1x`),
never details. Two programs that differ WITHIN a mark get the same certificate:

| domain (EINORDNUNG entry) | pair | verdict |
|---|---|---|
| `const` | value 8 vs 9 | KOLLISION |
| `table` | `count NK` vs `count 32` | KOLLISION |
| `table` | name `Knoten` vs `Knoten2`, same shape | KOLLISION |
| `type (Bereich)` | bound `..< 32` vs `..< 33` | KOLLISION |
| `type (Verbund)` | extra field `zahl` | KOLLISION |
| `walk` | `levels 2` vs `levels 3` | KOLLISION |
| `walk` | `down` with vs without `!` | KOLLISION |
| `format` | one field fewer | KOLLISION |
| `static` | value 64 vs 65 | KOLLISION |
| `reason` | number 1 vs 9 | KOLLISION |
| `assume / axiom` | text "eins" vs "zwei" | KOLLISION |
| `fn (impl/…)` | return type `u32` vs `u64` | KOLLISION |
| `let` | value 1 vs 2 | KOLLISION |
| `assignment` | value `true` vs `false` | KOLLISION |
| `return` | `x` vs `N` | KOLLISION |
| `if` | condition `== 1` vs `== 2` | KOLLISION |
| `match (option)` | arm body `true` vs `false` | KOLLISION |
| `let … else` | fallback `0` vs `1` | KOLLISION |
| `call` | local target `g1()` vs `g2()` | KOLLISION |
| expression | operand order `x && g` vs `g && x` | KOLLISION |
| array length | `[RingNr; NR]` vs `[RingNr; 16]` | KOLLISION |
| `costs` clause | `<= 0 ops` vs `<= 5 ops` | KOLLISION |
| `call` + foreign body | extra `extern fn nie2`, called | INJEKTIV (new foreign name + `fn` count) |
| `if` present vs absent | mark appears/disappears | INJEKTIV (control) |
| `table` one vs two | `table.absenkung 1x` vs `2x` | INJEKTIV (control) |
| same program twice | identical source | STABIL (control) |

What the certificate DOES see: the SET of marks (presence, count) and the NAMES of
foreign bodies. What it does NOT see: any value, bound, number, text, type, target,
or operand order inside a mark. The `call-ziel` row is the sharp edge of the rule:
a call to a different FOREIGN function is visible (new name in section E), a call
to a different LOCAL function is not -- the certificate sees the callee SET, never
the call EDGE.

## The verdict for OB3

**`unbrauchbar-als-Beweistraeger` is MEASURED, not asserted: the Zeugnis identifies
an equivalence class, not a program.** 22 of 23 difference-pairs collide; the one
that does not differs in the mark SET, not in a detail. Translation validation
through the certificate alone cannot distinguish `count 8` from `count 16`, `== 1`
from `== 2`, or a call to `g1` from a call to `g2` -- and the emitted C differs in
every one of these cases.

This does NOT demote the 36-pair result: within the traversal domains the marks
are per-domain (`traverse (slots of)` vs `traverse (threads)`), so domain
differences ARE visible. The boundlessness of `chain(…) in`, `fields of`,
`threads` (no `domaenenschranke`, `K003` asks) is a statement about COST bounds,
not about identity -- it is orthogonal to this finding and stands as documented.

## What was NOT measured (open)

- `lock`/`locks` (rank, footprint), `effects` details, `exchange`/`publishes`/
  `awaits`/`atomic` orderings, `retry`/`forever`/`leave`/`next`, `breaking`,
  `entrust` details, `entry`/`boot`/`check`, `device (mirrors)`, `group`,
  `accumulates`, `narrow`, `observes`/`rcu`, `fn (spec)`, `type (ghost/tagged)`
  details -- each needs a heavier scaffold (device/register context, lock
  footprint, foreign contract). Same harness, richer base programs.
- Redesign needs (REPORTED, not built): if the certificate is to carry programs
  instead of classes, each mark must record its distinguishing detail (the bound,
  the number, the callee). That is a `zeugnis.rs` change and belongs to whoever
  owns OB3-next -- this lane measured only.
