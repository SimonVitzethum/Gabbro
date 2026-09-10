# TOCTOU address space: does M3 / the World–Place model cover user-copy?

**Measured 2026-09-10, worktree `lane-51` (base `d162dfc`). Verdict: GAP.**

The question: whether SYNTAX §3 / M3 address spaces plus the World/Place model
cover user-copy TOCTOU — the check-then-copy shape across a user/kernel boundary
(`copy_from_user`: validate a user range, then copy from it, with the hazard that
the user side changes the bytes between the check and the copy).

## What COVERED would have required

At least one of: a user-memory region in the grammar or the World; a copy
primitive whose shape binds validation to copying (validate-then-copy,
inseparable); a rule or statement shape that refuses, or names, two reads of the
same user bytes with a check between them. None of the three exists.

## Evidence

**1. SYNTAX §3 has no user space, and `space` maps to no Lean.**

The space alphabet is closed (`dokumente/SYNTAX.md:352`):

```ebnf
space  = "normal" | "mmio" | "dma" | "code" | "boot" | "port" | ident ;
```

and the `space` row of the §3 table (`dokumente/SYNTAX.md:371`) maps the whole
concept out of the grammar:

> *the barrier follows from the space; the space of a carrier is a declaration
> fact and the emitter's concern* — Lean: **none** — *a declaration attribute.*

A `retires … from space` clause names a space (`SYNTAX.md:558`), but that is a
linear token leaving, not a memory region that untrusted bytes live in.

**2. The Lean type drops the space entirely.**

`grammatik/Grammatik/Typen.lean:52-56`:

```lean
| ptr (t : Nat) (rw : Bool)
```

The comment says the value is the *capability to name `t`*, and every access
through it needs the guards of `t` like a direct one. There is no side, no
region, no second world for the bytes to come from.

**3. Access through a pointer is the SAME access, once.**

`grammatik/Grammatik/Syntax.lean:292-295` (`Expr.durch`): `p->f` is the same
access as `T.slots[i].f` with the same guards (`hL : darf D t Λ`). One read, one
guard set, no re-read. A check-then-copy sequence — two reads of one user range
with a validation between them — has no constructor to be written with.

**4. The grammar `World` is one flat mapping.**

`grammatik/Grammatik/Semantik.lean:77-80`: per table, index and field a value;
per global a value; plus the trace. A single address space by construction:
there is no user partition whose contents could change under a check.

**5. The Body.lean `World`/`Place` model is one flat function.**

`programmlogik/Gabbro/Body.lean:138-145`:

```lean
inductive Place where
  | slot (carrier : String) (index : Int) (field : String)
  | field (carrier : String) (name : String)
  | global (name : String)

abbrev World := Place → Value
```

One function from places to values. Reading twice reads the same function
twice; the model has no writer on the user side between the two reads (the user
is not a thread in `Wettlauf.lean`), so the hazard — `v_check ≠ v_copy` — is not
statable, let alone refused.

**6. M3 checks rights and placement, never check-then-copy.**

`crates/gabbro-check/src/m3.rs:1-24` states the pass's three duties (rights,
DMA boundary note, placement rule) and explicitly what it is not (no alias
analysis; W9 silence where the pointer type is unresolvable). Its rules:

| rule | what it holds | TOCTOU relevance |
|---|---|---|
| `R001` | no `ops` carrier in `dma` space (`m3.rs:898-925`) | placement, not copying |
| `R002`/`R003` | read needs `r`, write needs `w` | per-access rights, one access at a time |
| `R004`/`R007` | same place at two `own` / writable parameters | call-shape alias, syntactic |
| `R008` | space must MATCH at a call (`m3.rs:265-318`) | equality of spaces, no crossing |
| `R013` | rights NARROW, never widen | lattice direction, no re-read |
| `R005`/`R006`/`R012`, `R009` | register classes, phases | device access, not user memory |

No rule reads a user range twice; no rule binds a check to a later copy.

**7. The word does not occur.**

`grep` over `crates/`, `dokumente/SYNTAX.md`, `dokumente/SPRACHE.md` finds no
`copy_from_user`, `copy_to_user`, or user-memory region construct. The six-room
census in `messung/ADRESSRAEUME.md` (§§5–7) is `normal/mmio/dma/code/boot/port`;
a user space is absent from the alphabet, the census, and the emitter.

## Consequence

GAP, on three independent legs: the grammar cannot *write* a user region or a
two-read sequence (legs 1–3), neither World model can *state* the hazard
(legs 4–5), and the checker has no rule that *fires* on it (legs 6–7). The
design shape for the missing piece is `grammatik/Grammatik/Adressraum.lean`
(new file, defs only): user-memory region, copy primitive with
validation-then-copy shape, boundary-crossing statement shapes as Prop-valued
defs.
