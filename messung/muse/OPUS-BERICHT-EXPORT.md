# Widening the exporter — sieve (b) of the chain

**Opus lane `export`. 2026-09-15.** Branch `worktree-agent-af1187a723d6822c3`, base `6479ea5b`.
Every `cargo build`, `cargo test --no-fail-fast`, `pruefe-emission.sh`, `lake build` and every
`gabbro lean-g` run below was measured on `ki-pc-fisch-101`, directory `gabbro-opus-exp`.

**Assignment:** `instrumente/zaehle-kette.py --lean` measures five sieves per corpus program;
sieve (b) is `gabbro lean-g`, and it covered **10 of 113** programs. Every program the exporter
refuses can never close a chain.

---

## 1. THE MEASUREMENT, first — every refusal, grouped by cause

`gabbro lean-g` was run over all **113 tracked** `beispiele/*.gab` (the population
`zaehle-kette.py` uses: `git ls-files` restricted to the top level, not the 797 files the
recursive glob would catch). **10 export, 103 refuse.**

The exporter stops at its FIRST refusal, so this table is *"which sieve stops the program
first"*, not *"everything wrong with it"* — closing a group moves its programs onward to
whatever refuses next, which is why §3 re-measures rather than predicts.

| n | group (first refusal) | class |
|---:|---|---|
| **11** | `LG001 static has no G form` | **(i)** `Deklaration.Glob`/`gtyp`/`Expr.glob`/`Stmt.assignGlob` are in `Syntax.lean`; the exporter writes `Glob := Empty`. 7 of the 11 are scalar statics, 4 declare an ARRAY static, which has no single-`Wert` form — those stay (ii) |
| **11** | `LG002 type X is not an integer range`, `X` a RECORD (`type Zelle = { … }`) | **(i)** `Syntax.lean` §1/§9 says a record is a `Tab` with `count 1`; the exporter builds no such table. A big job (every `x.f` access changes shape), not this lane |
| **9** | `LG001 type X has no G form`, `X` **`opaque`** (`opaque type Pa = u64;`) | **(i)** the alias IS an integer range; `opaque` is a rule about a UNIT BOUNDARY, and `Deklaration` has no boundary — exactly the argument the ledger already makes for `pub` |
| **9** | `LG001 function f is not 'impl'` (`spec fn`, `extern fn`, `prim fn`, `divergent fn`) | **(ii)/(iii)** a foreign body is `D.Ax` and a `spec fn` is substituted; neither has a `Programm.rumpf` |
| **7** | `LG002 type X is not an integer range`, `X` an **exclusive** range (`u32 in 0 ..< N`) | **(i)** `int_ty` returns `None` for `b.exklusiv`; `0 ..< N` is `.int 0 (N-1)` |
| **7** | `LG001 type X has no G form`, `X` **`linear`** (`linear ghost type Marke;`) | **(i)** `D.Marke`/`stufen`/`Res.marke`/`Stmt.advances`/`retires` are all in the spec |
| **5** | `LG001 assume has no G form` | **(i)** `D.Annahme` exists, but is only consumed at `forever` and `retires` |
| **4** | `LG001 format has no G form` | **(i)** `Tab` with `count 1` plus `Block.pruefung` (`Syntax.lean` §9) |
| **4** | `LG001 device has no G form` | **(i)** `D.Reg`/`rklasse`/`Block.regLies`/`Stmt.regSchreib` |
| **4** | `LG005 const X is not a numeral` | **(i)** the constant is an array/aggregate literal, which the `Scope` cannot hold |
| **4** | `LG001 table X carries a form with no G counterpart` (`invariant`, `ops`, `tree`, `occupied`) | mixed: a table invariant is `D.Inv` **(i)**; `tree`/`occupied` are **(ii)** |
| **4** | `LG002 field f has no integer-range or bool form` (`option index into Self`, `wrapping`) | **(i)** for the option (`Ty.opt`, `Expr.some`/`istSome`); **(iii)** for `wrapping` |
| **4** | `LG001 type X has no G form`, `X` **`tagged`** | **(i)** `Ty.sum`, `Expr.fall`, `Stmt.onTag` |
| **3** | `LG001 lock X carries a form with no G counterpart` (`masks irqs`, shared hold) | **(i)** `D.maskiert` exists |
| **2** | `LG004 … runs a floored caller into a floorless callee (RufPasst.hb)` | **EXPORTER DEFECT** — see §5 |
| **2** | `LG001 arena X has no G form YET` (**O14**) | **(i)** by name: `ArenaZucker.lean` has the sugar, the exporter does not build the pair |
| **2** | `LG001 atomic has no G form` | **(i)** `D.atomar`, `Stmt.publish`, `Block.awaits`/`exchange` |
| **2** | `LG006 'traverse' domain is not a table` | **(ii)** a `traverse` over a computed domain has no `Stmt.traverse` form |
| 1 each | `requires profile`, a call in value position, `group`, `accumulates`, a lock protecting an unknown name, `when` on an item, a `let` past its annotation, a `deadline` clause, a float alias | mixed |

**The 10 that export today:** `104-referenz`, `108-disjoint-start-locks`,
`118-sperrinvariante-erhaltung`, `119-sperrinvariante-bloecke`, `130-derived-contract-pure`,
`15-own-traegt-beide-rechte`, `16-by-ops-am-feld`, `62-grenzwort-im-ausdruck`,
`69-integer-conversion`, `73-sugar-widths`.

### 1.1 The work order this table decides

Largest group of class **(i)** first, and the record group is named as (i) but deferred with a
reason:

1. **`static` (11)** — globals. The largest, and the prerequisite for O14.
2. **`opaque` (9) + exclusive range (7)** — two one-line causes, 16 first-refusals between them.
3. **the arena (2)** — `O14`, named in the assignment.
4. **`RufPasst.hb` (2)** — decide defect or rule, with the measurement.
5. **records (11)** — class (i), NOT done here: a record type changes the shape of every
   `x.f` access, the `Tab count 1` lowering, `count`, the footprint and the guard proofs. It is
   a lane of its own and is booked as such, not as an oversight.
