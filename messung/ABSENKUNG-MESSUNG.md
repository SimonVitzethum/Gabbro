# Lowering measurement — per-primitive C statement counts against `emit.rs`

Measured: `2026-09-10`, on base `d162dfc`, against
`crates/gabbro-check/src/emit.rs` (`11708` lines, unchanged from the
baseline booked in `messung/ABSENKUNG-ZAEHLUNG.md` section `2`).
No unit was written, no binary was built, no `emit` run took place;
every figure below is a static count over the emitter source, read only.

## 0. Verdict

The measured maximum is:

```
17
```

It belongs to `Schleife`, subform `traverse over descendants of`
(`nachfahren`, `emit.rs:8523-8560`). The bound beside the constant in
`grammatik/Grammatik/Ziel.lean` is:

```
8
```

`17` exceeds `8`, so the acceptance clause of
`messung/ABSENKUNG-ZAEHLUNG.md` section `2` does not fire:
`Ziel.lean` was NOT touched, `absenkung` still stands on `4` with its
`UNMEASURED` comment, and finding `W7` stays open. The `by decide`
proof beside the bound is unaffected; its self-check output stands in
section `5`.

## 1. Counting rules — same lexer, same scaffold

The procedure in `messung/ABSENKUNG-ZAEHLUNG.md` section `2` asks for
the C statements one minimal unit per primitive produces, all units
with the same scaffold, all counts with the same lexer, maximum taken
after the last primitive. This file applies that procedure statically,
because no build and no `emit` run were in scope:

- Lexer: one `;` terminator in emitted C text is one statement, with
  three exclusions. Loop-header separators (`for (...; ...; ...)`)
  are not statements. Comment text is not statements. Refusal strings
  passed to `weigere` are not statements either — they never reach the
  output buffer, they reach the report.
- Scaffold: the file frame (`emittiere`, headers, type declarations,
  prototypes, function frames) is identical for every unit and cancels
  out of the maximum, so it counts toward no primitive.
- Bodies: statements of a nested body block are counted on the rows of
  the primitives that stand in that body, not on the row of the
  enclosing primitive. A row therefore books the scaffold the
  primitive itself emits for a minimal unit, with zero nested
  statements. Including bodies can only raise rows, never lower the
  maximum, so the verdict in section `0` is stable under both
  readings.

## 2. Orientation — emitter-source occurrences, never the result

Read-only baseline, same four commands as
`messung/ABSENKUNG-ZAEHLUNG.md` section `2`. Occurrences in the
emitter source, not statements in emitted C:

```
grep -c "_Atomic" crates/gabbro-check/src/emit.rs
```

```
7
```

```
grep -c "volatile" crates/gabbro-check/src/emit.rs
```

```
48
```

```
grep -c "__asm__" crates/gabbro-check/src/emit.rs
```

```
8
```

```
wc -l crates/gabbro-check/src/emit.rs
```

```
11708
```

All four agree with the booked baseline, so the emitter is the one the
procedure was written against.

## 3. The primitives — seventeen statement kinds

A Gabbro primitive here is one variant of `StmtArt`
(`crates/gabbro-syntax/src/ast.rs:1164-1190`):

```
pub enum StmtArt {
    Let(LetStmt),
    LetSonst(LetSonst),
    Zuweisung(Zuweisung),
    Wenn(WennStmt),
    Match(MatchStmt),
    Schleife(Box<Schleife>),
    Bricht(BrichtStmt),
    Narrow(NarrowStmt),
    Sperrt(SperrtStmt),
    Observiert(ObserviertStmt),
    Leave(Ident),
    Next(Ident),
    Publish(PublishStmt),
    AwaitLoad(AwaitLoad),
    Exchange(Box<ExchangeStmt>),
    Return(Option<Expr>),
    Ruf(Ruf),
}
```

Each variant has exactly one lowering arm in `fn anweisung`
(`emit.rs:6654-7755`), with `Schleife` dispatching to `retry`,
`traverse`, `forever` and `Match` dispatching to `match_option`:

```
6665:        StmtArt::Return(w) => {
6791:        StmtArt::Zuweisung(z) => {
7056:        StmtArt::Narrow(n) => {
7105:        StmtArt::Ruf(r) => aus.push_str(&format!("{e}{};\n", ruf(r, u, absagen))),
7110:        StmtArt::Let(l) if geist_wert(&l.wert, u) => {
7113:        StmtArt::Let(l) => {
7164:        StmtArt::Publish(pb) => {
7188:        StmtArt::AwaitLoad(al) => {
7209:        StmtArt::Observiert(o) => {
7247:        StmtArt::Exchange(x) => {
7464:        StmtArt::Sperrt(x) => {
7481:        StmtArt::Match(m) => match_option(m, s, aus, u, absagen, tiefe, austritt),
7484:        StmtArt::Wenn(w) => {
7500:        StmtArt::Schleife(sch) => match sch.as_ref() {
7514:        StmtArt::Leave(m) | StmtArt::Next(m) => {
7561:        StmtArt::LetSonst(l) => {
7739:        StmtArt::Bricht(b) => {
```

## 4. Per-primitive counts

One row per primitive, direct scaffold statements only (section `1`).
Every count is a plain code span; no cell carries bold type.

| Primitive | Emitter site | C statements |
|---|---|---|
| `Return` | `emit.rs:6665-6787` | `2` |
| `Zuweisung` | `emit.rs:6791-7051` | `2` |
| `Narrow` | `emit.rs:7056-7104` | `0` |
| `Ruf` | `emit.rs:7105` | `1` |
| `Let` | `emit.rs:7110-7146` | `2` |
| `LetSonst` | `emit.rs:7561-7697`, `emit.rs:11542-11622` | `4` |
| `Wenn` | `emit.rs:7484-7499` | `0` |
| `Match` | `emit.rs:7481` via `emit.rs:9033-9119`, `emit.rs:8833-8945`, `emit.rs:8954-8986` | `5` |
| `Schleife` | `emit.rs:7500-7504` via `emit.rs:7768-7839`, `emit.rs:8027-8093`, `emit.rs:8565-8821`, `emit.rs:8372-8424`, `emit.rs:8455-8561` | `17` |
| `Bricht` | `emit.rs:7739-7753` | `0` |
| `Sperrt` | `emit.rs:7464-7478` | `2` |
| `Observiert` | `emit.rs:7209-7221` | `2` |
| `Leave` | `emit.rs:7514-7532` | `1` |
| `Next` | `emit.rs:7514-7532` | `1` |
| `Publish` | `emit.rs:7164-7187` | `1` |
| `AwaitLoad` | `emit.rs:7188-7200` | `1` |
| `Exchange` | `emit.rs:7247-7463` | `10` |

How the non-obvious rows read:

- `Return` reaches `2` on the error-channel arms (`*_grund = ...;`
  plus `return false;`, `*_wert = ...;` plus `return true;`); plain
  returns emit `1`. Releases listed from enclosing locks count `0` in
  a minimal unit, which carries no enclosing lock.
- `Zuweisung` reaches `2` on the register bit-field
  read-modify-write (`_v = ...;` plus the write); every other path
  emits `1`.
- `Let` reaches `2` with the declaration plus `(void)name;` for a
  binding the body never reads back; otherwise `1`. The ghost path
  emits the bare call plus `1` terminator.
- `LetSonst` reaches `4` on the fallible-register-read path
  (`fehlbare_lesung`: binding declaration, error-name declaration,
  single read, conditional error assignment); the call path reaches
  `3` direct. The `else` bodies are nested and excluded.
- `Match` reaches `5` on the tagged form with a non-place scrutinee,
  an unread payload binder, and all arms returning (temporary plus
  payload declaration plus void silencer plus `break;` plus
  `__builtin_unreachable();`); the option form reaches `2`, the
  reason form `2`.
- `Schleife` reaches `17` on `traverse over descendants of`
  (`nachfahren`): root, cursor, and flag declarations (`3`), cursor
  advance with flag reset plus `continue;` (`3`), loop-exit `break;`
  (`1`), successor word declarations (`2`), successor selection
  across both branches (`4`), binder declaration plus void silencer
  (`2`), and cursor writeback (`2`). The `for (;;)` header carries no
  statement. `retry` reaches `5` with both jump labels, `3` without;
  `forever` reaches `3` with both labels, `1` without; `slots of`,
  `elems of`, and `ancestors of` emit `0` direct (a single `for`
  header each).
- `Exchange` reaches `10` on the `update` path (binding declaration,
  counter, expected-value load, operand declaration, binder
  declaration, null statement at the done label, `break;`, bound-exit
  call, counter increment, result writeback); the compare path
  reaches `3`. The `rumpf_als_wert` body is nested user code and
  excluded; a minimal legal body would add `2` more without moving
  the maximum.
- `Leave` and `Next` emit `1` (`goto ...;`) with zero enclosing
  releases in a minimal unit.
- `Narrow`, `Wenn`, and `Bricht` emit control structure and comments
  only: `0` direct.

The maximum over all seventeen rows:

```
17
```

## 5. Consequence for `Ziel.lean`

`17` is greater than `8`, so the constant is untouched:

```
def absenkung : Absenkung := ⟨4, by decide⟩
```

still stands with its `UNMEASURED` comment, and `W7` stays open. A
measured `proPrimitiv` would need a carrier bound of at least `17`,
which the `≤ 8` shape does not offer; widening the shape was out of
scope. The standing proof still checks — self-check in `grammatik/`:

```
lake env lean Grammatik/Ziel.lean
```

```
'Gabbro.Grammatik.ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_rahmen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_spur' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_wettlauf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_wettlauf_global' depends on axioms: [propext, Classical.choice, Quot.sound]
'Gabbro.Grammatik.ziel_ordnung' depends on axioms: [propext, Classical.choice, Quot.sound]
```

exit `0`. (The check needs the project library present; a preceding
`lake build` in `grammatik/` supplied it. No checker build, no
`cargo` invocation took place.)

## 6. What was expressly not done here

- No minimal unit was written and no `emit` run took place; the counts
  are static, over the emitter source, read only. The runtime pass of
  `messung/ABSENKUNG-ZAEHLUNG.md` section `2` (one lexer over real
  outputs) is still the missing half, and it can only confirm or raise
  the maximum, never lower it below `17`.
- No build of the checker was started and no `cargo` command ran.
- No sentence in `SPRACHE.md`, no fragment file, and no Lean source
  was changed — in particular not `grammatik/Grammatik/Ziel.lean`.
- The open fragment `F3` was not touched; `H` still stands where
  `messung/ABSENKUNG.md` books it.

Evidence beside the table: `grep -c` over
`crates/gabbro-check/src/emit.rs` for the baseline, `sed` over
`crates/gabbro-syntax/src/ast.rs:1164-1190` for the primitive list,
`grep -n` over `fn anweisung` for the arm sites, and per-arm reads of
the `aus.push_str` format strings with the section `1` exclusions.
