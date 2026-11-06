### Foreign result areas

A C14 target binding may declare `result area REGISTER` immediately after
`regs out { ... }`, before any `stack` or `clobbers` clause:

```ebnf
result_area = "result" "area" ident ;
sysbind     = "number" expr "regs" "in" regmap "regs" "out" regmap
              [ result_area ] { "stack" ident } "clobbers" names "errors" errmap ;
```

The register is an explicit hidden argument containing the address of a
caller-owned result area. It must be an unused request argument register;
overlap with a source parameter is refused by name. Source arguments retain
their existing order. Stage 0 currently supports this profile with scalar
request arguments; combining it with the separate pointer-buffer profile is
refused.

The area uses the ordinary internal value ABI: exactly `valueWords(resultType)`
64-bit words, in canonical word order. The provider must initialize the complete
value and preserve every other frame byte and all permission maps. Declared
world effects retain their original source contract. This realization is a
binding/user-logic duty, not a hardware assumption. The compiler copies the
complete value into the local binding with the ordinary value transport.

For a fallible call, the normal answer register carries only a tag: zero means
success, and a listed negative errno selects its declared reason. Unknown
nonzero tags stop with 110 before reading the payload. An infallible area
provider supplies a valid typed result under its contract; its answer register
is ignored. Without an explicit area clause, a multiword answer is refused by
name. Existing one-word integer, Bool and capability profiles remain available.

Reference answers name cells of their nominal represented open region. Region
capabilities retain their nominal identity and canonical capability encoding.
Freshness and disjointness remain obligations of the binding's source contract;
the clause introduces no integer-to-pointer conversion or implicit region storage.

### Statement calls with a reason handler

```ebnf
statement += path "(" [ arguments ] ")" [ "?" | "else" [ "(" ident ")" ] block ] ";" ;
statement += "(" expr ")" "(" [ arguments ] ")" "else" [ "(" ident ")" ] block ";" ;
```

`f(args) else { ... };` handles failure of a fallible foreign call and discards
its normal answer. `else (reason) { ... };` additionally names the reason inside
the handler, using the same reason binding as `let ... else (reason) { ... }`.
The handler must end with a return or another valid block exit. Success continues
with the original local scope; the discarded answer introduces no local.
A user function or an infallible foreign callee with a statement handler is
refused by the named `call else needs an axiom callee` or
`call else needs a fallible axiom callee` elaboration error, respectively.
The existing foreign result-type and contract admission rules still apply.

For a function pointer, `p(args) else { ... };` and
`(p)(args) else (reason) { ... };` use the pointer type's argument, effect,
result and reason contract. `(&f)(args) else { ... };` evaluates the function
reference once through the existing typed pointer binding. Success discards the
value; the ending failure block has its own reason scope. An infallible pointer
is refused with `indirect call else needs a fallible function pointer`; an
explicit expression that is not a pointer is refused with
`call else needs a function pointer`. The current exporter admits local
function pointers and function references as these expressions; other expression
shapes are refused with `indirect call else expression without G form`.
The canonical `Stmt.callIndElse` requires a value result type; a fallible void
pointer statement is therefore refused with `indirect call else needs a result type`.


### Flat record embedding

A record body may contain `..Name`, for example
`type Body = { ..Pos, mass: f64, };`. Embedded fields precede the record's
own fields, preserving embedding order and each embedded record's field order.
Their types and field metadata are retained. Literals and field access use the
resulting flat field names; embedding introduces no conversion or subtyping.
Duplicate field names, non-record targets and recursive embeddings are refused
with named `record embedding` errors. Existing restrictions on field metadata
remain enforced by the record exporter after expansion.

### Finite folds and boolean existence

```ebnf
primary    += foldexpr | existsexpr ;
foldexpr    = ( "add" | "min" | "max" ) ident "in" domain
              [ "where" pred ] ":" expr [ "else" expr ] ;
existsexpr  = "exists" ident "in" domain ":" pred ;
```

```gabbro
let open_sum = add k in slots of Orders where Orders[k].open : Orders[k].amount;
let best = min k in slots of Jobs : Jobs[k].latency else 0;
let worst = max k in slots of Jobs : Jobs[k].latency else 0;
let failed = true && (exists k in slots of Jobs : Jobs.slots[k].failed);
```

A fold traverses one finite table domain using an internal accumulator. The
existing slot, tree and fixed-array domain exporters determine its iteration
order and membership. The binder is in scope in the filter and element
expression; the `else` expression uses the surrounding scope. Generated local
names cannot collide with source identifiers. An element is evaluated once per
selected slot, after its filter succeeds. Access guards and ordinary expression
checks apply throughout; reading another table in the filter or element is
refused.

`add` starts at zero and forbids `else`. Its integer interval is capacity times
the element interval, including zero when fewer slots can be selected. A result
outside the result type is refused with `fold: result range does not fit its
integer type; narrow the operand first`. A fold never wraps. `min` and `max`
require `else`; the first selected element initializes the result, subsequent
elements update the extremum, and the fallback is evaluated only if no element
was selected. The fallback does not participate in a nonempty reduction.

Float `add` uses an IEEE accumulator initialized to **+0.0**, adding each
selected element in slot order, exactly as the generated `traverse` visits
it. Slot order is part of the meaning: reassociation, tree reductions and
parallel reductions that change the addition order are not allowed.
Float `min` and `max` use the model's ordered strict comparison, retaining
the first selected value on equality (including signed zeros). The kernel
IEEE comparison returns false if either operand is NaN; canonical G float
values are finite, so the existing introduction checks reject NaN and
infinity before they can enter a fold. These checks remain in place for
each generated IEEE operation. Decimal operands use the exact rational
literal and the model's rounding operation. As elsewhere in the canonical
model, `Ty.fl` interprets both f32 and f64 source types in binary64; this
syntax extension does not close the existing f32 precision cut.

An OPEN table has no finite fold capacity and is refused. Missing extrema
fallbacks, an `else` on `add`, unsupported domains and second-table reads are
named refusals. Float folds expand to the existing G IEEE literal and
operation forms. Continuing blocks have a connected exporter. A float
introduction at function top level or in an ending branch remains refused
as `float: IEEE introduction requires a continuing G block; no canonical
Endblock form`: the canonical `Endblock` has no IEEE introductions yet.
Float fold expansion therefore does not claim complete function-level
float lowering.

`exists` is an ordinary boolean expression, including in a binding, condition,
boolean operator or return. It elaborates through the existing predicate
exporter to the canonical `Expr.existsSlots`, equivalent to leaving a traversal
on the first matching slot. It introduces no source interpreter or new G form.
Fold costs use the existing traversal and statement cost computation: capacity
times the per-slot work, including filter and update, plus loop and binding
overhead. These syntax extensions do not change the model's guarantees.

### Nominal table spaces

The canonical Lean source exporter accepts an independent optional table binder:

```gabbro
table T count 2 space Data { slot { value : u32 in 0 .. 100, } }
```

`space Data` binds the table to the nominal space used by `ptr<Data, r> T`.
Omitting it selects `normal`. The registry starts with `normal` and then uses
first declaration order; several tables may explicitly share one name. The
printer puts the binder before `count`; the reader also accepts it among the
other header clauses and refuses a second `space` clause in the same header.

`owner Mark` remains a separate linear-mark obligation and may coexist with
`space Data`. A space name supplies no address, hardware protection or implicit
permission. Existing owner, lock, field, binding and hardware duties still apply.
Unknown pointer-space names and incompatible table capabilities remain refused.

### Call-scoped owner loans and owned access

```ebnf
effect     += "borrows" name ;
effect     += "moves" name ;
effect     += "mints" name ;
```

A function that touches an `owner`-guarded table through an `own@m` capability
borrows the owner mark for the call: `effects { …, borrows Marke }`. The loan is
the C09 `OwnerFlow.loans` entry: the callee holds the mark during the call, the
caller gets the same mark back on normal return. A `borrows` that names no
table owner is refused (`loan without owner`); a mark both `consumes`d
(`takes`) and borrowed is refused (`mark both consumed and borrowed`); ordinary
`allocs` of an owner stays refused (`owner produced without mint`).

```gabbro
impl fn u(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool
  effects { reads r.slots, writes r.slots, borrows Marke }
  { r.slots[i].b = true; return r.slots[i].b; }
```

Reads and writes through the owned capability elaborate to the canonical owned
accesses `Expr.thruOwn` / `Stmt.assignThruOwn`: the same guarded carrier as
`thru` / `assignThru`, plus the resolved owner mark, the table's owner entry
and the guard at the held stage. Machine G evaluates and executes them exactly
like the plain forms. Access without the held mark is refused
(`access without held guard`); an unresolvable owner is refused
(`owned read/write without a declared owner mark`).

### Checked owner mint and linear handoff

A function that creates an `owner`-guarded table's mark declares it:
`effects { …, mints Marke }`. The mint is the checked `OwnerFlow.mints`
output: the minter holds the fresh owner from its start frame and returns it
on every exit. It is never ordinary production (`eigner_nie_erzeugt` still
forbids owner `produziert`). A `mints` that names no table owner is refused
(`mint without owner`); a second mint of the same instance is refused
(`duplicate mint`).

```gabbro
impl fn minter(r : ptr<normal, rw+own@Marke> T, i : index into T) -> bool
  effects { reads r.slots, writes r.slots, mints Marke }
  { r.slots[i].b = true; return r.slots[i].b; }
```

A function that takes an owner's mark for the call declares
`effects { …, moves Marke }`. The handoff is the `OwnerMove` handback: the
callee holds the same nominal identity during the call and hands it back at
the same stage on the normal and the reason return alike. A `moves` that
names no table owner is refused (`move without owner`); a mark both borrowed
and moved, or consumed and moved, is refused (`mark both borrowed and moved`,
`mark both consumed and moved`); moving a mark the caller does not hold is
refused at the call (`call without held mark`).

```gabbro
impl fn mover(p : ptr<normal, rw+own@Marke> T, i : index into T) -> bool
  effects { reads p.slots, writes p.slots, moves Marke }
  { p.slots[i].b = true; return p.slots[i].b; }
impl fn caller() -> bool
  effects { writes T.slots, moves Marke }
  { mover(&T, 0); return true; }
```

A terminal transfer uses the existing `consumes` effect: the callee receives
the mark and promises no handback (`OwnerMove.after := none` for an owner).
It must explicitly discharge that input before returning:

```gabbro
impl fn finish() effects { consumes Marke } { retires Marke; }
impl fn caller() effects { consumes Marke } { finish(); }
```

`retires Marke;` removes exactly the held mark from the resource inventory.
The same statement discharges an ordinary linear mark, such as a C16 Duty.
It introduces no runtime value and no hardware assumption. Retiring an unheld
or already retired mark is refused (`retire without held mark`); retiring a
`borrows` loan is refused (`retire of borrowed mark`), because loans must be
returned. Dropping a terminal input without retire fails the exact return
inventory check. Retiring a `moves` handback also fails that check, because
the promised output is missing.

Resource-only handoffs and retirement emit no runtime words: `nachSig` erases
the call inputs and appends exactly the outputs, and `retires` lowers through
the existing ghost statement case. The source-to-IR retirement witnesses are
implemented, pending the lead build. The dynamic escrow replay and the C08
mint software-call/root-once admission remain open; Stage 0 continues to
refuse mint effects and ghost value types at its metadata gate.
