
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

### Call-scoped owner loans and owned access

```ebnf
effect     += "borrows" name ;
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
