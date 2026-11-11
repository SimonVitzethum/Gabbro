# Zero-cost abstractions without objects — syntax plan

**Status (source audit 2026-11-03): Lean front ends are present for steps 1a–3c, within the
checked domains below.** This replaces the stale “planned, not started” claim; it does not claim
that every planned form reaches a Stage-0 image or that the Rust/Lean pipeline was rebuilt.
Paths are relative to `grammatik/Grammatik/Parser/`; no build was run for this audit.

| Step | Code-derived status | Missing or restricted part |
|---|---|---|
| 1a | Lean front end present: `Stmt/Anweisung/Defs1,Defs2a`, `Elab/Uebersetze/Teil/Teil18` parse/expand `from` and `?`; `Elab/Proben/Spaet/UebersetzeProben42` has expansion witnesses. | No general expression `?`: it is checked call propagation with a matching reason channel; adapter modifier/self/prelude restrictions remain. |
| 1b | Lean front end present and generalized on `syntax-s0` (2026-11-04, needs the lead build): `SourceFolds/Range` expands arbitrary literal integer bounds (upper bound at or below the array length), `min`/`max` with required else, `and`/`or` folds (new `XKind.foldAnd`/`foldOr`, parsed with add-like else rules, printed, resolved and refused on table domains) and nested folds over array variables (inner sums in `u64`, extrema keep the element type, logic folds are Boolean), with the `expandNested_ok` elimination theorem; `BoundsWitness` covers the truncated bound. Closed on `syntax-s0` (needs the lead build): nested folds over table row projections (`T[k].field` expands to a traverse over the table domain with the value type inferred from the row expression; the outer collection skips nested fold subtrees, so collections may differ per level; the elimination theorems cover both domains, with `returnFold_nested_row_zeuge`) and folds outside direct returns (`SourceFolds/Hoist`: `let` bindings and subexpressions hoist to a fresh local accumulator loop before the statement, preserving prefix-before-statement order with the freshness gate; `hoistAnw_shape`, `hoistList_gate`, `hoistAnw_let_zeuge`; direct returns keep the `returnFold` shape; source-text-to-image witnesses cover a hoisted `let` and a row-nested fold). | Symbolic upper bounds below a symbolic length, nested float elements, provider-backed tables and folds in contract/cost clauses, constant initializers, type bounds and traverse/lock headers still refuse with named errors. |
| 2a | Lean front end present: `Spec/{Parse,Items,Contract,Check,Resolve,Walk,Expand,Zeugen}` implements spec/impl, effects and checked conformance. | Conformance is the implemented syntactic contract/effect inclusion check; arbitrary semantic implication is not supplied. Ordinary elaboration/checking of expanded bodies remains required. |
| 2b | Lean front end present: `Elab/Generic/` has arguments, substitution, literals, expansion, static conformance, parametricity and pipeline witnesses; type/const/function arguments and explicit `::[ ]` are represented. Stage-0 gate on `syntax-s0` (2026-11-04, needs the lead build) checks the expanded unit: `Stage0.Frontend.ExpansionGate` runs the canonical expansion and checks the expanded members, with the `expansion_gate` certificate tying acceptance to the elaborated unit; source-text-to-image witnesses cover one generic function at two instantiations. | Unsupported abstract operations and unbound generic library translators refuse; this is instantiate-before-G, not a universal parametric-body theorem. Check model B (a generic body checked once in G) remains future work. |
| 2c | Lean front end present: `Elab/Modules/{Shape,Substitution,Expansion,Frontend}` plus witnesses expands generative module uses, with freshness/closure/output checks. Stage-0 gate on `syntax-s0` (2026-11-04, needs the lead build) accepts expanded instances; source-text-to-image witness covers one module instantiated twice. | No complete container library is established by these frontend files; row-projection and provider-backed modules still refuse. |
| 3a | Lean front end present: `TaggedDispatch/{Signature,Resolve,Expressions,Expansion,Frontend}` and source witnesses expand `tagged … by S`. Stage-0 gate on `syntax-s0` (2026-11-04, needs the lead build) accepts the expanded dispatchers; source-text-to-image witness covers a two-case dispatch. | Only checked dispatch signatures/payloads and ordinary output forms are admitted; Stage-0 sum payload/metadata limits still apply. |
| 3b | Lean front end present: `Dyn/{Collect,Closed,Rewrite,Frontend}` and source witnesses close linked implementations into tagged dispatch. Stage-0 gate on `syntax-s0` (2026-11-04, needs the lead build) accepts the expanded closed sums; source-text-to-image witness covers a `dyn` call with two linked implementations. Closed on `syntax-s0` (needs the lead build): payloads of any size and shape (scalar, wide, aggregate, aliased) are carried through the closed sum into the existing tagged sum layout — the scalar/8-byte gate is removed, with `scene_wide_payload_closed_zeuge`, `scene_alias_payload_closed_zeuge` and `scene_wide_payload_accepted_zeuge`. Lowering premise (Stage 0, branch s0-gaps1): sum payloads beyond one word lower through `sumPayloadWords`/`sumOff` and the `encodeWords` sum branch. | This code uses closed sums, not the proposed `Ty.dyn` extension. Downcast/equality/implementation tests and unsupported bound conversions refuse by design; unrestricted dynamic linking is missing. |
| 3c | Lean front end present: `Elab/Generic/PointerTypes`, `Signatures.vertragPasstB/vertragPasstAt/passtAt` share C06/O43 contract inclusion with static function arguments. | Conjunct inclusion compares written predicates (including names); arbitrary implication and positional normalization are not supplied here. This header does not establish the planned generic call/goal proof by frontend presence alone. |

The owner decisions of 2026-11-02 and the intended scope below remain the design reference;
the table records code already present, independently of the historical implementation order.

Every form below follows §3 of `AGENTS.md`: the Lean model first (front end, exporter, the generic theorem of
the desugaring, or the G extension with `gabbro_ziel` on the standard axioms), then the Rust checker and
compiler, then `SYNTAX.md` and `LANGUAGE.md`. Every new refusal gets its code (next free `N`, re-measured),
its sentence in `saetze.rs` and a poison probe in the same commit.

---

## 1. Principles: Gabbro does not become object-oriented

1. **No methods, no receiver, no `this`/`self`, no dot calls** (the existing `.is_some` stays the one exception).
   Behaviour lives in free functions, data in tables and types.
2. **No inheritance, no subtyping, no class hierarchy, no downcast.** Polymorphism comes from **spec groups**
   (type classes over types, not over objects) and from **sums** — closed (`tagged … by`) or link-time closed (`dyn`).
3. **The unit of encapsulation is the module** (`opaque`, `pub`), never a class.
4. **Data-oriented:** an "object" is an index into a table, not a pointer to a record with a vtable.
5. **Static first:** desugaring, monomorphisation and inlining before machine G. `dyn` is the one form with a
   run-time dispatch, and it is spelled at every place that pays for it.
6. **Contracts are never derived.** Every function an adapter or an instantiation produces carries contracts
   the writer wrote; the rule "never derive `ensures`" stands.
7. **The vocabulary stays closed:** exactly **one** new word, `dyn` (248 → 249). Everything else reuses
   existing words (`from`, `spec`, `impl`, `by`, `add`, `min`, `max`, `exists`, `const`, `module`, `use`,
   `effects`) or adds punctuation (`..` in parameter and field lists, `-name` in adapter lists, `?`, `::[`).

Two facts of the current model shape the design:

- **Records are not values** (former work item O15, `LG002`). Generic values are integers, floats, `bool`, sums,
  indices, reasons and `fnptr`; a structure travels as `ptr<…> T` or as an index.
- **Function-pointer types carry no contract** (`N589`, O43). `dyn` does not depend on O43 (§6.2); O43 itself is
  planned in §6.3.

## 2. Map: object-oriented idiom → Gabbro form

| Idiom | Gabbro | Phase |
|---|---|---|
| class with private fields | module + `opaque type` + table + `invariant` | exists |
| constructor | `fn` with `ensures` returning an `opaque` value or an index | exists |
| exceptions, `throws` | `or R` channel; `?` propagation | exists / 1 |
| iterator, stream, LINQ | `count`, `add`, `min`, `max`, `exists` over a domain | exists / 1 |
| `extends` to vary code | adapter `fn … from f` | 1 |
| `extends` to add data | embedding `{ ..A, … }` | 1 |
| interface, abstract method | `spec S[T] { … }` + `impl S[X] { … }` | 2 |
| generics, templates | `fn f[T: S](…)`, instantiated | 2 |
| strategy, callback, lambda | static function parameter `[g: fn(…) …]` + function literal | 2 |
| generic collection | parametric module `module stack[T, N: const u32]` | 2 |
| virtual method, closed set | `tagged type … by S`, generated `match` | 3 |
| virtual method, open set | `dyn S`, link-time closed sum, vtable in the image | 3 |
| callback stored in data | contract-carrying `fnptr` (O43) | 3 |
| GC, reflection, operator overloading, subtyping | **not in Gabbro** (§7) | — |

## 3. Lexis and grammar conventions

- **Square brackets after a name are compile-time parameters**: `fn f[…]`, `spec S[…]`, `impl S[…]`,
  `module m[…]`. At a use site they are written `::[ … ]` (`f::[u32](x)`) and are optional wherever the
  value arguments determine them. The existing `type X(T)` form for parameters of types stays as it is.
- `..` inside a parameter list (adapter) or a field list (embedding) means "all of the named source".
- `-name` inside an adapter parameter list removes one parameter of the source.
- `?` directly after a call in binding or statement position propagates the reason channel.
- `dyn` is the one new reserved word; it opens a type (`dyn S`) and a producer expression (`dyn S(e)`).
- A new constructor of `Expr`, `Stmt` or `Ty` in the Lean model goes at the END of its inductive (`AGENTS.md` §9).

---

## 4. Phase 1 — pure desugaring (machine G unchanged)

### 4.1 Adapter: `fn … from f`

```ebnf
fndecl     += adaptfn ;
adaptfn     = [ "pub" ] "fn" ident "(" adaptparams ")" [ "->" typeexpr ] [ "or" ident ]
              "from" path [ "::[" garglist "]" ]
              [ "=>" ident [ "else" "(" ident ")" endblock ] ]
              [ "requires" predlist ] [ "ensures" predlist ]
              [ "effects" "{" efflist "}" ] [ "costs" "<=" expr "ops" ]
              [ "[" { stmt } "]" ]                         (* prelude, runs before the call *)
              ( endblock | ";" ) ;
adaptparams = adaptparam { "," adaptparam } ;
adaptparam  = ".."                                         (* every parameter of f, in f's order *)
            | "-" ident                                    (* this parameter of f is not taken over *)
            | ident ":" typeexpr ;                         (* a new parameter *)
```

```gabbro
fn scaled_area(.., -scale, factor: u8 in 1 .. 16) -> u64
    from area => a
    ensures result >= 1
    effects { reads Circles } costs <= 60 ops
    [ let scale = factor * 2; ]
{ return a + 1; }

fn area_x4(.., -scale) -> u64 from area [ let scale = 4; ];      // `;`: returns f's result as it is
```

**Desugars to** an ordinary function:

```gabbro
fn scaled_area(c: index into Circles, factor: u8 in 1 .. 16) -> u64
    ensures result >= 1 effects { reads Circles } costs <= 60 ops
{
    let scale = factor * 2;
    let a = area(c, scale);
    return a + 1;
}
```

Rules (each a named refusal):

1. `..` at most once; `-x` only for a parameter `f` has; no name twice after expansion.
2. The prelude binds every removed parameter with `let`, exactly once on every path; it may `return` early
   (the return type and channel are `g`'s).
3. `f` is a black box: `g` sees `f`'s signature and contract, never its body. At the call `requires(f)` is an
   ordinary obligation; in the body `ensures(f)` over the bound result is an assumption.
4. Reason channel: if `f` has `or R` and `g` has the same `or R`, the error propagates; otherwise
   `else (e) endblock` is required.
5. The short body `;` only when `g`'s result type equals `f`'s; the bound name is then not needed.
6. `requires`/`ensures` are written by the writer (never derived). `effects` and `costs` may be omitted: they
   are then the computed sum of prelude, `f` and body — the same computation that checks a written budget.
7. Refused: `f` is `divergent`, `spec`, the adapter itself, or reachable from the adapter's own prelude.

### 4.2 Embedding of fields

```ebnf
structty = "{" { field | embed } "}" ;
embed    = ".." path "," ;
```

```gabbro
type Pos  = { x: i32, y: i32, };
type Body = { ..Pos, mass: u32 in 1 .. 1000, };        // = { x: i32, y: i32, mass: u32 in 1 .. 1000, }
```

- The fields of the embedded type are inserted flat, in order, with their `where`, `@` and `reserved`.
- A field name twice after expansion is refused; embedding a type that embeds the outer one is refused.
- **No view `Body → Pos`**, no conversion, no subtyping: a write through such a view could break an invariant
  of `Body` over the fields of `Pos`. Code over `Pos` is reused through a spec group (§5.1) or an adapter.

### 4.3 Reason propagation `?`

```ebnf
letstmt  += "let" [ "mut" ] ident [ ":" typeexpr ] "=" call "?" ";" ;
exprstmt += call "?" ";" ;
```

- Allowed only when the enclosing function has the SAME reason channel `or R` as the callee.
- Desugars to `let x = f(…) else (e) { match e { F1 => { return R::F1; } … Fn => { return R::Fn; } } };`
  with one arm per ground of `R` (exhaustive by shape, `M123`).
- Different reasons keep the written `else`; there is no implicit mapping between reasons.

### 4.4 Folds over a domain and `exists` as an expression

```ebnf
primary   += foldexpr | existsexpr ;
foldexpr   = ( "add" | "min" | "max" ) ident "in" domain [ "where" pred ] ":" expr
             [ "else" expr ] ;                               (* `else` required for min and max *)
existsexpr = "exists" ident "in" domain ":" pred ;
returnstmt += "return" "add" ident "in" "0" "..<" expr [ "where" pred ] ":" expr ";" ;
```

```gabbro
let open_sum = add k in slots of Orders where Orders[k].open : Orders[k].amount;
let worst    = max k in slots of Jobs : Jobs[k].latency else 0;
if exists k in slots of Jobs : Jobs[k].failed { … }
```

- Over ONE table, like `count` («SG-24»); desugars to a generated `traverse` with an accumulator variable;
  `exists` leaves early (`leave`).
- `add` over integers: the result range is `capacity · hi` (and `capacity · lo`); a range that does not fit the
  result type is refused — the writer narrows first. There is no wrapping fold (wrapping stays `+%`).
- `add` over floats folds in slot order (IEEE: no reassociation); the order is part of the meaning.
- `costs` is capacity × per-element cost plus the loop overhead, computed statically.
- The §5.2 `total` example additionally uses a full-array range: `return add i in 0 ..< N : e`.
  Its indexed array must have declared type `[T; N]`, with the same symbolic upper bound;
  this expands before instantiation to `traverse i over elems of xs by unvisited` and an
  explicitly typed integer accumulator. The operand's call is bound inside the traversal,
  so normal spec resolution can select the implementation. The ordinary checks retain
  overflow, effect, contract and cost obligations; no range or budget fact is assumed.
  Other range-fold contexts are refused. This is source sugar over existing forms and
  does not change machine G, `Akzeptiert` or the meaning of `Spec.lean`.

---

## 5. Phase 2 — spec groups, generics, parametric modules (check model A)

### 5.1 Spec groups and implementations

```ebnf
item      += specdecl | impldecl ;
specdecl   = [ "pub" ] "spec" ident "[" ident { "," ident } [ ";" effparams ] "]"
             "{" { specfn } "}" ;
effparams  = "effects" ident { "," ident } ;                (* effect parameters, owner 2026-11-02 *)
specfn     = "fn" ident "(" [ params ] ")" [ "->" typeexpr ] [ "or" ident ]
             [ "requires" predlist ] [ "ensures" predlist ]
             "effects" "{" efflist "}" "costs" "<=" expr "ops" ";" ;
impldecl   = "impl" ident "[" typelist [ ";" effargs ] "]" "{" { fndecl } "}" ;
effargs    = "effects" "{" efflist "}" { "," "{" efflist "}" } ;
efflist   += ident ;                                         (* an effect parameter inside a spec *)
efflist   += ident "[" typelist "]" ;                        (* the effects of an instance: `Shape[T]` *)
call      += path "::" ident [ "::[" garglist "]" ] "(" [ arglist ] ")" ;   (* `Shape::area(c)` *)
```

`spec S[` and `impl S[` are told apart from `spec fn` and `impl fn` by the token after the word.

```gabbro
spec Shape[T; effects E] {
    fn area(s: T) -> u64 ensures result >= 1 effects { E } costs <= 50 ops;
}

impl Shape[index into Circles; effects { reads Circles }] {
    fn area(s: index into Circles) -> u64 ensures result >= 1 effects { reads Circles } costs <= 20 ops {
        return 3 * Circles[s].r * Circles[s].r + 1;
    }
}

let a = Shape::area(c);                       // T from the argument; explicit: Shape::area::[index into Circles](c)
```

**Conformance** (decidable, a Bool of the checker; the same rule serves `dyn` and O43):

- after substituting the instance (types and effect arguments) into the spec function:
  every conjunct of `requires(impl)` occurs in `requires(spec)` (the impl asks for no more), and every
  conjunct of `ensures(spec)` occurs in `ensures(impl)` (the impl promises no less) — inclusion of normalised
  predicate lists, the mechanism `refines` already uses;
- `effects(impl) ⊆` the substituted `effects(spec)`; `costs(impl) ≤ costs(spec)`;
- no `Held(L)` in a spec function (no lock crosses an abstract call, as `N036` at a pointer);
- every spec function implemented, nothing else in the `impl`; at most one `impl` per spec and type tuple in
  the whole linked program; no overlap, no specialisation, no default bodies (a default is an adapter or a
  generic function over the spec).

A later extension may discharge general implications (`requires(spec) → requires(impl)`) as user logic in
`LogikPflicht`; the syntactic inclusion is the first and sufficient rule.

### 5.2 Generic functions, constant parameters, static function parameters

```ebnf
fnhead    : "fn" ident [ "[" gparams "]" ] "(" … ;          (* extends the head of every fndecl *)
gparams    = gparam { "," gparam } ;
gparam     = ident [ ":" ident { "+" ident } ]             (* a type with spec bounds *)
           | ident ":" "const" typeexpr                    (* a value known at translation time *)
           | ident ":" fnptr ;                             (* a static function parameter *)
call      += path "::[" garglist "]" "(" [ arglist ] ")" ;
garglist   = garg { "," garg } ;
garg       = typeexpr | constexpr | path | fnlit ;
fnlit      = "fn" "(" [ params ] ")" [ "->" typeexpr ] fncontract endblock ;
```

```gabbro
fn total[T: Shape, N: const u32 in 1 .. 4096](xs: [T; N]) -> u64
    effects { Shape[T] } costs <= N * 60 ops
{ return add i in 0 ..< N : Shape::area(xs[i]); }

fn apply_all[g: fn(u32 in 0 .. 1000) -> u32 effects {} costs <= 8 ops]()
    effects { writes Vals } costs <= 40960 ops
{ traverse k over slots of Vals by unvisited { Vals[k].v = g(Vals[k].v); } }

apply_all::[fn(x: u32 in 0 .. 1000) -> u32 effects {} costs <= 3 ops { return x * 2; }]();
```

- **Parametricity:** a value of a type parameter can be passed, bound and handed to the spec functions of its
  bounds; nothing else (no arithmetic, no comparison, no field), as with `opaque`.
- **Static function parameters replace closures.** After instantiation `g(…)` is a DIRECT call checked
  against the argument's own signature, so `N589` does not apply and nothing is paid at run time. The
  argument must conform to the parameter's `fnptr` type (`SigPasst`; with O43 also its contract).
- **Function literals capture nothing:** a free name inside a literal that is not a global item is refused.
  State travels as an explicit parameter.
- **Finiteness:** the set of instances is computed as a fixpoint; polymorphic recursion and an instance that
  produces a growing type form are refused.

### 5.3 Parametric modules

```ebnf
moduledecl += [ "pub" ] "module" ident "[" gparams "]" "{" { item } "}" ;
usedecl    += [ "pub" ] "use" ident "=" path "::[" garglist "]" ";" ;
```

```gabbro
module stack[T, N: const u32 in 1 .. 65536] {
    table Items count N { slot { v: T, } }
    static top: u32 in 0 ..= N;
    pub fn push(x: T) or Full  effects { writes Items, writes top } costs <= 12 ops { … }
    pub fn pop() -> T or Empty effects { reads Items, writes top } costs <= 10 ops { … }
}

use Jobs = stack::[index into Tasks, 64];
Jobs::push(t)?;
```

- Every instance is its own set of tables, statics and functions (ML functors, no classes).
- The standard library's containers (stack, queue, ring, map over arenas and open regions) are written this
  way in Gabbro and checked like user code.

### 5.4 Check model A

1. The front end instantiates in this order: parametric modules → generic functions → spec calls → function
   literals become named functions. The result is an ordinary program; G and `Akzeptiert` run unchanged on it.
2. Lean: the instantiation function in the elaborator, a generic theorem that its output is well-formed and
   uses only existing forms, and a `_zeuge` on a non-degenerate fixture.
3. Soundness does not depend on conformance: every instance is checked against the real contracts of its
   implementation. Conformance gives modularity, stable interfaces and early, precise refusals.
4. Rust instantiates identically (a difference is a checker bug); Stage 0, IR and LLVM need nothing new.
5. Measure check time per instance and code size. Model B (a generic body checked once inside G) only if the
   measurement asks for it.

---

## 6. Phase 3 — dispatch

### 6.1 Closed: `tagged … by S`

```ebnf
typedecl += [ "pub" ] "tagged" "type" ident "=" variants "by" ident ";" ;
```

```gabbro
tagged type AnyShape = { C(index into Circles), R(index into Rects) } by Shape;
let a = Shape::area(s);                       // s : AnyShape
```

- Generates `impl Shape[AnyShape; effects { … union of the cases … }]`, one `match` per spec function with
  one arm per case calling the case's implementation.
- **Dispatchable spec function:** exactly one parameter of type `T`, `T` not in the result, no `Held`.
  Non-dispatchable functions, including constructors returning `T` by value, remain static and
  do not block `by`; only dispatchable functions require a case implementation for dispatch.
  A call to a non-dispatchable member through the tagged group is refused by name.
- Cost: one branch on the case number; no table of addresses, no heap.

### 6.2 Open: `dyn S` — a sum closed at link time

```ebnf
typeexpr += dynty ;
dynty     = "dyn" ident [ "effects" "{" efflist "}" ] ;       (* required when S has effect parameters *)
primary  += dynexpr ;
dynexpr   = "dyn" ident "(" expr ")" ;                       (* producer: the argument's type has an impl of S *)
```

```gabbro
table Scene count 256 { slot { s: dyn Shape effects { reads Circles, reads Rects }, } }

Scene[i].s = dyn Shape(c);                    // c : index into Circles
let a = Shape::area(Scene[j].s);              // dispatched call
```

**Meaning.** A value of `dyn S effects B` is a pair (implementation, payload): one of the implementations of
`S` in the WHOLE linked program whose effects lie in `B`, and a value of that implementation's type. A call of
a dispatchable spec function on it is the call of that implementation's function. Within one program this is
a sum whose cases are known only at link time — open for the writer of a unit, closed for the statement.

**Rules.**

- The payload type of every implementation used with `dyn` is a value type of at most 8 bytes (index,
  integer, `opaque`, reason, `bool`, float, `option index`) — a uniform two-word value, no heap, no boxing.
- Only dispatchable spec functions are callable on a `dyn` value; the spec's conformance (§5.1) covers
  every implementation; the effects of a call are `B`, its costs the spec's plus a fixed dispatch constant.
- No downcast, no test of the implementation, no equality on `dyn` values (no reflection).
- `dyn` values are ordinary values: in tables, parameters, results and lets; shared carriers keep every rule.

**Model (G change, Lean first).**

- A new `Ty.dyn S B` at the END of `Ty`; its value is a dependent pair of an implementation index of the
  linked program and a value of that implementation's type.
- The call is the case analysis on the index followed by the direct call — the same proof shape as a `match`
  over a sum. `Akzeptiert` gets the conformance Bool and the payload-size rule.
- Linking: implementation indices are assigned by `GabbroZielVerbund`; a single unit is checked against the
  implementations it can see plus the spec contract for the rest (that is exactly what conformance buys).
- `gabbro_ziel` re-proved on the standard axioms; the commit describes the change of meaning of `Spec.lean`
  (machine G gains a type; no premise weakened).

**Lowering.** One read-only table of function addresses per (spec, implementation) in the image; the value is
two words (implementation number, payload); a call is a load and an indirect call. The lowering theorem shows
that the table call equals the model's case analysis; the table's contents are validated with the image.

### 6.3 Contract-carrying function pointers (O43)

- Lifts `N589`: a `fnptr` type may carry `requires` and `ensures`. `&f` conforms when `SigPasst` holds and the
  contract inclusion of §5.1 holds (requires contravariant, ensures covariant, effects ⊆, costs ≤).
- A call through the pointer is checked against the type's contract; the conformance proof travels with the
  value (`{f // D.passt f sig = true}` gains the contract part).
- Model change in `SigPasst`/`Deklaration.passt` and the indirect call rule; `gabbro_ziel` re-proved.
- Independent of `dyn`; useful for callbacks stored in data where no spec group exists.

---

## 7. Deliberately not in Gabbro

Inheritance; subtyping (also no view `B → A`); methods and receivers; overloading by type outside spec
groups; operator overloading; closures with captured environment; specialisation and overlapping
implementations; default bodies in specs; downcast and reflection; GC; exceptions; implicit conversion;
`defer` (linear marks already force the release, and a hidden release does not fit the
explicit style). §15 of `SYNTAX.md` stands as it is. `async fn`/`.await` is separate work
(a verified state-machine transformation), not part of this plan.

## 8. Work order and obligations

| Step | Forms | Model | Lean part | Size |
|---|---|---|---|---|
| 1a | adapter `from`, `?` | desugaring | elaborator export + desugaring theorem + witness | small |
| 1b | embedding, folds, `exists` expression | desugaring | as 1a | small |
| 2a | `spec`/`impl`, effect parameters, conformance | desugaring + checker Bool | conformance in `Akzeptiert`-side front end | medium |
| 2b | generics, `const` and function parameters, literals, `::[ ]` | instantiation (A) | instantiation function + theorem + witness | medium–large, **critical path** |
| 2c | parametric modules, first library containers | instantiation | as 2b | medium |
| 3a | `tagged … by S` | desugaring | as 1a | small (after 2a) |
| 3b | `dyn S` | **G extension** | `Ty.dyn`, call rule, linking, `gabbro_ziel` | large |
| 3c | O43 | **G extension** | contract in `SigPasst`, indirect call | medium–large |

Rough estimate: phase 1 is 2–4 agent rounds, phase 2 6–12, 3a 1–2, 3b 6–10, 3c 4–8. The critical path is
2a → 2b → 3b. Every step: Lean first, then Rust parser and checker (identical desugaring), `SYNTAX.md` and
`LANGUAGE.md` (vocabulary +1 at 3b), refusal codes with sentences and poison probes, positive examples.

---

## 9. After the forms: diagnostics for known slow code

**Goal.** The compiler reports code it KNOWS is slow and may not make fast by itself, with the measured
reason and the concrete cheaper source form. Purely informative: a diagnostic never changes acceptance,
semantics, the image or the exit status, and no existing refusal becomes a diagnostic.

### 9.1 When a diagnostic fires (all three conditions)

1. **A cost fact the tool chain already has**: the static op count of the checker (the same computation that
   checks `costs`), a fact of the emitted IR (an indirect call, a check left inside a loop), or a missed
   optimisation reported by LLVM (`-pass-remarks-missed`) mapped back to the source through debug locations.
2. **A hot context**: inside a `traverse`, `retry`, `forever` pass or fold, or contributing at least 25 % of
   the enclosing function's computed costs (threshold configurable in the build file).
3. **A cheaper form exists that the compiler may not pick itself** because it needs something only the writer
   can state: a new carrier with an invariant, a different float result, a declared layout, a lock hold
   time, an effect order, a contract. The diagnostic names that form.

### 9.2 Catalogue (codes from the next free `W`, re-measured; today `W004`)

| Code | Trigger | Why not automatic | Suggested form |
|---|---|---|---|
| W004 | traversal or fold over `slots of T` with a `where` filter, large capacity | an index is a new carrier with an invariant | a `group`-maintained subset table or a `tree` |
| W005 | nested traversals joined on equal fields, O(n·m) | same | an index table keyed by the join field |
| W006 | `count`/`exists` over the same table inside a loop | a running count is a `group` invariant the writer declares | `group` invariant («SG-24») |
| W007 | a `narrow`/`where`/bounds check repeated per iteration on a loop-invariant operand | the invariant is not provable from the declarations | `narrow` before the loop or a loop `invariant` |
| W008 | float `add` fold or float accumulation in a loop, not vectorisable | IEEE order is part of the result | an explicit blocked reduction (different result, the writer's choice) or fixed point |
| W009 | `dyn` call in a hot loop over values of one implementation | the set of implementations is open | a generic `[T: S]` or `tagged … by S` |
| W010 | indirect `fnptr` call in a hot loop, not inlinable | the callee is a value | a static function parameter |
| W011 | `locks L` taken per iteration | the hold time is lock discipline | one `locks L` around the loop |
| W012 | `seq` atomic in a hot loop | weaker orders are the writer's protocol proof | `acquire`/`release` where the protocol allows |
| W013 | a packed bit field (`@ bitpos`) written in a hot loop (read-modify-write) | the layout is declared | an unpacked field or a staging table |
| W014 | `syscall`, `extern` or library call in a hot loop | effects fix the order and number of calls | a batching interface of the binding |
| W015 | instantiation blow-up (instances or code size over the configured bound) | monomorphisation is the meaning of `[T]` | `dyn S` or fewer type parameters |
| W016 | `grow` of an arena inside a loop | the commit point is the writer's | one `grow` before the loop |
| W017 | non-tail recursion with a large `decreases` bound | stack depth is the writer's | a `traverse`/`retry` form |
| W018 | an LLVM missed vectorisation whose remark names a source cause (early `leave`, non-unit stride, possible alias) | the cause is a source decision | the form the remark points to |

### 9.3 Output and control

```
warning[W004]: filtered traversal over `Orders` (count 65536)
  --> src/orders.gb:41:5
   = cost: 65536 iterations × 7 ops = 458752 ops, 93 % of `close_all` (budget 500000)
   = not automatic: an index on `open` is a new carrier with an invariant you declare
   = try: a subset table `OpenOrders` kept by a `group` invariant (SYNTAX.md §9)
```

- Shown by `gabbro pruefe` and `gabbro build`; `--slow=off|warn|deny` (`deny` fails the build at the user's
  choice — a warning made stricter, never a refusal made weaker).
- **No source syntax:** suppressions live in the project's build file (`BUILD-SYSTEM.md`), each with a code,
  an item path and a mandatory reason; a suppression that no longer matches is itself reported.
- Deterministic and static: no run-time profile (a profile-fed mode over the assembly runner is a later option).

### 9.4 Obligations

- Rust only (`crates/gabbro-check` for the static facts, `gabbro build` for the IR facts and LLVM remarks);
  no Lean model change, off the trust path. The cost numbers come from the checker's `costs` computation, and
  a test holds them equal to it.
- Every code: its sentence in `saetze.rs`, a positive example that fires and a negative example that must stay
  silent; generic analyses only (nothing for particular programs).
- Order: W004–W008, W011–W014, W016–W018 need none of the new forms and can start right after the C packages;
  W009, W010 and W015 follow phases 2 and 3.

## 10. Open questions

1. Payload of `dyn`: is 8 bytes enough, or should 16 bytes (two words, e.g. index plus generation) be allowed?
   Recommendation: 8 now; 16 when a container needs generation-checked handles.
2. Spec costs: fixed bounds only, or costs over the spec's `const` parameters? Recommendation: both, with the
   same expression language as `costs` today.
3. Hot-context threshold for §9: 25 % of the function's computed costs as default. Recommendation: keep, measure
   the noise on the corpus before the first release.
