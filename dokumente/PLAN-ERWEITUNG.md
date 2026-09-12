# Library syntax, expansion, bounded memory -- the road to extensions such as GPU kernels

*Written 2026-09-12 after a design discussion with the folder owner. Decisions and order;
nothing is built. Companion to `PLAN-SYSCALL.md` and `PLAN-BITS.md`.*

## 0. The idea, and why it fits Gabbro

A library may bring its own syntax, invoked as `@<library>#<name>`, for example to write GPU
kernels directly. The load-bearing observation: **an expander never needs to be verified,
only its output checked.** If an extension expands into core Gabbro and the ordinary checker
runs over the result, the library is not part of the trusted base -- a wrong library produces
a term the checker refuses. "Every term is a derivation" stays true; not every term is written
by a human any more. This is the architecture `PLAN-UMSETZUNG.md` §1.3 already plans for the
checker (derivation printed, Lean checks it); an expander is one more source of core terms.

Gabbro can enforce what Rust procedural macros cannot: an expander is a Gabbro function with
`effects { pure }` and `decreases` -- a total, effect-free map from AST to AST. Determinism
and termination are a signature, not a convention, and the expansion is an object Lean can
talk about: the certificate says "this source expands to this core term", and Lean re-checks
the expansion without knowing the expander.

## 1. Extension slots, not free mixfix

`@spirv#kernel ( … ) { … }` marks a **delimited region**: up to the matching brace, the named
library parses; the surrounding grammar is unchanged (the Racket `#lang` principle). Free
operator definition in open text is excluded: it makes the grammar depend on load order and
can become ambiguous, which is fatal for a language whose claim is "the grammar is the type
system". Ordinary library functions need no new syntax (`use path`, qualified names exist).

## 2. What the expander works on -- mostly present already

* **Trees as tables:** `table … tree` with `reaches`, `descendants`, `ancestors` exists; an
  AST is a tree table whose children are `option index` fields.
* **Binding structure in the AST type, not in text:** the Lean model already carries
  variables as typed de Bruijn indices (`Var Γ τ`: `hier`/`dort`). An AST data type with the
  same structure is hygienic by construction -- the point where such systems usually fail.
* **Guardians move to the core term:** today's mechanical checks read source text; after
  expansion they run on the core term, plus a separate set on the macro definitions.
* **Error mapping:** a checker refusal in an expanded term must point back to the line in the
  extension syntax. Experience says this is more work than the expander; it is planned as its
  own step, not as an afterthought.

## 3. Bounded memory -- the owner's rule and its three forms

**Rule (owner, 2026-09-12):** a heap is allowed, but never one that grows without bound: every
allocation region carries an upper and a lower bound. The plan fixes WHICH form a region is,
because the forms carry very different proof load:

| form | release | fragmentation | allocation can fail | in Gabbro |
|---|---|---|---|---|
| **arena, monotone, reset as a whole** | only all at once | no | only beyond the upper bound | new -- for compile time and expanders |
| **pool with fixed element size** | per element | no | only when full | **exists**: every `table T count N` with generated `insert`/`remove` |
| general bounded heap | per element, any order | **yes** | also below the upper bound | not built unless a concrete case forces it |

* **Arena = linear mark.** The arena is a linear mark; its reset `consumes` it and `allocs` a
  fresh one. A node is an `index into arena`; an index into a reset arena is not expressible,
  because the reset consumed the mark. **Use after free falls out grammatically, without
  lifetimes.**
* **The lower bound is a reservation.** Allocations statically within the reserved share
  (counted like `costs`) need no `or R`; only the share between lower and upper bound owes the
  error branch. Better still, following `PLAN-BITS.md` §0: bind the capacity structurally to
  the input (`capacity ≥ f(input_size)`, and the expander carries a proved bound
  `nodes_out ≤ f(nodes_in)`), so the check sits at one place -- like `narrow` at entry instead
  of at every index.

## 4. GPU kernels -- where the real boundary is

Two things coincide in the example and must be kept apart:

* **(a) syntax that expands into core Gabbro** -- cheap in the sense of §0; the checker stays
  the last instance, the trusted base does not grow.
* **(b) a library as a second emitter** (SPIR-V, PTX): after it, nothing checks any more.
  "The emitted SPIR-V means what the source means" needs a SPIR-V semantics and a UB
  inventory, as built for C (`BEWEIS.md` §2).

(b) stays inside Gabbro's promise only if a library can **export its hardware assumptions**:
named, listed in the manifest, composable -- the same bookkeeping as `restrict`, `volatile`
and the `syscall` assumptions of `PLAN-SYSCALL.md`, as a library property. Without that
mechanism (b) is a hole with a library label. Two further facts for GPU work:

* **The GPU memory model** (weak, scoped: workgroup/device) is a whole new set of A10-class
  assumptions. Gabbro's lock and rank discipline does not map onto SIMT execution with
  barriers and divergence; this is a concurrency model of its own, not a backend detail.
* **A cheaper intermediate target:** emit a closed subset of OpenCL C (or CUDA C) with a form
  table and a UB inventory, reusing the method that exists for C, instead of a binary format
  with its own semantics.

## 5. Order

1. total, effect-free compile-time evaluation (`PLAN-BITS.md` §6) -- **returning values**
   (tables, trees), not only literals;
2. the compile-time arena of §3;
3. the AST as a Gabbro data type with binding structure (§2);
4. expansion into the core with a certificate, plus error mapping;
5. only then an execution model and a second emitter with exported assumptions (§4).

**Cheap now, in wave 3:** write the compile-time design so it returns values; treat the core
AST from the start as something that may be the output of a program (on the Rust side this is
the planned `Ableitung` datum of `PLAN-UMSETZUNG.md` §1). Both cost almost nothing now and
decide whether this road is open later.
