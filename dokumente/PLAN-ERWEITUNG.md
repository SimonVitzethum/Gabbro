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

## 0b. Decision (owner, 2026-09-12): executed at run time, checked at translation time

`@<library>#<function> ( args ) { region }` is a **run-time call** of `<function>` in
`<library>`. The region is read and checked when the program is translated; at run time the
program calls the library -- for a GPU kernel, the launch through the driver. So:

* **At translation time** the library's declared *translator* (a pure, total Gabbro function,
  as the expander of §0) turns the region into a **payload**: a value of a payload type the
  library declares (for a kernel: a descriptor table, or the kernel code in a closed target
  subset). The checker checks that the payload is a well-typed value of that type. The
  translator is not trusted; a wrong translator produces a payload the checker refuses.
* **At run time** the call is a library call with a contract (`requires`, `ensures`,
  `effects`), exactly like a foreign body or the `syscall` construct of `PLAN-SYSCALL.md`:
  in Lean a call whose arguments include the payload. By §0c the library function is safe
  Gabbro with a proved contract, so the call is an ordinary proved call; what remains are the
  hardware assumptions the library requires from the program's profile.
* **The verification reaches the hand-over:** arguments, payload type, contract and effects at
  the call are checked; the library's run-time behaviour is the assumption it exports.

**Gabbro code is always compiled at translation time, never at run time (owner, 2026-09-12,
clarified the same day).** Everything the program does is fixed when it is translated: no
Gabbro source, region or AST is compiled, generated or interpreted while the program runs. The
payload of a region is fully produced at translation time; at run time the library only
executes or launches it. **What the program does at run time is unrestricted within that
rule** -- open TCP connections, read files, launch GPU work -- provided the code doing it was
fixed at translation time; the DATA is dynamic, the code is not.

Consequence for GPU payloads: a portable intermediate format (SPIR-V, PTX) is **admitted**.
Gabbro produces it at translation time from a kernel written in Gabbro; that the driver lowers
it to the GPU's instruction set when it is loaded is the driver's step, not a compilation of
Gabbro code. That step is a **named assumption** of the hardware profile (§0c) -- "the driver
compiles this SPIR-V version faithfully", keyed by API and SPIR-V version, with its falsifier
probe -- in the same class as trusting the C compiler, the CPU's decoder or the kernel behind a
`syscall`. A native binary for one fixed GPU (for example a CUDA cubin) stays possible and
removes that assumption at the price of portability.

Compile-time expansion of regions into core Gabbro (§0) stays possible as a later form, but it
is not what `@lib#func` means.

## 0c. Decision (owner, 2026-09-12): a library function is always safe Gabbro, with no hardware assumption contradicting the main program

**Why this is load-bearing:** contradictory assumptions make every proof over the combined
program vacuous -- from a contradiction everything follows. That is the defect class the
first two agent waves found again and again (premises that no ordinary program can satisfy),
here at the level of hardware assumptions. Consistency is therefore enforced **by structure**,
never by comparing prose.

1. **Safe Gabbro only.** A function reachable through `@lib#func` is Gabbro code checked by the
   same checker; its contract is proved like any other. Foreign bodies (`extern`, `raw`,
   `prim`, `asm`) are refused anywhere in its call hull. A library that must reach hardware does
   so through Gabbro constructs -- `syscall` (`PLAN-SYSCALL.md`), `device`/`reg`, `atomic` --
   whose assumptions are named. The library's run-time behaviour is then covered by the proof;
   what remains are its declared hardware assumptions, handled by points 2-4.
2. **One hardware profile per program.** The main program declares the profile: the one set of
   hardware assumptions the whole program runs under (target arch, memory-model assumptions,
   FP environment, device assumptions, ...). A library does not ASSERT assumptions; it REQUIRES
   profile entries, by reference to the declared assumption, never by a copy of its text.
   Linking refuses a library whose requirements are not in the profile -- the main program
   must add them to its profile, where they meet everything else. **Consistency becomes a
   subset check against one set**, decidable and cheap.
3. **Keyed assumptions for modes and resources.** An assumption that fixes a mode or a
   resource names its key and value (FP rounding mode, FP contraction, memory-model mode,
   interrupt routing, arch). Two entries with the same key and different values are refused
   at the profile itself. A same-named assumption with a different statement or class is
   refused.
4. **Exclusivity by linearity.** Device and register access reaches a library only as a
   linear capability (an owner mark, `D.eigner`); two components cannot both assume exclusive
   ownership of one device, because the mark exists once (`eigner_nie_erzeugt`).
5. **In Lean:** the program theorem takes ONE assumption set, the profile; a library's set is
   required to be a subset, so linking adds no premise. For keyed mode assumptions with
   pairwise distinct keys, a theorem constructs a model (an oracle satisfying all of them) --
   the profile is satisfiable by construction, not merely unrefuted. Free-prose assumptions
   carry their falsifier probe as today.

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
* **Target: SPIR-V emitted directly, not through OpenCL C (review, 2026-09-12).** The OpenCL C
  route reuses the C tooling but not the C proof load: OpenCL C has undefined behaviour of its
  own with no reference comparable to the C standard to inventory it against; the Clang path
  OpenCL C → SPIR-V is far less exercised than the C path; the prelude method (`_Static_assert`,
  probes) cannot reach into it; and it puts two semantic gaps in a row (Gabbro → OpenCL C →
  SPIR-V → driver) of which the profile assumption covers only the last. Direct emission of the
  G1 subset is small. **Measured here:** a complete G1 kernel (`out[gid] = in[gid] * 3 + 1` on
  `u32`, with its bounds guard, two storage buffers, `NonWritable`/`NonReadable`) is **29 distinct
  opcodes, 760 bytes**, assembled with `spirv-as` and accepted by `spirv-val --target-env
  vulkan1.1`. Bounded loops (`OpLoopMerge`, `OpPhi`), floats (`OpFAdd`/`OpFMul` with
  `NoContraction`), signed operations and conversions bring it to roughly 40-50. The format is a
  word stream with a fixed header and no relocations.
* **The payload is validated by Gabbro's own validator** (structure: header, ids defined before
  use, types, storage classes, the closed opcode set of the G1 subset). It checks shape, not
  meaning; `spirv-val` (pinned version, manifest) runs as a second, independent check at build
  time. The lowering's correctness is stated against a semantics of the G1 subset only -- small
  because the subset is small -- and the driver's step is the profile assumption of §0b.

### 4a. GPU kernels written in Gabbro -- staged (owner question, 2026-09-12)

Gabbro's existing restrictions fit a GPU unusually well: no recursion, bounded loops, no
unbounded allocation, sized tables. What is new is the concurrency model. The stages differ in
proof load by an order of magnitude each, so they are separate decisions:

| stage | kernel form | race freedom by | new proof load |
|---|---|---|---|
| G1 | **map**: each invocation reads anything read-only and writes only its own output cell | construction (`PLAN-BITS.md` §0, option 2) -- see the two conditions below | the direct SPIR-V lowering of the subset with its validator, FP environment keys (denormals via float-controls execution modes, contraction via `NoContraction`), host launch contract |
| G2 | **fixed patterns**: reduction, scan, histogram as library kernels proved once | the pattern's proof, done once in the library | one proof per pattern |
| G3 | **free kernels** with workgroup memory, barriers, scoped atomics | a SIMT memory model with barrier divergence -- research grade (compare GPUVerify, VerCors) | a concurrency model of its own |

**G1 is race-free only under two conditions, both structural:**

1. **The own cell is a form, not an index.** The write target is written `out.mine` (spelling
   open): a construct bound to the invocation id, with no index expression at all. An ordinary
   indexed write `out[e]` is not admitted in a G1 kernel, even when `e` happens to be `gid` --
   otherwise `out[gid % n]` looks the same and races. The error class disappears only because the
   wrong form cannot be written.
2. **Input and output buffers are disjoint.** Otherwise one invocation reads what another writes,
   although each writes only its own cell. In Gabbro this is an aliasing statement over two
   distinct linear marks, so it is expressible; the launch contract requires it, and the lowering
   emits `NonWritable` on inputs and `NonReadable` on outputs (as in the measured kernel).

**Recommendation:** G1 is worth it and fits the structure of §6 (payload = SPIR-V produced by
the translator at translation time, launch = run-time library call with a contract). G2 follows
naturally. G3 is not planned. None of it comes before the verification core closes; the
structure lanes of §6 keep the road open.

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

## 6. Scope for the next wave: the structure only (owner decisions, 2026-09-12)

**Only the structure that makes run-time library calls with checked regions possible is built
-- no GPU backend, no concrete translator, no second emitter.** Each lane gets a fixed
deliverable; "done" means the mechanism exists, is checked, and has one minimal example plus
poison probes.

| # | lane | deliverable | depends on |
|---|---|---|---|
| E1 | call syntax | `@<library>#<function> ( args ) { region }` in `SYNTAX.md` as a call in statement and binding position -- **guardian patterns first** (vocabulary, grammar table), then the document; the parser captures the region as a brace-balanced token tree without interpreting it; poison probes: unbalanced region, unknown library, unknown function | -- |
| E2 | library function declaration | a library declares a run-time function with a contract and a PAYLOAD TYPE; the call is checked like any call (arguments, effects, `or R`) plus the payload's type; in Lean the call is an `Ax` whose arguments include the payload -- no new statement constructor | E1 |
| E3 | translator declaration | a library declares the translator from region to payload; the checker holds its signature to `effects { pure }` with `decreases`; the payload type is a table/tree type (trees as tables, §2). Running the translator needs the compile-time evaluator -- **only the declaration and the typing are built now** | -- |
| E4 | arena | `arena A capacity lo .. hi` as a linear mark (§3): allocation within the reservation needs no `or R`, `reset` consumes the mark and allocates a fresh one; Lean: an index into a reset arena is not expressible, a monotone arena has no fragmentation. Serves the translator (compile time) and run-time code alike | -- |
| E6 | hardware profile and library requirements | per §0c: the program's hardware profile as a declaration; libraries REQUIRE profile entries by reference; linking refuses requirements outside the profile, a same-named assumption with a different statement, and two keyed entries with one key and different values; foreign bodies refused in the hull of any `@lib` function; the manifest lists every requirement with its library and the calls relying on it. Lean: the program theorem over one profile, library sets as subsets, and a model for keyed mode assumptions with distinct keys | E2 |
| E7 | error mapping | a span map from payload values (and later expanded terms) back to positions in the region; one checker diagnostic routed through it, with a test | E1 |
| E5 | translation stage with certificate | the checker runs translators at compile time and checks the payload; the certificate is the payload's typing derivation, so Lean checks the OUTPUT and never needs the translator | the compile-time evaluator (`PLAN-BITS.md` §6) -- **therefore the wave after next** |

E1, E3 and E4 start in parallel; E2, E6 and E7 follow E1 within the wave. E5 waits for the
compile-time evaluator, which itself waits for the certificate measurement of `PLAN-BITS.md` §6.

**The payload type stays abstract in wave 3.** E2/E3 fix only that a payload is a value of a
library-declared table or tree type; nothing in the wave commits to a GPU form. A SPIR-V module
is a table of `u32` words and fits that shape, so the direct-emission decision of §4 needs no
change to E1-E7.
