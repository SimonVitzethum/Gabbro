# TOCTOU as a class: check, window, use

> **Measured on 2026-09-10 against `d162dfc`, read-only first, then by test.**
> Every pattern below has the same three parts: a **check** that establishes a
> fact, a **window** during which the world can move, and a **use** that relies
> on the fact still holding. What differs is what moves, and what the checker
> holds across the window today. Each entry names its **carrier** (the rule
> that holds it) or its **gap** (where nothing holds it, and why no refusal
> was added for it this lane).

## The five patterns

### 1. narrow-then-use

**Pattern.** A range condition (`if`), a `narrow … to … else`, a `match` on a
`tagged` value, or a foreign `ensures` narrows a carrier-derived value (V1--V3
facts) or taints a local with its carrier (V4 freshness); a later branch
condition, call argument, return, `narrow` subject, or index acts on it.

**Window.** Narrow point to use point, inside one body.

**What must hold across it.** No write to the carrier on the window -- by this
body, by any callee, or by any concurrent sibling.

**Carriers and gaps, per writer:**

| Writer | V1--V3 facts | V4 taints (`M147`) |
|---|---|---|
| Own body | Killed per write (`schreiben_toetet_fakten`, `m1.rs`), field-granular since 2026-08-19 | Expired per write at carrier granularity (`frische_toeten_schreiben`) |
| Direct call | Killed per callee writes-hull, coarse kill-all-nonlocal when the hull is unreadable; `pure` kills nothing (refined 2026-08-25, `rufe_toeten_fakten`) | Expired per callee writes-hull, all taints when the hull is unreadable |
| Indirect call (`t->f()`) | Killed coarse -- no path names a hull, so every non-local fact dies (`aufruf_toetet_fakten`) | **GAP, closed this lane: nothing expired.** `rufe_toeten_fakten(&[])` early-returned through the V1-only coarse rule, so a stale decision after an indirect call passed. New refusal: every taint expires at an indirect call, mirroring the V1 coarse kill (`m1.rs::rufe_toeten_fakten`). Pinned by `beispiele/gift/715` (statement call), `/716` (call in `let` RHS), `/717` (boundary: refresh and store stay silent, `narrow` subject falls) |
| Loop | Carried inward never; facts die at what the body writes (`geschriebenes_toeten`) | **All** taints expire at the boundary (`frische_alle_toeten`); a value needed across iterations is re-read inside (pinned by `gift/703`, `/709`) |
| Concurrent sibling | **GAP, open.** `M1` walks one body with one `Lage`; a `concurrent { f, g }` member's writes never expire facts in another member's body | Same gap -- same `Lage` boundary |

The cross-thread gap gets **no new refusal this lane**: holding it needs
cross-body hull propagation (the `nebeneinander.rs` machinery, which today
refuses write-write overlap as `W001`/`W002` and fail-closed incomplete hulls
as `W003`), not a one-line kill. What stands there instead: `W001` refuses
same-place and same-table writes between declared-concurrent bodies, so the
narrowed carrier cannot be *legally* written by a sibling that also writes it
-- but a sibling that only writes while this body only reads-and-uses stays
silent, and the catalog says so instead of covering it.

### 2. syscall check-then-copy

**Pattern.** Gabbro validates a length or pointer, then hands it to an `extern
fn` that copies (the `copy_from_user` class measured at K3): check in Gabbro,
copy in foreign code.

**Window.** The Gabbro-side check to the foreign copy.

**What must hold across it.** The checked value still describes the source
bytes at copy time -- neither the user side nor a concurrent writer changed
them in between.

**Carrier.** At the call boundary both halves die: the extern callee's effects
name its parameters, so the hull is unreadable by construction and the coarse
rules apply -- V1 facts over non-locals die, and every V4 taint expires. A
checked value cannot be *used* afterwards without a re-read.

**Gap (by construction, no refusal).** Inside the foreign body the checker
sees nothing: a re-read after the check is invisible, and an `ensures` clause
that narrows the result is trusted surface (`messung/FREMDVERENGUNG.md`: 1 of
10 foreign contracts narrows effectively). The boundary is held; the far side
is exported, not checked.

### 3. awaits-then-act

**Pattern.** `let x = A awaits { p, q }` loads a published snapshot; the body
then acts on `x`.

**Window.** Load to act.

**What must hold across it.** The snapshot is still the latest -- always
memory-safe (the carrier is atomic), but possibly logically stale after a
newer publish.

**Carriers.** `V006`/`V007` hold the payload *order* (writes before
`publishes`, reads after `awaits`); `V001`/`V002` refuse orphan halves;
`V004`/`V005` hold the ordering strength on the publish side.

**Gap (no refusal).** No revalidation rule: the load rebinds V4-clean --
correct, it *is* fresh at load time -- and nothing later expires it on a
concurrent publish. Same `Lage` boundary as pattern 1: the publishing sibling
is a body this pass never walks beside this one. Staleness here is a logic
question the pairing rules deliberately do not ask.

### 4. budget-check-then-run

**Pattern.** `costs <= N ops` is counted statically against the declaration;
a caller relies on a callee's declared budget without recounting its body.

**Window.** Count time to run time. The code is fixed, so the "change" sits
across the call boundary: the actual body versus the declared number.

**What must hold across it.** Every body costs what it declares, and every
indirect target costs what its pointer type promises.

**Carriers.** The `K` pass counts statically; `K005` refuses a promise the
pass cannot read instead of dropping it; an indirect call costs what its
`fn(…)` type promises and falls without a constant bound (`kosten.rs`, B8
2026-08-21); `E008` reconciles declared effects against the computed hull.

**Gap (fail-closed, no refusal needed).** A count over a domain with no length
(`count … in threads`) cannot be bounded at all -- `D025` refuses the shape
outright (pinned by `gift/693`) instead of admitting an unbounded budget.
Foreign bodies' `costs` are trusted lines in the certificate (section E), same
export as pattern 2.

### 5. deadline-check-then-run

**Pattern.** `deadline <= n ops arch X falsifier p` names by when, in cycles
on machine `X`, with a probe that can refute it.

**Window.** Probe run to deployment on `X`.

**What must hold across it.** The cycles measured still hold on the target
hardware under its actual load.

**Carriers (structural only).** `K011` requires a readable number, `K012` a
declared machine (R16); `N056` requires a falsifier that resolves in-unit to
be able to refute; the obligation is booked as the named assumption `hardware
(fortschritt a)` with manifest entry `frist_<fn>_eingehalten`; the sample
probe is `sonden/sonde_tick.c` (R15/W10).

**Gap (by construction, no refusal).** Probe-then-ship: a sample is not a
bound, an unresolved probe is a program next to the tree, and the Lean mapping
`fristAlsAnnahme` proves nothing about time (`SYNTAX.md` §18). Time is a
hardware outcome; the checker verifies only its paperwork.

## What this lane changed, and what it left open

**Changed:** pattern 1 across indirect calls -- one line in
`rufe_toeten_fakten` (`crates/gabbro-check/src/m1.rs`): the coarse path that
already killed every non-local V1 fact now also expires every V4 taint. Three
gift probes pin it and its boundary (715--717).

**Left open, with the reason beside each:** cross-body (thread) expiry needs
hull propagation, not a kill line (§1); foreign re-reads are invisible by
construction (§2); awaited-value staleness is unasked (§3); unbounded counts
are refused rather than held (§4); deadlines are sampled, not bounded (§5).

**Follow-up, not built:** refine the indirect-call expiry with the `fn(…)`
type's own contract (it may name `reads`/`writes`/`pure` since B8) instead of
expiring everything. The coarse rule errs safe; the refinement buys precision
only where indirect calls sit on hot tainted paths, and no corpus site shows
that yet.
