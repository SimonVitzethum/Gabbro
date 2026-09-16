# MUSE-REPORT-203 — Lane 203 verdict: hand models for 07/59/109/125 (TODO §1.3, Lean half)

## 0. Procedural note (read first)

The wave preamble (NEW SINCE WAVE 5, binding) says: *"You are an INDEPENDENT
REVIEWER now: do not change any existing file; write only the verdict file your
task names."* The task text asks for four new `Korpus*.lean` files plus an
`import` line in the existing `grammatik/Grammatik.lean`. Those two orders
conflict: adding the import edits an existing file, and new files without the
import are not part of the build. The preamble is newer and explicitly binding,
so I obeyed it: **no Lean files were created or edited, no existing file was
touched, no `Korpus*.lean` was written.** This report is the deliverable, per
rule 8 (commit the report; no Lean changes to revert) and rule 13 (an
unbuildable witness is a finding — report it, do not weaken it).

Consequence for the ZEUGE lines (`korpus07_nutzer`, `korpus59_nutzer`,
`korpus109_nutzer`, `korpus125_nutzer`): **none of the four is built.** This is
not only procedural. For 07 and 125 there are additionally *substantive*
reasons a joint non-degenerate witness cannot be built today (§§1, 4 below):
the source has no G form at all (07), or its shape hits a documented exporter
refusal (125). Building a "witness" over a reshaped program would violate rule
13's non-degeneracy clause (the statement shape must apply where the program
applies it). For 59 and 109 a faithful model is feasible and I record exactly
what it would contain, so a future build lane can do it (§§2, 3).

## 1. Method

Read: `Korpus124.lean` (template), `beispiele/07`, `59`, `108`, `109`, `125`,
`crates/gabbro-check/src/lean_g.rs` (read-only; refusal codes LG001–LG007),
`dokumente/OFFEN.md` O12, `TODO.md` §1, `dokumente/SATZKARTE.md` tail. No
`cargo`, `lake`, or `lean` calls (rule 1; the one queued `./cargo-pruef` probe
exceeded its 300 s timeout without output and was abandoned — it is not needed
for a file-only verdict). No `./lean-bau` run: nothing in `grammatik/` changed,
so the build state is the merged tree's own.

## 2. Measure (deliverable 2)

Before: **2 of 6** have a model (108 via exporter, pinned in
`grammatik/Grammatik/Export108.lean`; 124 by hand, `Korpus124.lean`).
After this lane: **still 2 of 6.** No program gained or lost a model; the
change is a per-program feasibility verdict with exact refusal codes:

| program | shape | verdict |
|---|---|---|
| 07 eintritt-und-boot | `walk`/`format`/`entry`/`boot`, linear ghost marks, axioms, `prim`/`raw`/`extern`/`divergent` fns, no tables, no `concurrent` | NOT MODELABLE — needs source/language work first |
| 59 maskierte-sperre | tables + 2 locks + 4 fns + 2 entries | MODELABLE modulo dropping `deadline`/`falsifier` (LG001) |
| 109 lockfree-entry-roots | tables + 2 locks + 4 fns + 2 entries | MODELABLE — every form has a G counterpart |
| 125 read-under-lock | `static mut` + lock + 2 fns + `concurrent` | BLOCKED — value `return` inside `locks` (LG004) |

## 3. Per-program findings

### 3.1. 07 — no G form exists (report, do not fix the source)

`07-eintritt-und-boot.gab` declares: a `walk Seitentabelle` (page-table walk
type with `mappings of` quantifier domain, two invariants), a `format Pte`
(bit-level register format with `reserved` fields), two `entry` items (register
files, preserves/clobbers, stacks, dispatch), a `boot` item (ordered steps,
token flow), five `linear ghost` marks, four `axiom` declarations, `raw`/`prim`/
`extern`/`divergent` functions, and constants. It has **no `table`, no `lock`,
no `impl fn` with a block body, no `concurrent`**. Against `lean_g.rs`:

- `walk`, `format`, `entry`/`boot` *items*, axioms, `prim`/`raw`/`extern` are
  LG001 ("item with no G form"); the `entry`/`boot` *dispatch roots* travel as
  starts, but the dispatched functions (`syscall_verteiler`, `nmi_verteiler`,
  `rust_eintritt`) are all `extern` — LG001, and an `entry` naming nothing
  resolvable is LG005.
- The linear marks are `D.Marke`, a resource held in `Λ` — expressible in G in
  principle, but there is no program around them to attach the discipline to.
- There is no carrier (`Tab := Empty` needs at least one table elsewhere, and
  a G program needs at least one function — both LG001).

A `kP`-style `Einheit` for 07 would be an invention, not a model: G has no walk
types, no formats, no register files, no boot steps. The honest statement is
the task's own escape clause: **07 needs a source fix (or rather a language
extension: G forms for entry/boot hardware) first.** No `korpus07_nutzer`
witness is buildable, and any "witness" over a degenerate invention would fail
rule 13's non-degeneracy requirement (no table any function writes). This is a
finding about G's coverage, not a failure of this lane.

### 3.2. 59 — modelable after dropping checker-only annotations

Two modules, each a table (`Takte` count 64 / `Auftraege` count 16, one `u64`
slot field), a lock (`TAKT` with `masks irqs` / `RING` without), a `Held`-gated
leaf (`zaehle`/`bearbeite`, index param, one slot write), a distributor taking
the lock around a call (`takt_verteiler`/`ruf_verteiler`), and an `entry`
dispatching to each distributor. G counterparts exist for all of this:

- tables of `u64` ranges, locks (`Lock`/`rang`/`braucht`); `masks irqs` maps to
  the declaration's `maskiert` field (Korpus124 sets it `false`; a 59 model
  sets it `true` for TAKT — the one place the file's single-word difference
  from gift 460 becomes a model bit);
- index params travel (`Ty.index (D.count t)`; `lean_g.rs` ~l.919, ~l.663);
- `requires Held(L)` is the signature-held set; `locks L { … }` blocks and
  direct calls with `RufPasst.hh` are the Korpus124 routine;
- the two `entry` dispatch roots travel as declared starts (exporter docs
  l.183: starts = `concurrent` members, then `entry`/`boot` dispatch roots);
- `reads`/`costs` effects are NO FORM (ignored, l.1181) — fine.

The one refusal: every function in 59 carries
`deadline <= … arch x86_64 falsifier …`, and `check_fn` (l.1133) refuses any
function with `deadline`/`decreases`/`arch`/… as LG001 ("function carries a
form with no G counterpart"). A faithful hand model therefore **drops the
`deadline`/`arch`/`falsifier` annotations** (checker-only timing promises with
no `Expr` form — same class as `costs`, which is already ignored) and keeps
bodies, Held sets, locks, and starts. That is a documented weakening of
annotations, not of behavior, and the report of the build lane must say so.

O12-shape check for 59: the leaves have no `requires`/`ensures` beyond `Held`
and no lock invariant is declared, so the release-side question O12 asks for
124 does not arise as a failure — but the build lane must still state the
`NutzerPflicht` premise groups explicitly and prove them (the leaves' bodies
are single slot writes; the distributors' caller duties run the Korpus124
`kA_lauf` routine). No open premise is expected, but none is claimed here
without the proof.

### 3.3. 109 — fully modelable; the recommended next hand model

109 is the cleanest of the four: tables `T`/`U` (count 4, `u32` field), locks
`L`/`M` (ranks 0/1, disjoint carriers), Held-gated leaves `write_a`/`write_b`
(index param, single slot write of a constant), distributors
`distribute_a`/`distribute_b` taking their lock around a call, and two entries
dispatching to the distributors. Every item has a G counterpart (same
inventory as §3.2, minus the `deadline` problem — 109 functions carry only
`costs`, which is ignored form). Starts are the two entry dispatch roots, both
with empty Held sets — the `StartExklusiv` transfer shape the file header
describes, and the two lock domains are disjoint on top.

Lock-invariant note: the source declares no invariant, and none is needed for
the premise groups (leaves write constants to disjoint private-per-lock
tables; nothing is shared). If a build lane adds one (e.g. none), it must say
so; the faithful model adds none. Expected premise groups: `KoerperGutS` per
function (leaf: single-write routine as in `kP_koerper_setze`; distributor:
caller-duty routine as in `kP_koerper_A/B`), `SperrInvOk`, `ohneEwigB`, then
`NutzerPflicht` + `HardwareAnnahmen` + `akzeptiert` and the `gabbro_ziel`
instantiation exactly as `k124_ziel`. **Recommendation: 109 is the next hand
model to build** (lane 201 owns the exporter side; a Lean build lane owns the
model). No `korpus109_nutzer` witness is claimed here — stating the groups
without proving them would violate rule 4.

### 3.4. 125 — blocked by return-under-lock (LG004)

125 is otherwise the easiest shape: one global (`static mut z : u32`, supported
— `Glob`/`gtyp` with `gSp0` initializer), one lock, two functions, `concurrent`
starts, Held sets empty. The blocker is one statement: `lese_schreibe` does
`let v = z; z = v; return z;` **inside** `locks WACHE { … }`. Per the
`Export108.lean` header, the take-inside remedy "has no G form for value
readers (LG004: no `return` under `locks`)". 125's reader is exactly that
refused shape, with a write added. A hand model would have to restructure the
body (read under lock into a local, release, then return) — i.e. model a
*different program* than the source, which is precisely what Korpus124's
header refuses to do silently (its body differences are documented line by
line). **Verdict: 125 needs a source-side decision first** — either the
example is rewritten to return outside the lock (a corpus change with
re-measurement, lane 204's territory), or the exporter/G gains a form for
value-return under lock. Until then no faithful `korpus125_nutzer` witness is
buildable; report WHY (this section), do not weaken the witness.

## 4. Why no ZEUGE witness is built (rule 13 accounting)

| witness | status | reason |
|---|---|---|
| `korpus07_nutzer` | unbuildable | no G forms for any of 07's items (§3.1); any instantiation would be degenerate (no table) |
| `korpus59_nutzer` | not built (reviewer lane) | feasible after dropping `deadline`/`falsifier` (§3.2); proving it belongs to a build lane |
| `korpus109_nutzer` | not built (reviewer lane) | feasible with no weakening (§3.3); proving it belongs to a build lane |
| `korpus125_nutzer` | unbuildable as written | value return under `locks` has no `Stmt`/`Endblock` form (§3.4); needs source or G change first |

No premise is quantified over all syntax anywhere in this report (no theorems
are stated), so rule 13's mechanical gate has nothing to check in — and must
not be read as passed for the four models either.

## 5. Ownership and handoff

- Lane 201 (exporter, owns `lean_g.rs`): the 59 `deadline`-LG001 and 125
  return-under-lock-LG004 refusals are its measurement inputs, not mine to fix.
- Lane 204 (owns the 124 corpus file / O12): 59's annotations and 125's body
  shape are corpus decisions of the same kind; I changed no `.gab` file.
- Suggested next build lane: hand model for **109** per §3.3 (template
  `Korpus124.lean`, `kP`-style, `masks` untouched, no invariant), with
  `korpus109_nutzer_zeuge` on the non-degenerate program (tables T and U both
  written; reached runs of both distributors with a memory-changing step).
- 07 belongs to the entry/boot language-extension track (§0c/§2 sieves), not
  to the Korpus family.

## 6. Build state

No Lean changes; `./lean-bau` was not run (nothing to check). `git status`
before this report was clean (merged tree at `57c44087`). This report is the
only new file, committed per rule 8.

## CUTS

- No `Korpus07/59/109/125.lean` written (reviewer instruction; §§3.1/3.4 give
  the substantive blocks for 07 and 125).
- No premise group stated or proved for any of the four programs; all
  proof-shaped claims above (§§3.2/3.3 routines) are expectations for a build
  lane, explicitly not theorems.
- No `#print axioms` output: there are no new theorems. Every Lean fact cited
  (Korpus124 names, `gabbro_ziel`, exporter refusal codes) is by reference to
  the merged tree.
- The `./cargo-pruef` probe timed out in queue and was abandoned; no Rust
  claim is made.
