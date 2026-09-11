# The order of duties (PFLICHTEN-ORDNUNG) -- lane-133, 2026-09-11

**What this note is:** the composition premises a duty register rests on, measured
against the checker as it stands, with the one refusal this lane adds (`H022`) and
the reason it stays unwired.

## 1. Duty counting today (read-only finding)

`crates/gabbro-check/src/pflichten.rs` **counts and names; it refuses nothing.** `sammle`
walks one unit and books eight kinds -- preservation (`E`), postcondition (`N`),
foreign duty (`F`), precondition at the call site (`V`), refinement (`R`), device
promise (`D`), loop invariant (`S`), unowned invariant (`W`) -- each with the function
that owes it, the anchor where it arises, and the wording (or the named reason there
is none). `zeige` prints the register; `gabbro pflichten` prints no register at all
over a file the passes refuse (`gabbro-cli/src/main.rs`: "has errors -- no register").

*Enforcement lives in the passes, not in the register.* A cycle without a measure
falls at `kosten.rs` (`K008`/`K009`), never at `pflichten.rs`. That split is the
reason this lane puts the `H022` detector beside the register (a second reader over
the same graph) instead of a ninth duty kind: the cycle is not a new debt, it is the
missing premise under debts already counted.

## 2. Premise one: every call cycle carries a measure

**Live enforcement:** `K008` (a member that reaches itself declares no `decreases`)
and `K009` (a recursive site that does not visibly lower the measure), both in
`kosten.rs::rekursionsmass`, both over `aufrufgraph::Graph::im_zyklus`.

**Pinned before this lane:** `gift/150` (`K008`, self-recursion), `gift/151`
(`K009`, measure passed through unchanged), `gift/184` (`K009`, swapped measure).

**Pinned by this lane** (composition shapes: the induction must cover every member):

| probe | shape | falls with |
|---|---|---|
| `beispiele/gift/746-wechselruf-ohne-mass.gab` | mutual cycle, no measure on either side (must fall) | `K008` |
| `beispiele/gift/747-halbes-mass-im-wechselruf.gab` | mutual cycle, measure on one side only (must fall once) + twin with both measures (must stay silent, in-file) | `K008` |
| `beispiele/gift/748-dreierzyklus-ohne-mass.gab` | three-member cycle, no measure (boundary: the premise holds past length two) | `K008` |

Measured 2026-09-11: the 747 twin runs silent (zero `Fehler`; two `E009` hints --
the honest third state over the cycle hull, same as `gift/727`, which carries a
mutual cycle WITH measures).

**`H022` (assigned free, no prior use in the tree):** the cycle as one composition
unit -- which members it has, which of them carry no measure, where the refusal
anchors. Built in `pflichten.rs` as `H022` + `Zyklenluecke` +
`zyklen_ohne_mass` (mirrors the `K008` condition over the same graph, so the two
cannot disagree about membership) + `h022_weigerung` (code, site, two notes).
Unit tests inside `pflichten.rs`: both members found, half measure names only the
bare one, silence with measures and without a cycle, refusal carries code/stufe/
member, twin silent through `pruefe`, bare cycle falls per member with `K008`.

**Unwired on purpose.** Wiring is a line in `lib.rs::pruefe`, and `lib.rs` is
frozen for this lane. Follow-up: one line in the pass list, then the three gift
probes move from `-- erwartet: K008` to `-- erwartet: H022 allein` (the `cc`
half is already the claim -- a bare cycle must not change what ships).

## 3. Premise two: caller-before-callee order, where checkable

Measured, not built (no new refusal; nothing in scope was missing its pin):

- Boot-step order: `gift/71` falls with `O002`, `gift/205` with `O007`.
- Lock order across calls: `gift/142` falls with `H012`; the same call shape WITH
  a cycle goes honestly silent (`gift/727`, `Hinweis E009` -- R16, incomplete hull).

What "where checkable" excludes is deliberate: declaration order inside a unit is
not an order (names resolve unit-wide), and lemma order in the emitted theory is
the emitter's business, pinned by `pruefe-emission.sh`, not by a refusal.

## 4. Premise three: bodies end the way their type promises

Measured, not built:

- A `narrow ... else` branch must leave (`M105`, `m1.rs`).
- A valueless `return` where a value is owed falls (`N044`, `gift/428`).
- A `never` routine that returns falls (`S009`, `gift/692`).
- Phase steps inside `return` fall (`O004`, `gift/258`).

Open, named here and not measured: a value-typed body that falls off its end on
some path with no `return` at all. No probe pins it either way; that measurement
belongs to the lane that takes it.

## 5. What this lane changed

- `crates/gabbro-check/src/pflichten.rs` ONLY: `H022` section (constant,
  detector, refusal constructor, six unit tests). No existing line touched.
- `beispiele/gift/746`, `747`, `748`: composition-premise probes, all firing
  with `K008` today.
- This note (new).
- Nothing else: `lib.rs`, `saetze.rs`, the mutation catalog, the code catalog
  (`BENANNT`), and `tests/beispiele.rs` are untouched.

## 6. Addendum 2026-09-11 (p07): `H022` wired, `H023` withdrawn, probes 774-775

**`H022` is wired, beside `K008`.** The line §2 left open stands in
`crates/gabbro-check/src/lib.rs`: every gap `pflichten::zyklen_ohne_mass`
reports is refused via `pflichten::h022_weigerung`, in both the plain and the
`GABBRO_ZEIT` pass list. Detector + constructor are unchanged from §2. The
sentence register books the rule (`saetze.rs`:
`pflichten.masslose-wechselrufe`, `H022`, `Gemessen`). This supersedes the
"Unwired on purpose" paragraph of §2; that paragraph stays as the lane-133
record.

**Measured full sets, not just the booked pair.** The register books
`K008+H022`; what the pipeline emits per bare member is the triple `H022` +
`K001` + `K008`. `K001` is structural, not noise: a call counts the callee's
DECLARED `costs`, so a bare member always exceeds its own promise -- a
recursive call costs nothing only under `decreases` (`kosten.rs`). The measured
member of a half-covered cycle stays fully silent (no `K008`, no `K009`, no
`K001`). Pinned per file in `crates/gabbro-check/tests/pflichten_zyklen.rs`,
where the file-level gift run only asserts the expected code fires.

**`H023` is withdrawn, in code.** The candidate was the cross-body freshness
expiry (callee write-hulls expiring caller taints, `nebeneinander.rs` as the
home). `messung/CROSSBODY-REGEL.md` measures that the transport already runs in
`m1.rs` (`rufe_toeten_fakten`, refused as `M147`, pinned by `gift/752`-`754`),
so a second refusal would double-book one defect -- and the code-to-pass map
puts `W`-codes in `nebeneinander.rs` while the `H`-family lives in
`geteilt.rs`. The withdrawal stands as a reason note beside the `H022` section
in `pflichten.rs` (backticks only: it NAMES the code and ASSIGNs nothing, per
`instrumente/pruefe-kennungen.py`). Owner if ever built: whoever owns the `m1`
freshness internals.

| probe | shape | falls with (exact, measured) |
|---|---|---|
| `beispiele/gift/774-selbstruf-ohne-mass.gab` | self-cycle, no measure (length-one complement to 746/748) | `H022`, `K001`, `K008` |
| `beispiele/gift/775-dreierzyklus-halbes-mass.gab` | three-member cycle, measure on one side only (length-three complement to 747) | `H022` x2, `K001` x2, `K008` x2 on the bare members; the measured member silent |

Verification, scoped (server down, 2026-09-11): `cargo +nightly test -p
gabbro-check --test pflichten_zyklen` 8/8, `--test beispiele` 25/25. Local
stable (`rustc 1.97.1`) does NOT build this base: pre-existing `E0614` at
`lean.rs:4475` and `refinement.rs:494`, in files this lane never touched;
nightly (`1.98.0-nightly 2026-06-22`) builds it clean.
