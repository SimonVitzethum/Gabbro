# MUSE-REPORT-232 — hold chunking: scans that fit under held (K002)

Lane 232 (TODO §-1 wave B, after merged lane 223). Worker scope:
`kosten.rs`, `saetze.rs`, tests/probes only. No Lean, no `emit.rs`,
no `MARKE_EMIT*`, no OS surface.

## What was built

The checked chunked-scan combinator, cost-side. No new syntax: windows are
existing statements (one bounded window per `locks` acquisition, as in
`beispiele/147-ftp-alg-control.gab`: 1024 slots as 16 windows of 64, 8320 ops
per tick under `held <= 16384`). What the checker was missing was the
refusal-side half: an unchunked full scan overflowing `held` fell at K002 with
no word on the remedy, and nothing pinned that the bound is not the thing
that moves.

1. **`crates/gabbro-check/src/kosten.rs` — N421 beside K002.**
   In `Rechner::sperrbloecke`, where an exclusive `locks` block overflows its
   `held` promise AND the block textually scans a full domain, a second
   refusal fires at the same span naming the remedy (split into bounded
   windows, one per acquisition, each fitting `held`; raising `held` is
   latency for all cores, not a fix). K002 itself is byte-identical:
   same condition, same span, same text, same strictness.
2. **`enthaelt_traverse` (new free fn in `kosten.rs`).** Detects a
   `Schleife::Traverse` anywhere inside a block, walking every
   block-carrying statement form (`wenn`/`match`/`bricht`/`narrow`/
   `let-else`/`observes`/nested `locks`/`retry`/`forever`/`exchange-update`/
   `alloc-else`). A scan behind a call edge is deliberately NOT named: its
   cost already sits in the block total through the declared `costs` edge.
3. **`crates/gabbro-check/src/saetze.rs` — `kosten.haltezeit_fenster`
   (`N421`).** Fires exactly on the conjunction (exclusive overflow AND a
   written scan), beside K002, never alone, never instead. The `vorbehalt`
   states what is NOT checked: coverage (that the windows tile the full
   scan) is author logic, like `costs` itself.
4. **Probes both directions.**
   - Poison: `beispiele/gift/1082-haltescan-ungestueckelt.gab`
     (`-- erwartet: N421 allein`: 64 slots x 2 ops under `held <= 32`;
     falls K002 + N421, and `cc -Werror` accepts the emitted C).
   - Positive + boundary inline in `crates/gabbro-check/tests/paesse.rs`:
     `haltezeit_fenster_ungestueckelt_faellt_mit_k002_und_n421` (exact
     `["K002", "N421"]` — the unchunked scan still falls at K002),
     `haltezeit_fenster_ohne_scan_bleibt_k002_allein` (20 plain stores vs
     `held <= 8`: exact `["K002"]`, N421 silent without a scan),
     `haltezeit_fenster_gefenstert_bleibt_sauber` (16-slot window under
     `held <= 64`: zero errors).

Consumed: N421 (N422–425 stay free), gift 1082 (1083–1086 stay free).

## The per-window invariant argument (deliverable 2)

Each window is its own `locks` acquisition. The existing release check
(`sperrinv.rs`, untouched — outside this lane's file scope) demands the lock
invariant at every release, so every window re-establishes it before the next
window acquires. Between acquisitions no lock is held, so waiting cores get
their slot: the one 2048-op full-scan latency becomes N bounded per-window
latencies, each held against the unchanged `held` promise by K002. Chunking
moves work across acquisitions, never outside them — that is why the lock leg
holds across chunks with no model change and no weakening of any check.

## Gates (all green)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (paesse suite 148 -> 151;
  the 3 new tests verified individually: 3 passed).
- `./lean-bau`: `Build completed successfully (274 jobs).` (no Lean touched).
- `./emission-pruef`: `EMISSION: ALL PASS`. `MARKE_EMIT*` untouched.
- `pruefe-saetze.py`: 417 Kennungen, 173 Saetze, 0 erfunden (N421 booked).
- `pruefe-kennungen.py`: ALL PASS (N 132 -> 133, one file).
- Corpus verdict diff, measured with the lane binary: **zero moves in the
  clean corpus** (no `beispiele/*.gab` carries N421); in gift only
  `35-sperre-zu-lang.gab` gains N421 beside its existing K002 (contains
  harness, suite green). Every N421 in either corpus stands beside K002 —
  the code never fires alone.
- `pruefe-englisch.py` stays red exactly as before the lane (7960/37/5 vs
  booked 7949/26/2, identical with my changes stashed): pre-existing drift
  per TODO §6, zero German lines added here.

## What remains open / what the task got wrong

- `messung/BEFUNDE-bm13.md` does not exist in this tree (only
  `messung/BEFUNDE.md`); H-1/H-3, `altere_fenster` and the 1024-packet tick
  were reconstructed from the in-tree shape (`beispiele/147`, lane 236
  noted the same gap). If the firewall tree's exact window contract differs,
  say so and the N421 note text follows it.
- `dokumente/PLAN-SYSCALL.md`, `PLAN-BITS.md`, `dokumente/PLAN-ERWEITUNG.md`
  contain no chunking/window design for this task; nothing in them changed
  the design. TODO §-1 lane 223 (trusted costs) is merged and composes:
  window totals count declared callee costs through the same edge.
- The lane prompt's reviewer paragraph ("do not change any existing file")
  contradicts the task's explicit file scope (`kosten.rs`, `saetze.rs`,
  tests/probes); TODO §-1 wave B confirms 232 is the `kosten.rs` worker,
  so the task scope won.
- NOT built, plainly: window coverage (windows tiling the full scan),
  shared-side (`K004`) chunking guidance, and any bound-raising path —
  the last is refused by design, the first two need new syntax or a wider
  scope than this lane owns.
- No Lean theorems added, so rule 13 has no target (no `ZEUGE:` line, no
  ∀-over-syntax premise). The Rust-side equivalent stands: one poison file
  plus exact-set tests in both directions.
- Scratch probes under `.tmp/` (`probe-fenster-positiv.gab`,
  `probe-fenster-grenze.gab`) are gitignored and uncommitted.
