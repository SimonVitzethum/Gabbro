# MUSE-REPORT-197: explicitness as a view — `gabbro fmt --explicit/--elide`

Lane 197 (SIMPLICITY lever 3, `dokumente/PLAN-EINFACHHEIT.md` §1.3, after lane 191).
This session RESUMED an uncommitted tree (three modified files, two new files)
and brought it green; one REAL finding from the earlier session is kept and
repaired (see §3).

## 1. What was built

`gabbro fmt --explicit FILE` writes every settled derived clause out;
`gabbro fmt --elide FILE` removes every clause equal to what would be derived.
Both are pure views over the checker's own derivation — never a second
computation: the effect fixpoint (`crate::ableitung::leite_ab`, wide) and
`crate::kosten::abgeleitete_kosten`. `ensures`/`requires`/invariants are never
derived or removed (PLAN-EINFACHHEIT §2).

New definitions/theorems — all Rust (no `grammatik/` file touched):

- `crates/gabbro-check/src/fmt.rs` (new): `Art`, `Edit`, `Zaehlung`,
  `plane_explicit`, `plane_elide`, `explicit`, `elide`, `zaehle`, plus
  private helpers `sicht`, `satz`, `normiere`, `geschrieben_normiert`,
  `schreibbar`, `formuliere`, `hypothetisch`, `ohne_kosten`,
  `bibliotheksrufe`, `rufkante`, `kosten_schluss`, span/anchor surgery
  helpers. Key rules: a removable written clause is DELETED and re-inserted
  at the E4 anchor (never rewritten in place); a written bound TIGHTER than
  derived, a symbolic bound, a relied-upon bound (caller closure), a
  `divergent`/`spec`/bodiless/translator function, and an unsettled
  derivation are all kept as written.
- `crates/gabbro-check/src/emit.rs`: `wirkungsattribut` over an OMITTED
  `effects` now derives the attribute from the deeds
  (`wirkungsattribut_abgeleitet`, same walker the checker runs). Without
  this the views moved the emitted C on every pure leaf — the "same C"
  property below would be unachievable. No new diagnostic, no new pass.
- `crates/gabbro-cli/src/main.rs`: `fmt` subcommand (`befehl_fmt`,
  `--explicit`/`--elide`, English-only flags, refuses units with errors),
  `COMMAND_NAMES` + `hilfe()` entries.
- `crates/gabbro-check/tests/fmt_views.rs` (new): over every accepted
  corpus file — same diagnostics (codes/levels/texts/notes/fixes), same M1
  pair, byte-identical emitted C, and both round trips byte-identical
  (`elide(explicit(F)) == elide(F)`, `explicit(elide(F)) == explicit(F)`).
  Also prints `FMT-ZAEHLUNG` (see §4).
- `crates/gabbro-cli/tests/fahnen.rs`: registered `["fmt"]`,
  `--explicit`, `--elide` (the procedure that file demands for new
  spellings; English-first, no German second name).

## 2. The session's own work (on top of the resumed tree)

1. Fixed `explicit()` round-trip, direction 1: a written-but-removable
   clause was rewritten IN PLACE while the elide path deletes and
   re-inserts at the anchor — 20 files red with
   `explicit(elide(F)) != explicit(F)` (incl. `messung/fragmente/F10.gab`).
   Fix: delete + anchor insert (fused with omission inserts; rear-to-front
   application keeps coordinates consistent).
2. Fixed round-trip, direction 2 (3 files, among them
   `beispiele/13-zeuge-mit-staerke.gab`): `explicit` rewrote the SPACING of
   a relied-upon `costs` bound (`costs    <= 2 ops`) that `elide` keeps —
   bytes that can never converge. Fix: a relied-upon bound is neither
   omitted nor removable, so `explicit` leaves it alone entirely.
3. Registered the new spellings in `fahnen.rs` (2 red tests).
4. Added the corpus-wide elide/explicit counts to the test log.

## 3. The kept REAL finding (repaired, with file and clause)

`explicit(elide(F)) != explicit(F)` on `messung/fragmente/F10.gab`:
`impl fn kerne_zaehlen` carries written `effects { reads k }` (removable)
on its own line plus a kept `costs   <= 65540 ops`; `explicit(F)` rewrote
in place (two lines) while `explicit(elide(F))` inserted beside `costs`
(one line). Repaired by the delete+insert rule (§2.1); verified by hand:
both round trips byte-identical on F10 after the fix.

## 4. Measured numbers (after; corpus untouched, so before identical)

- `./cargo-pruef`: `== exit 0; failing tests: 0`.
- `./emission-pruef`: `ALL PASS -- 37 durchgestochen, 262 von 262
  uebersetzen, 2 umgekehrte Probe(n)`. `MARKE_EMIT` untouched.
- `fmt_views`: `FMT: 183 accepted, 619 refused, 0 findings`.
- `FMT-ZAEHLUNG` over the 183 accepted files: `--elide` would remove
  **120 effects + 58 costs clauses**; `--explicit` would write
  7 effects + 9 costs clauses (most derivable clauses stand written).
- PLAN-EINFACHHEIT §0: Zeremonie LEHR **135 von 1743** (120 measured,
  1 refused), echter Code **14 von 110**; sentences
  `163 over 12 passes (155 measured, 2 ARGUED, 6 CONJECTURED, 0 proved)`.
  Deltas vs lane 191's table (131 von 1715; 160 sentences) come from
  merged waves 4–5, not this lane: zero `.gab` files changed, zero
  passes/codes/sentences added, `messung/PASSREGISTER.md` untouched.
- `./lean-bau`: `Build completed successfully (230 jobs).`
  (no `grammatik/` file touched).
- `pruefe-kennungen.py`: ALL PASS (408 codes, none new).
- `pruefe-englisch.py`: red, PRE-EXISTING drift — 29 Zubringer (booked 26;
  28 already at lane 191's HEAD) and 5 Sink messages (booked 2); verified
  none names `fmt.rs`/`fmt_views.rs`/`fahnen.rs`, and the count is identical
  with this lane stashed. `pruefe-todo.py`: 14 findings, none mine.

## 5. What is still open / NOT measured

- `instrumente/pruefe-luecken.py` (mutation anchors) never runs on a dirty
  tree and was not run; the full mutation run, `abnahme.py`, and Isabelle
  were not run either (same stand as lane 191, §6 there).
- No `before` binary run for §0: justified by construction (empty corpus
  diff, no new pass/code/sentence) instead of measured. A skeptical merger
  can rebuild at this commit's parent in minutes.
- The `Zaehlung.ausgelassen` blind-spot list is printed nowhere user-facing;
  it exists for debugging and the report above. If the merger wants it
  behind a flag, that is a new flag plus a new `fahnen.rs` line.
- Poison/positive probes for new REFUSALS: none added, none needed — this
  lane adds no refusal (the `fmt` views own no diagnostic; the `emit.rs`
  change moves only the C attribute, pinned by the byte-identical-C check).

## 6. What I believe is wrong (in the task, not the tree)

Nothing load-bearing. One remark: the brief's "THREE modified files"
miscounts — the tree held four (`fahnen.rs` was already touched by the
earlier session to start the registration). No consequence.
