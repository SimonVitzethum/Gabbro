# MUSE-REPORT-206 — lane 206: simulation-certificate printer + Lean checker for stage (b)

Branch: `muse/206`. Task: TODO §1 sixth bullet + §2 stage (b) — a printed
certificate plus a Lean checker turning it into the simulation, so stage (b)
scales beyond the hand-built `sim124`.

## What was done

1. **Printer (Rust, extended `crates/gabbro-check/src/corrcert.rs` only).**
   New `SimCert124` with the four relation tables of `R124` as data
   (`g_a`/`h_a` for `hauptA`, `g_b`/`h_b` for `hauptB`), the expected tables
   (`erwartet_g_a/h_a/g_b/h_b`), the print entry (`gedruckt`), a printer-side
   check mirroring Lean `pruefeSim` (`pruefe`), the sidecar path
   (`sidecar_path`, `<stem>.simcert`), and two renderings: `to_json` and
   `to_lean` (the Lean literal body of `cert124_printed`). Five new unit
   tests: printed-tables check, one forged entry per table fails (plus
   truncation), JSON spelling pinned, Lean literal pinned byte-for-byte
   against `SimPruef.lean`, sidecar convention. `corrlean.rs`, `certemit.rs`,
   `certstmt.rs`, `main.rs` untouched (nothing needed there); no new N codes,
   no MARKE_EMIT touch, example 124 untouched.
2. **Checker (Lean, new `grammatik/Grammatik/SimPruef.lean`, one import line
   appended to `grammatik/Grammatik.lean`).** `SimCert` (four `List Nat`),
   expected tables `erwartetGA/HA/GB/HB` read off
   `gOfA`/`heldGA`/`gOfB`/`heldGB`, checker `pruefeSim` (`decide` over the
   four equalities), soundness `simpruef_tab` (checked cert carries the
   expected tables), result package `SimPruefErg`, and `simpruef_liefert`
   (checked cert + `Wurzeln w` yields the `SimC` package built from
   `sim124`). Witness `simpruef_124_zeuge` with the printed literal
   `cert124_printed`.
3. **Round trip on 124.** Rust `to_lean()` output == `cert124_printed`
   literal (pinned by test
   `sim124_lean_literal_stimmt_mit_simpruef_ueberein`); Lean decides
   `pruefeSim cert124_printed = true` inside `simpruef_124_zeuge` (`by
   decide`); `simpruef_liefert` turns it into the `sim124`-shape `SimC`.
   `DRFSC`/`LaufzeitC` are named premises of `schlusssatz_124_bei` and are
   hand-fed there, not smuggled — precisely the "still hand-fed" premise
   the task asks to name (alongside the G segments, see CUTS).

## Exact names of new definitions/theorems

- Rust (`corrcert.rs`): `SimCert124`, `SimCert124::erwartet_g_a`,
  `erwartet_h_a`, `erwartet_g_b`, `erwartet_h_b`, `gedruckt`, `pruefe`,
  `sidecar_path`, `to_json`, `to_lean`; tests
  `sim124_gedruckt_besteht_die_pruefung`,
  `sim124_gefaelschte_tabelle_faellt_laut`,
  `sim124_json_traegt_programm_und_vier_tabellen`,
  `sim124_lean_literal_stimmt_mit_simpruef_ueberein`,
  `simcert_seitenwagenpfad_teilt_die_konvention`.
- Lean (`SimPruef.lean`): `SimCert`, `erwartetGA`, `erwartetHA`,
  `erwartetGB`, `erwartetHB`, `pruefeSim`, `simpruef_tab`,
  `SimPruefErg`, `simpruef_liefert`, `cert124_printed`,
  `simpruef_124_zeuge`.

## Verification results

- `./lean-bau`: exit 0, 0 error lines, last line `Build completed
  successfully (269 jobs).` (`SimPruef.olean` built).
- `./lean-probe grammatik/Grammatik/SimPruef.lean`: exit 0, 0 errors.
- `#print axioms`: `simpruef_tab` depends on no axioms;
  `simpruef_124_zeuge` on `[propext, Classical.choice, Quot.sound]`
  (standard three).
- `./cargo-pruef`: exit 0, failing tests 0; the five new tests pass
  individually (`sim124_*` 4/4, `simcert_*` 1/1).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is used
  (`simpruef_liefert` destructures the checked-table conjunction into the
  result package).

## Certificate format (grammar)

- JSON sidecar `<stem>.simcert`:
  `{"program":"124-two-threads-private","gA":[…],"hA":[…],"gB":[…],"hB":[…]}`
  — C-position→G-residue maps (`gA` 13 entries for positions 0–12,
  `gB` 9 for 0–8) and held-lock flags (`hA` 7 residues, `1` at 3,4;
  `hB` 5 residues, `1` at 2,3).
- Lean literal (body of `cert124_printed`):
  `⟨[0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6], [0, 0, 0, 1, 1, 0, 0],`
  `[0, 0, 1, 1, 2, 2, 3, 3, 4], [0, 0, 1, 1, 0]⟩`.

## What the checker checks vs. assumes

- Checks: the four tables equal the expected ones (`decide`).
- Assumes (hand-fed, named in CUTS): the per-step G segments (`gBlatt`,
  `gNimm`, `gSetze`, `gGib`, `gPruefe`) and position case splits
  (`schrittA/B`) via `sim124`; the hand transcriptions `c124`/`kP`;
  `DRFSC`/`LaufzeitC` at `schlusssatz_124_bei`.

## What still blocks program #2

Checked segments, not just checked tables: a second program needs
`SegPasst` evidence per step in the certificate. Behind that: the exporter
refuses concurrent programs (124 is `LG003`/`LG004`), there is no Lean C
parser joint for stage (b) (same joint as A2), lock calls live only at the
top of a root continuation, and atomics/volatile/foreign calls sit outside
the direct fragment. Wiring the printer into `gabbro certificate` is a
follow-up (CLI left read-only on purpose).

## Where the task as written is wrong (or conflicts)

1. The wave preamble casts this lane as an independent reviewer that "does
   not change any existing file", while the task scope explicitly orders
   extending the four Rust files. The task wins for its named files; I
   changed only `corrcert.rs` among them, plus the mandated new Lean file,
   its one import line, and this report.
2. "Produces the simulation" cannot be a `theorem`: `SimC` is a `Type`
   structure, not a `Prop`. The producer is the `def`
   `simpruef_liefert`; the `Prop`-level soundness is `simpruef_tab`. The
   `ZEUGE` name `simpruef_124_zeuge` is the witness itself (checker
   premises jointly on the contended two-thread run, memory `privA[0]`
   `0 → 7`); no further `_zeuge` companion is owed.
