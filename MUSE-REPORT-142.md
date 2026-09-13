# MUSE-REPORT-142 (lane 142, docs lane — SYNTAX.md on the new stand)

## What I did

Rewrote `dokumente/SYNTAX.md` §16 and the "Open items" section for the proved
goal over machine G. Docs-only lane: no Lean, Rust, or corpus file touched
(`git diff --stat`: `dokumente/SYNTAX.md`, +132/−63).

- **§16** (was: `zwei_fehler`/`kein_wettlauf` over traces plus the twelve items
  of 2026-09-09): now §16.1 the theorems as they stand — `ziel_ort_geraet`
  (`ZielOrtGeraet.lean`, statement in words and as the Lean name, `ziel_ort` /
  `ziel_ort_voll` / `ziel_ort_voll_lokal` as legs, witness
  `ziel_ort_geraet_zeuge`, axioms `propext`/`Classical.choice`/`Quot.sound`
  only), `rennfrei_g` + `rennfrei_g_nah` (`RennfreiG.lean`, witness
  `rennfrei_g_zeuge`), `frame_schritte_beschraenkt` + `kosten_passt_deklaration`
  + `frame_schritte_pruefer` (`KostenG.lean`), and the single-body legs
  (`zwei_fehler`, `exec_rahmen`, outcome table kept); §16.2 premise classes
  (USER / HARDWARE / DECIDABLE / START / DATA) with the surface construct or
  checker rule behind each decidable premise — fragment (`gOk`,
  `programmImFragmentG_ok`), footprint (`fussOrtGB`, `fussOrtGB_ok`, surface
  `effects`/`requires Held(L)`/`H007`/`W001`/`W002`), start exclusivity
  (`concurrent` held sets, `audit_startExklusiv_const`), costs (`costs`/
  `bounded`/`per_pass`, checker `K001`/`K005`–`K009`, `kosten_passt_deklaration`)
  — plus the named hardware assumptions (`GutO`, `RegLokal`, the scheduler
  assumption for lock waiting: fair scheduling + bounded hold time, named and
  proved nowhere, surface `held <= N ops` checked `K002`/`K004`); §16.3 what
  the three theorems do NOT cover (SATZKARTE §11.3 in this file's language:
  fragment edge, carrier-less declarations, locks-block-only readers, non-local
  oracles, waiting/termination/time, converse adequacy, lock-free sharing,
  witness shape, user-copy hazard, parser, handler scheduling); §16.4 maps the
  old twelve items 1–12 onto the new stand, so every older `§16 (n)` reference
  in §§1–15 (§1, §2 `§16 (4)`, §3 `item 12`, §11 `§16 (7)`/`(1)`/`item 10`/
  `(2)`) keeps its target — no cross-reference edits needed.
- **Open items**: closed the guardians item (measured: EBNF 176/0, vocabulary
  239/239 + 4 Sonderformen; rounds in lane 129 and this lane 142) and credited
  the concurrent semantics with `rennfrei_g` (lane 130); kept the parser item,
  reworded as translation validation T3 (`PLAN-UEBERSETZUNGSVALIDIERUNG.md`);
  kept the `owner` producer (`D026`); added the user-memory region check
  (`Adressraum.lean`: region check beside the run, no user partition) and the
  lock hold bound missing from the Lean model (`KostenG.lean` CUTS, TARGET 4);
  refreshed the last item to point at §16.3 / SATZKARTE §11.3.
- §§1–15 and the grammar untouched: 18 `ebnf` blocks and 16 `gabbro` blocks
  before and after (verified via stash comparison); no EBNF terminal, vocabulary
  word, or production added, removed, or renamed.

## New definitions/theorems

None. No Lean file touched, no Rust touched.

## Guardian runs (before → after, identical)

- `pruefe-wortschatz.py dokumente/SYNTAX.md`: exit 0 → 0, output identical.
- `pruefe-syntax.sh`: exit 2 → 2, output identical (`EBNF: 176 Regeln definiert,
  0 offen`; `== SYNTAX: ALL PASS ==`; then `ABBRUCH: cargo build --tests`
  exit 127 — no Rust toolchain on this machine, pre-existing).
- `pruefe-englisch.py`: exit 1 → 1, output identical (pre-existing single German
  user message `main.rs:713`; docs prose is not in its scope).
- `pruefe-grammatiktafel.py`: exit 1 → 1 (same `cargo` FileNotFoundError).
- `pruefe-zahlen.py`: exit 1 → 1 (same `ABGESCHNITTEN` at the cargo-dependent
  entry run; no new bold Kennzahl added to table cells — verified by scan).
- Nothing redder: every delta is zero.

## Last `./lean-bau` result line

`Build completed successfully (89 jobs).` — 0 error lines. Expected: docs-only
change, no Lean source modified.

## What remains open

- The §16.2 checker-rule column is honest where wiring is missing (fragment
  Bool, footprint Bool, `StartExklusiv` have no checker rule yet — booked as
  emitter work per SATZKARTE §11.5); a Rust lane still has to implement and
  wire `programmImFragmentG` / `fussOrtGB` / `kostenPasst` per program.
- The "four marks of the second version" open item was left verbatim; its
  numbers were not re-measured by this lane.
- The `State — measured` table and §§17–21 still speak of the `Ziel.lean`
  family (e.g. §18, §21.4); outside this lane's mandate, flagged here so a
  later docs lane can carry them onto the G stand.

## Task feedback (believed wrong or imprecise)

- The brief lists `frame_schritte_beschraenkt` "in KostenG.lean" alongside the
  goal theorems; SATZKARTE §11.3 (lane 133) still books "no `KostenG.lean`
  exists in the tree". Both are outdated relative to this tree: `KostenG.lean`
  exists with `frame_schritte_beschraenkt` (:927),
  `frame_schritte_beschraenkt_tief` (:1587), and `kosten_passt_deklaration`
  (:964) — the transfer-phase merges (lanes 130–134) closed that gap. §16.1
  documents the file as found.
- The brief's "which surface constructs/checker rules establish each decidable
  premise (fragment, footprint, start exclusivity, costs)" reads as if all four
  have checker rules; only costs does (`K001`/`K005`–`K009`). §16.2 states the
  other three as Lean-decidable without a checker rule rather than inventing
  one.
