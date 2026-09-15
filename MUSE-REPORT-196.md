# MUSE-REPORT-196: TRANSFER 2 — Rust checker computes the Lean `Akzeptiert` Bool

Lane 196, wave 6. Third session on this clone: the first two sessions built the
work and ran out of time before committing. This session verified, repaired two
stale sentences, measured before/after, and commits.

## What was built (sessions 1–2, committed here)

Two missing `Akzeptiert` components now have Rust rules; both reserved codes used
(`N315`, `N316`; `N317`–`N319` stay free):

- **`N315` (`einzelnB`, `ws.Nodup`)** — `crates/gabbro-check/src/fusswache2.rs`
  (`race`): the same routine named twice as a declared start is refused at the
  second entry, idle or not. The busy shape stays `N304`'s alone; the two codes
  are exclusive by construction (`idle` flag). Poison probe
  `beispiele/gift/976-duplicate-idle-start.gab` (exactly one error, `N315`);
  positives inline (`doppelter_schreibender_start_faellt_n304` asserts no `N315`;
  the idle test asserts only `N315` fires).
- **Payload exemption removed from `N300`/`N301` (verdict P3)** — same file: two
  starts writing one unguarded publish payload are a C11 race on a non-atomic
  object (`ausgenommenB` has no payload arm; `H013` never had one). Per-core
  cells stay exempt. The `N300` note names the payload so the pairing reader is
  not left guessing why the remembered exemption is gone. Test
  `nutzlast_zwillinge_fallen_n300` flipped from silent to `N300`-alone.
- **`N316` (`antwortenB` exactness)** — `crates/gabbro-check/src/m1.rs`
  (`fn_gestalt_genau`, `enthaelt_unbekannt`, hook in `pruefe_axiom_ruf`): an axiom
  call/binding whose declared `fn(...)` answer no runtime function has EXACTLY
  (params and result through names with ranges; effects ghost, never compared;
  `Unbekannt` on either side matches by fiat; orphan with no representation at
  all stays `N312`'s alone). Poison probe
  `beispiele/gift/977-axiom-answers-near-pointer.gab` (errors `H021`, `K003`,
  `N316`; guardian class `begleitet`); positives inline (range-exact twin silent,
  orphan twin `N312`-alone).
- **`D268` pin updated** (`crates/gabbro-check/tests/paesse.rs`): the twice-named
  idle minting root now draws `D268` + `N315`; two rules, two reasons.
- **Sentence updates** in `crates/gabbro-check/src/saetze.rs`
  (`m1.signaturgenaue_antwort` new; `wirkungen.rennboden` extended to six codes).
- **Differential test** `instrumente/pruefe-akzeptiert-diff.py`: for every corpus
  program `gabbro lean-g` exports, Rust verdict (accept = none of the 20
  `Akzeptiert` codes fires) vs Lean `Akzeptiert` decided component by component
  (`frag`, `abg`, `fuss`, `stufen`, `sperrOrte`, `wurzeln`, `einzeln`, `renn`,
  `antworten`, `gesamt`) via `./lean-probe`. Disagreement = finding, exit 1.
  `--selbsttest` speaks both directions (104 agrees; doubled start refuses at
  `einzeln`).

## What this session changed (repairs)

1. `saetze.rs`: the carried sentence "beispiele/108 … newly refuses with N303"
   is FALSE in this tree — lane 183 reworked 108 lock-free and plain `pruefe`
   (even `--paesse`) reports zero errors; the differential confirms
   rust=accept/lean=accept. Replaced with the measured sentence. A claim bigger
   than its proof is what gets a lane sent back; this one was caught before it.
2. `pruefe-akzeptiert-diff.py` component table: `einzeln` listed `N304`/`N319`
   (the lane used `N315`, not `N319`) and `antworten` omitted `N316`. Fixed to
   `N304`/`N315` and `N310`–`N314`+`N316`. Verdicts were unaffected (the
   `AKZEPTIERT_CODES` set was already right) — documentation-only, but the
   report's per-component map is what the merger reads.

## Measured numbers (before = HEAD `282a45f1` via `git stash -u`, after = this commit)

- `./cargo-pruef` first line: `== exit 0; failing tests: 0` (before unmeasured
  by me; after measured twice, plus once more after the `saetze.rs` repair).
- `./lean-bau` last line: `Build completed successfully (230 jobs).`
  (No `grammatik/` change in this lane; run once for the record.)
- `zaehle-gifttreffer.py`: before `681 angesehen — 493 sauber, 141 begleitet,
  37 verdeckt, 5 FEHLT, 1 cc, 4 abgeleitet`; after `683 angesehen — 494 sauber,
  142 begleitet, 37 verdeckt, 5 FEHLT, 1 cc, 4 abgeleitet`. Delta is exactly the
  two new gifts (976 sauber, 977 begleitet). `verdeckt` unchanged: the
  DECKE 37-vs-24 and the five FEHLT (850–854, syscall gifts expecting `C180`–
  `C184` with empty chains — another wave-6 lane's unfinished work, present at
  HEAD) predate this lane. Nothing of mine covers an old probe; nothing breaks.
- N300/N315/N316 corpus sweep (`pruefe` over `beispiele`, `messung/proben`,
  `messung/fragmente`, `messung/tor-proben`): N315 only in gift 976, N316 only
  in gift 977, N300 only in the nine pre-existing race gifts
  (704, 708, 743, 744, 760, 146, 897, 899, 964). No non-gift file draws any of
  the three. No new refusal outside the gifts.
- Differential: `--selbsttest` ok (both directions); full run
  `compared=12 skip=181 partial=0 findings=0` — all 12 exported programs agree
  (rust=accept/lean=accept). Skips are counted, not hidden (checker-error or
  `LG` export refusal). The comparison measures Rust-accepts ⇒ Lean-accepts;
  the reverse direction is pinned per-code by the gift probes.
- Guardians: `pruefe-saetze.py`, `pruefe-kennungen.py` (410 codes),
  `pruefe-englisch.py` all pass.

## Still open / not measured

- `N317`–`N319` unused by design (lock floors `StufenM` beyond `N294`'s leg and
  call-graph closure `abgAlleB` are decided by construction on the export
  fragment — named in the script as `None`, never silently dropped; if the
  merger wants explicit Rust rules there, codes are free).
- The `antworten` Lean side for `N316`-shapes: the differential's 12 compared
  programs contain no axiom-with-fnptr-answer case, so the exactness agreement
  Rust-vs-`antwortenB` on a near-miss shape is pinned only by the gift + inline
  twins, not by the sweep. A positive export carrying a range-exact axiom answer
  through `lean-g` would close that loop; none exists in the corpus.
- DECKE 37-vs-24 and FEHLT 850–854 belong to other lanes (measured at HEAD,
  unchanged by me) — reported, not owned.
- Lean side untouched: no new theorems, no rule-13 witnesses needed (Rust lane;
  rule 13's Lean-inhabitation clause does not apply, and no `ZEUGE:` line names
  a Lean target).

## What I believe is wrong

- Nothing in the task statement itself. One trap for the merger: the task's
  component list predates the `ausgenommenB` payload-arm removal — any wave-6
  text still promising "atomic / payload" exemption for `N300`/`N301` (older
  `fusswache2.rs` doc lines, older reports) contradicts verdict P3; this lane
  updated the code, the notes, the tests, and the sentence table, but grep for
  `payload` across `dokumente/` and `messung/` will still find the old promise.
