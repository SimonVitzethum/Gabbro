# MUSE-REPORT-341 — AccessList (wave-B item B1, single owner)

## What was done

Created `grammatik/Grammatik/X86/AccessList.lean` (282 lines) plus the one
additive import at the end of `grammatik/Grammatik.lean`. It is the
SINGLE owner for the access list of one G step, for both consumers named
in REVIEW-TSO.md section 5.2 (bridge D-access/L-access-complete and the IR
lowering map).

Definitions (all in `Gabbro.Grammatik.X86`, over the real source model):

- `TraegerWert D c` / `traegerWert s c`: whole-carrier value slices (table
  slot function / global value) read from an endpoint memory. The canonical
  events carry no values, so values come from the endpoint states; nothing
  is invented.
- `ZugriffEintrag D`: `.liest c v` (pre-state value) / `.schreibt c v`
  (post-state value).
- `ZugriffBefund D`: `.voll entries` or the explicit refusal `.luecke`
  (a constructor, never a silent empty list).
- `eintraege M M' f`: maps the decided `zugriffe` trace delta to entries.
  No new evaluator, no second IR, no duplicated rule inversion.
- `accessList M M' f := .voll (eintraege M M' f)`: THE function both
  consumers cite.
- `IstRMW M u g := ExchangeKopf M u g` (MaschineW.lean): RMW-ness comes
  from the exchange head, never from a behavioural heuristic.
- `pruefeBefund : ZugriffBefund D -> Bool` (voll = true, luecke = false):
  validator admission; consumers may proceed only on `true`.

Theorems:

- `eintraege_liest`: `LiestG <-> exists liest-entry` [propext, Quot.sound].
- `eintraege_schreibt_aufgezeichnet`: recorded write `<-> exists
  schreibt-entry` [propext, Quot.sound].
- `schreibG_voll`: `SchreibG <-> entries-or-changed-memory` — the
  unrecorded-change disjunct stays explicit [propext, Quot.sound].
- `zugriffG_voll`: `ZugriffG <-> read/write-entries-or-changed-memory` —
  the completeness lemma both consumers cite [propext, Quot.sound].
- `accessList_kein_luecke`, `accessList_besteht`: the owner never refuses
  its own extraction [propext].
- `luecke_faellt`: PROVED REFUSAL, `pruefeBefund .luecke = false` [propext].
- `exchange_rmw_voll`: every exchange step yields `IstRMW`, its read entry
  and `SchreibG` — reuses `exchange_liest_schreibt` (RMW.lean) instead of
  duplicating the 70-case inversion [propext, Classical.choice,
  Quot.sound].
- `exchange_zwei_liest`: exchange step plus a second recorded read carrier
  yields two distinct read entries; all four premises used [propext,
  Classical.choice, Quot.sound].
- `accessList_ta_zeuge`: CONCRETE WITNESS on the reached `taP` run (29
  steps): step 24 reads `flag` (recorded event, hence a `liest` entry),
  step 16 publishes `flag` 0 -> 1 (memory change), the same run writes
  table `tab[0]` 0 -> 1 (nondegenerate), post-write value of `flag` is 1
  [propext, Classical.choice, Quot.sound].

## Verification

- `./lean-probe grammatik/Grammatik/X86/AccessList.lean`: 0 errors.
- Full `./lean-bau`: build completed successfully (386 jobs), whole project
  green.
- Axiom probe `#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel`:
  `[propext, Classical.choice, Quot.sound]` — unchanged.
- All new theorems' axioms are subsets of the standard three (see
  `#print axioms` lines at the file end).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every theorem premise
  is used; contracts keep actual values (no `forall`-away quantification);
  changed files only: `grammatik/Grammatik/X86/AccessList.lean` (new),
  `grammatik/Grammatik.lean` (+1 import line).

## What remains open (see CUTS in the file)

- Per-rule SYNTACTIC classification for the ~69 non-exchange rules (the
  D-lower micro-event labels): consumers use the generic lemmas instead.
- Recorded-write entry of exchange not re-derived (would duplicate the
  inversion); `SchreibG` form kept.
- No concrete two-carrier exchange RULE application built (needs full rule
  premises); conditional form plus concrete run witness instead.
- Byte values, alignment, tearing, TSO visibility (lanes B2/B4); no TSO
  bridge, no IR map, no source-to-bytes claim; shared IR 287 pending.
- Consumer citation (bridge D-access, IR LowerMap) is an OPEN interface
  until those lanes cite it.

## What I believe is wrong (task reading)

- The plan's "(reads+values, writes+values, RMW flag)" suggests values
  live in the access record; in the actual model (`Ereignis`,
  Semantik.lean:61) events carry carrier plus write-flag only, so values
  are endpoint-memory slices here. If the bridge needs per-access W
  message values (`wahl`), that mapping is bridge work, not extraction.
- "Closes: O-access/D-access" overstates: this file closes the ownership
  (one function, completeness stated once) and the exchange instance, not
  all ~70 per-rule syntactic instances. The report states the bounded
  claim; full closure needs the citing consumers plus the OPEN items.
