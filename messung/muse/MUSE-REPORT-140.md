# MUSE-REPORT-140 (lane 140: device carriers `rtraeger` in the language)

Rust lane + SYNTAX.md. The goal theorem admits register reads under the hardware
assumption `RegLokal` and the decidable footprint check `fussOrtGB`; the surface had
`device`/`reg` but no way to name a register's device-state carriers. This lane adds
it: `depends { C1, C2 }` on `reg`, checked, with the `RegLokal` assumption per
register in the manifest. No Lean file touched (transfer lane: the model already
exists in `ZielOrtGeraetSem.lean`).

## What was built

1. **Syntax** (`dokumente/SYNTAX.md` §10, guardian patterns first): `regdecl` gains
   `[ "depends" "{" [ carrier { "," carrier } [ "," ] ] "}" ]`, new rule
   `carrier = ident [ "." ident ]`. New contextual keyword `depends`
   (`crates/gabbro-syntax/src/kw.rs`, `Depends`, with the ledger reason the
   word-count ratchet demands). Vocabulary table + counts (240 terminals/words,
   177 rules). Design: BARE carrier names only -- Lean's `rtraeger` is
   `List (Tab ⊕ Glob)`, and `GleichAuf`/`fussOrteG` are carrier-granular (see §5
   for why the task's dotted sketch was refused).
2. **Parser** (`parse.rs::regdecl` + `carrier()`): `RegDecl::depends: Vec<Ort>`
   (the surface of `D.rtraeger`; empty = no carriers, check vacuous). At most
   one `.field` suffix parses; deeper forms are parse errors.
3. **Checker** (`namen.rs::geraetetraeger_pruefen`, one file per `pruefe-kennungen`;
   reuses `m3::geraetetabelle`/`griffe_von`/`ort_register` and
   `aufrufgraph::held_aus_pred`, no second registers):
   - `N255` unknown carrier name (house answer N033/N053: unit declarations +
     `use` tails; outside the cut is refused);
   - `N257` declared but no carrier (lock/device/register/bank/function);
   - `N258` dotted place (`T.feld` parses, is refused, never truncated -- W16);
   - `N256` per (function, read site, carrier): carrier declared `writes`
     somewhere (the surface of `D.schreibt`/`D.gschreibt`, `spec fn` excluded)
     but no signature-held lock guards it (`requires Held(L)` with the carrier
     in `L`'s `protects`). A `locks`-block-only taking does NOT count (the G
     machine has no bare lock steps, SATZKARTE §11.3); the check is per function
     over its own body, mirroring `fussOrteG`. `N259` reserved for the writer
     side (`hWatch`/D6/`H007` territory).
   Sentences `namen.geraetetraeger_nennt_traeger` (N255/N257/N258) and
   `namen.geraeteleser_haelt_wache` (N256) in `saetze.rs`.
4. **Manifest** (`manifest.rs::reglokalannahmen` + `reglokalklasse`): one
   `reglokal.<device>.<reg>` line (`<device>.<bank>.<reg>` for banks) per
   register WITH its carriers, including clauseless registers (empty carriers
   still claim locality). Class structural (`NichtFalsifizierbar`, E6 reading),
   sixth construction site (`pruefe-unfalsifizierbar.py` 5→6).
5. **Probes/examples/tests**: gift `925` (N255), `926` (N256 bare), `927` (N257),
   `928` (N258), `929` (N256 wrong-lock twin) -- each falls with its code ALONE
   (1 error, 0 hints); `beispiele/112` (guarded reader, written carrier) and
   `/113` (unwritten table+global carriers, two registers) -- both clean, both
   emit and compile under `cc -Werror` at `-O0`/`-O2`; `tests/geraetetraeger.rs`
   (8 snippet tests incl. the locks-block-only N256 shape, which has no gift
   file); reglokal manifest test; N255-N258 in the korpus BENANNT list.
6. **Census numbers** (all measured, not added): README (91/91 examples, 362
   diagnostics, 177 rules, 240/240 words, 623 poison, 232/232 emit, 1559
   ceremony sites), DONE, TODO (146 sentences claiming 311 codes, 362 awarded),
   PLAN.md A-census 67→97 (30 generated reglokal lines over `beispiele/*.gab`),
   ZEREMONIE N 1548→1559 (+11 from the 7 new files, verified by removal run),
   emission bookings (F02 3→20, F04 3→26, b12/b20 0→2, b37 0→1), emission mark
   89→91, wortschatz mark 242→243.

## Verification (final state)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (incl. 8 new + 1 manifest test,
  gift 925-929, examples 112/113 in both directions).
- `./lean-bau`: `Build completed successfully (89 jobs)` -- `grammatik/` untouched.
- `./emission-pruef`: `EMISSION: ALL PASS -- 35 durchgestochen, 232 von 232`.
- Guardians: wortschatz 240/240, zaehle-wortschatz 243, saetze (55 ohne Satz
  unchanged), kennungen ALL PASS (N:91), vergabe (29/84 unchanged), grammatiktafel
  GRUEN (0/240), unfalsifizierbar ALL PASS, syntax ALL PASS, todo README/DONE clean,
  zahlen: all four lane-140 findings closed.
- Pre-existing reds left untouched (verified identical on stashed baseline where
  applicable): `pruefe-englisch.py` exit 1 (main.rs:713 message), syntax Warnungen
  branch (referenz snake-case), zahlen TODO.md staleness (170/233/89/179/~~169~~),
  PFLICHTEN-H/fremde-Ruempfe/Nahtstellen drift, README-zeremonie patterns,
  PASSREGISTER/mutation Suchweg-ab.

## Open / for later lanes

- Cross-unit writes: the unwritten disjunct reads this unit's declared `writes`
  (N025/N038 reticence, booked in the sentence). A carrier written from another
  unit is missed.
- `transition` mirror reads are not counted as register reads (Lean `regs`
  doesn't list them either -- consistent, but worth a look by a Lean lane).
- Shared vs exclusive `Held` strength is accepted as held (H001's question).
- The `A_p` share / `A_u = 2 of 45` prose in PLAN.md was NOT re-measured: 30 new
  unfalsifiable-by-structure lines entered the census. Simon's decision whether the
  share denominator moves.
- N259 free for the writer-side guard lane.

## Where the task was wrong (or underspecified)

- The sketch `depends { dev.state }` names a SLOT. The model has no slots
  (`GleichAuf` is carrier-granular), so a dotted entry cannot mean anything the
  theorem reads. `carrier` parses one optional suffix and `N258` refuses it by
  name instead of truncating it. If per-slot carriers are ever wanted, the Lean
  model moves first.
- Gift `929` is a second `N256` probe (wrong lock), not a fifth rule: four rules
  cover the decidable surface; the remaining number is booked (`N259`,
  writer side) rather than spent on a duplicate check.
- "A function reading R holds ... a lock guarding them, or they are written by
  no function" is per (function, carrier) in the checker, while `fussOrtGB` is
  per (function, carrier) over `fussOrteG` -- exact mirror, except the checker
  reads declared `writes` where Lean reads `D.schreibt`: the lowering that fills
  `D` from declarations is a later (UMSETZUNG) lane's business.
