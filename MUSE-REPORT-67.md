# MUSE-REPORT-67: English guardian + stale Erhaltung header

Lane 67 (Rust + Lean doc lane). Branch `muse/67`.

## What I did

1. **Report-string fix in `crates/gabbro-check/src/certemit.rs`** (the one
   genuine German-prose feeder hit). Changed two user-visible report words
   plus the two doc comments that named them:
   - `slot … guard darf = {}` -> `slot … guard holds = {}` (`:437`)
   - `glob … guard gdarf = {}` -> `glob … guard holds = {}` (`:406`)
   - doc `:76` `` (`gdarf`, recomputed …) `` -> `(recomputed …)`
   - doc `:85` `` (`darf`, recomputed) `` -> `(recomputed, never trusted …)`
2. **Rewrote the header comment of `grammatik/Grammatik/Erhaltung.lean`**
   (lines 1–110) in English to describe what the file actually proves.
   No definition or theorem touched. Also translated the 11 remaining
   German doc comments in §§10–11 and one stale cut label
   (`` `cInclude` `` -> `the open slot`, since `tafel_nicht_geschlossen`
   no longer exists) to English. File now has 0 German comment lines.
3. **Did NOT rename anything else**, with measured reasons (see below).

## Exact names of new/changed items

- Changed strings: `"guard darf = {}"` -> `"guard holds = {}"`,
  `"guard gdarf = {}"` -> `"guard holds = {}"` in
  `crates/gabbro-check/src/certemit.rs` (`CertExpr::sides_into` arms).
- No new definitions or theorems. No new files.

## Grep evidence per changed string (rule: grep whole tree before changing)

- `"guard darf"`: before the fix it matched only
  `crates/gabbro-check/src/certemit.rs:437` and the stage-0 booking notes
  (`messung/WAECHTER-STUFE0.md:475`, `messung/SYNTAX-ZEUGNIS-ENTWURF.md:108`
  which documents the same report line). No match in `instrumente/`,
  `crates/*/tests`, or `beispiele/`. No test reads the certificate report
  text (`grep -rn "glob.*carrier\|guard gdarf\|guard darf" crates/*/tests
  instrumente beispiele` empty). `darf_restrict` (the checker function) is a
  different token and untouched; the feeder booking in `pruefe-englisch.py`
  cites only `schablonen.rs:191` (a `Voraussetzung.durch` citation of that
  function name plus the mutation key `restrict-auch-bei-zwei-zeigern`),
  which is a proper name, not this string.
- `"guard gdarf"`: same grep, only `certemit.rs:406` plus the same two
  booking notes. `gdarf` names no variable and no field anywhere in
  `crates/` (only `certemit.rs:76,85` doc comments and the two report
  lines) — as already measured in `WAECHTER-STUFE0.md` §6.
- After the fix: `grep -rn "guard darf" crates/ instrumente/` is empty;
  `gabbro certificate` report tests (`tests/beispiele.rs:1061-1081`,
  `tests/zeugnis_injektiv.rs`) match header/wording, not these lines.

## What I deliberately did NOT change (each with the grep that forbids it)

- **Sink hit `main.rs:713` (`--mit-beweis` in `hilfe()` text, word `mit`).**
  The flag is REAL: parsed at `main.rs:1047`
  (`"--proved" || "--mit-beweis"`), routed at `:1061`, documented at
  `:768/:918/:1043`, and pinned by `crates/gabbro-cli/tests/fahnen.rs:201`
  (`zweitname: "--mit-beweis"`). Renaming the flag spelling would break that
  test and bilingual CLI policy (`erstnamen.rs`: every subcommand/flag keeps
  a German second spelling; `--proved|--mit-beweis`, `--unit|--einheit`,
  `--model|--modell` are the same pattern). The guardian counts function
  words and cannot tell a flag name from prose (its declared W10
  coarsening) — same class as the 23 booked feeder names. Decision for the
  owning lane (rename or book); I report it, I do not rename it.
- **The 23 feeder hits in `saetze.rs` / `schablonen.rs` / `lib.rs`.**
  Verified word-by-word that every hit sits inside a proper name:
  probe file names under `beispiele/gift/` (all exist on disk:
  `401-registerklasse-ohne-marke.gab`, `402-…-nach-dem-schritt.gab`,
  `403-…-schweigt-ueber-stufe.gab`, `404-…-gibt-es-nicht.gab`,
  `48-grund-mit-erzeuger.gab`, `295-zeigerziel-ohne-typ.gab`,
  `237-kanal-ohne-einloeser.gab`, `249-breaking-auf-ops-traeger.gab`,
  `351-breaking-nennt-nichts.gab`, `405-…-blank-gelesen.gab`,
  `406-falsifikator-nennt-nichts.gab`, `301-tor-ohne-paarung.gab`,
  `253/254/255-refines-*.gab`), mutation anchors in
  `instrumente/mutiere-pruefer.py` (all present: `refines-auch-an-spec-fn`,
  `refines-nennt-ins-leere`, `consuming-ohne-consumes-geht-durch`,
  `rahmen-faellt-unter-unvollstaendiger-huelle-aus`,
  `gruppenrang-aus-der-wurzel`, `adressraum-egal-am-rufort`,
  `syntaktischer-alias-geht-wieder-durch`,
  `min-akkumulator-ohne-umkehr`, `restrict-auch-bei-zwei-zeigern`,
  `verbundmarken-nur-als-menge`, `verbund-ohne-marken-geht-durch`,
  `breaking-darf-ins-leere-nennen`), sentence keys (`paarung.keine-waise`,
  `kbedingung.breaking-nennt-etwas`,
  `parser.pub-nur-wo-die-grammatik-es-fuehrt`), and citations of the
  genuinely German heading `dokumente/MESSUNGEN.md:4100`
  (`# SWEEP — die anderen Verbindungs-Invarianten, 2026-08-16`).
  `grep -rn "<each name>" crates/ instrumente/` outside `saetze.rs` /
  `schablonen.rs` finds only the anchor definitions (renames) or nothing
  (file names referenced nowhere else). A file name is not a translation
  problem, it is a rename — booked the same way in `pruefe-englisch.py`
  `:596-621` (18 names in `saetze.rs`, 4 in `schablonen.rs`, 1 in `lib.rs`).
- **Checker comment ratchet (7903 vs 7881, +22 after my fix).** The rise is
  the p04–p27 lane batch documented in `WAECHTER-STUFE0.md` §6
  (`paarung.rs` +8 new German lines at `:751-759`, `geteilt.rs` +1 at
  `:488`, plus new files `absenkung.rs`/`kostenledger.rs`/`ableitung.rs`/
  `nebeneinander.rs`/`certemit.rs`/`corrcert.rs` — the last two mine, now
  fixed: `certemit.rs` 1→0). Rewriting other lanes' design prose in a
  watcher-stage commit would trade a loud red for a quiet meaning change;
  the owning lanes own those lines. My own delta is -1 (certemit comment
  + string), verified: feeder count 24→23.
- **Instrument comment ratchet (1085 vs 1069, +16).** `pruefe-gestalt.py`
  +13 (lane 100's fresh design prose), `nachpruefer.py:71` (verbatim quote
  of the German linker diagnostic `Mehrfachdefinition von` — evidence, a
  translated quote is none), `pruefe-abstieg.py:288`
  (code identifier `` `Wenn` `` — a name), `pruefe-grammatiktafel.py:200`
  (half-English sentence continuation). No test-safe subset: no other
  guardian or test matches on these comment texts, but they are other
  lanes' words. Same verdict as `WAECHTER-STUFE0.md` §6.

## Verification results (last lines)

- `./lean-bau`: `== 0 error line(s) in the COMPLETE output` (green,
  whole project; `Erhaltung.lean` axioms unchanged:
  `entschieden`/`satz_tafel` `[propext]`, soundness theorems
  `[propext, Quot.sound]`).
- `./lean-probe grammatik/Grammatik/Erhaltung.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./cargo-pruef`: `== exit 0; failing tests: 0` (green).
- `python3 instrumente/pruefe-englisch.py`: exit 1, three ratchets remain
  red by others' deltas — feeders 23 vs 23 GREEN (was 24), sink 1 vs 0
  (`main.rs:713`, the real `--mit-beweis` flag, see above), checker
  comments 7903 vs 7881, instruments 1085 vs 1069. Full guardian green is
  therefore NOT claimed; what this lane could fix without renaming other
  lanes' artifacts is fixed and measured.

## What remains open

1. `main.rs:713` sink hit: rename `--mit-beweis` (breaks `fahnen.rs:201`
   + bilingual policy) or book the flag spelling like the 23 feeder names
   (guardian-side change in `pruefe-englisch.py`). Owning-lane decision.
2. Checker comments 7903 vs 7881 (+22) and instruments 1085 vs 1069 (+16):
   owned by lanes p04–p27 / 100 / nachpruefer / abstieg / grammatiktafel.
3. `pruefe-gestalt.py` is red on this tree independent of this lane
   (`Unterbrechung`/`Wettlauf`/`Zeugnis`/`Ziel` drifted past its table;
   new files `VertragOrtB` etc. unbooked) — pre-existing, untouched.

## What I believe is wrong in the task

- "Translate the flagged comments/strings in `saetze.rs` … Then
  `./cargo-pruef` green and `pruefe-englisch.py` green" assumes the 18
  `saetze.rs` feeder hits are prose. They are not: every hit word sits
  inside a file name, mutation key, sentence key, or citation of a German
  document heading. Translating them means renaming probe files (each with
  corpus site + anchor + citations), renaming mutation anchors (each a
  literal source line in `mutiere-pruefer.py`), or falsifying a citation —
  exactly the renames the guardian file itself (`:600-621`) and the task's
  own "WITHOUT changing any string the tests or other guardians match on"
  clause forbid. The achievable green on this lane is feeders 24→23 (the
  one real prose hit, `certemit.rs`), not 24→0.
- The task says "German prose in `saetze.rs` (and possibly elsewhere)".
  The actual prose regression is in `certemit.rs:436-437` (new file from
  the p-lane batch), not `saetze.rs`. The `saetze.rs` hits are all
  pre-booked names.

Co-Authored-By: muse-agent-67 <muse-agent-67@noreply.invalid>
