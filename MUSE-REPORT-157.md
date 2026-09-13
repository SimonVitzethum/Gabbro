# MUSE-REPORT-157 — T3 part 3: Lean deep item parser + probes

Lane 157, branch `muse/157`. Task: items in depth in the Lean
parser (SYNTAX.md sections 1-2, 6, 9-14) in a NEW file
`grammatik/Grammatik/Parser/ElementTief.lean` (Element.lean
untouched except nothing — no changes there at all), with the
same probe discipline as parts 1-2 (literal token lists; token
pin + tree pin; STRUCTURAL fuel-indexed recursion only; kernel
`decide` stays small), plus one complete small corpus file end
to end.

## What was built

Two new files (imports appended at the end of
`grammatik/Grammatik.lean`):

- **`grammatik/Grammatik/Parser/ElementTief.lean`** (3458 lines)
  — surface types `STyp` (9 ctors: `atom`/`pfad`/`ptr`/`index`/
  `bereich`/`reihe`/`wickelnd`/`einbettet`/`roh`), `SEffekt`
  (9 effect arms), `SKlausel` (14 clauses incl. `wirkung`),
  `FnSig`, `SFeld`, `SRegFeld`, `SReg`, `STrans`, `SGruppenInv`,
  `SKonstWert`, `STabTeil` (6), `SGerTeil` (4), `SAnKlasse`,
  `SProfEintrag`, `SRegBind`, `SBootSchritt`, `SWeg`,
  `SEingang`, `SCheck`, `SHerkunft`, `SSyscall`, `SItemTief`
  (all 30 `ItemArt` arms — same shape as `SItem` but every body
  structured), kernel-reducible `beq*` for each (all two-function
  `mutual` blocks plus plain helpers, per the part-2 CUTS-11
  finding), and fuel-indexed readers for every production:
  `parseTyp`/`parseTypNach`, `parseEffekt`/`parseEffektListe`,
  `parsePredListe`, `parseKlausel`/`parseKlauseln`,
  `parseParams`/`parseFnSig`/`parseErgebnis`/`parseFnRest`,
  `parseFeld`/`parseFeldListe`/`parseFeldFolge`,
  `parseReg`/`parseRegRest`/`parseRegFeld`/`parseTrans`/
  `parseSchritte`/`parseSchrittPlatz`/`nimmBisPfeil`/
  `parseGruppenInv`, place/binding/path/boot lists, and one
  `parse*Tief` per item form with `parseItemsTief`/
  `parseItemTief`/`parseItemKopfTief`/`parseTopTief`/
  `beqTopTief`. Probes live in `ElementTiefProben.lean`.
- **`grammatik/Grammatik/Parser/ElementTiefProben.lean`** (1281
  lines) — 118 ground `decide` theorems: `t01`–`t58` lex pins
  (`tNN_lex`) + tree pins (`tNN`), each citing its corpus site
  and `ast.rs` counterpart, plus the end-to-end pair
  `tEnd_lex`/`tEnd`. Every one of the 30 item forms is probed;
  `SCheck`, `SSyscall`, `SEingang`, `SWeg`, transitions,
  invariants, reasons, arenas, formats, banks and all 14
  contract clauses ride with corpus text.

Target met: `tEnd` parses **beispiele/112-register-traeger-bewacht.gab
whole (38 lines — measured the smallest whole file with a
table, a lock and contracted functions; `108` is next at 41)
into `modulT` + table + lock + device + two contracted
functions with nothing skipped.

One existing file changed, minimally and loudly:
**`grammatik/Grammatik/Parser/Lexer.lean`** gains the missing
keyword `depends` in `wortschatz` + `schluesselTafelC`
(242 → 243 words). The probe discipline caught it: `t03_lex`
failed on `depends { Zustand }`, and SYNTAX.md (`Vocabulary —
closed, 243 words`) plus `kw.rs` agree against the Lean list.
`lex_keywords` re-verifies the whole table by `decide`.

## Verification

Last `./lean-bau` result lines:

```
== lake exit code: 0
== 0 error line(s) in the COMPLETE output
Build completed successfully (144 jobs).
```

`./lean-probe` on all three touched files: exit 0.
`#print axioms` on `parseTopTief` and `tEnd`: only `[propext,
Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` (two grep hits are the word "axiom"
in a doc comment and a corpus string). No theorem has premises
— all 118 are ground `decide`s — so rule 13 needs no witnesses
(no ZEUGE target, no universal-over-syntax premise anywhere in
the new files). `pruefe-kennungen.py`: ALL PASS.
`pruefe-englisch.py` exits 1 identically with and without my
changes (pre-existing: 2 of 2187 Rust messages German).

## Findings (measure, don't guess)

1. **`depends` was missing from the Lean vocabulary** (above):
   lane 140 added the checker rule without the lexer word.
2. **`regdecl` takes no `;`** (grammar + corpus agree); first
   cut demanded one. **`check` takes bare `measures`/`gates`
   lists** (`parse.rs` `placelist`/`identlist`); first cut
   wanted braces. **Reason cases are newline-separated**;
   first cut took commas only. **`cost O(e)`'s `O` is an
   identifier in both lexers** (`kw.rs` has no `O`).
3. **Two `parseOr` traps in transitions**: `a -> b` reads as
   arrow-field, so the step place rides restricted
   `shiftplace` (`parseSchrittPlatz`) and the `from` side is
   split at the top-level `->` first (`nimmBisPfeil`).
4. **Three `{`-list readers re-demanded `{` on recursion**
   (fields, reg-fields, carriers, bindings, paths) — every
   multi-member list failed; single-member probes stayed green
   and hid it until `t35` (`concurrent` with two members).
5. **Single-letter rights are keywords**: `w` (t05), `x`, `r`;
   `result`, `O`... i.e. `result` is a word, `O` is not.
   Four probe transcriptions tripped on this; the lex pin
   caught each loudly.
6. **Heartbeat prices** (measured): `t26_lex` needs 800000,
   `tEnd_lex` 1600000 (default 200000 fails) — whole-item
   lexing cost, same family as lane-135 finding 6.
7. **Hand-nested terms need a paren counter**: two committed
   probes carried one slip each (t50/t51); all new single-line
   terms are balance-checked by script before probing.
8. **One red commit stands in this branch's history**
   (`b4295cd1`, t54 lex pin): committed before re-probing,
   fixed green in the next cycle. Against rule 8 — booked
   here, not hidden.

## What I believe is wrong in the task

Nothing load-bearing. Two notes: (a) "239 words" in older
task text vs 242 vs now 243 with `depends` — the count moves
with the language, the table is the truth; (b) the 60-line
skeleton rule $TMPDIR-vs-scratch: debugging token shapes
needs `#eval`, which must live in the tree for `./lean-probe`
— I used short-lived `grammatik/Kratz157.lean` files, always
removed before committing (none remain; `git status` is clean
of them).

## Open (for the CUTS blocks, summarized)

No `pred` reader (quant/member/reaches/`=>` refused — every
corpus invariant quantifies; member shapes probed with
quantifier-free bodies); `structty`/`variants`/`fnptr` and
`asm`/`bank` bodies ride raw; `by`/`retires`/`deadline` tails
ride printed strings; trailing commas + empty `effects {}`
accepted beyond `parse.rs` ([SUPERSET], itemized); no semantic
checks anywhere (shapes only); unprobed-but-supported:
table `owner`/`shared`, entry `ist`/`bounded`/`via`,
translator/axiom extras, `publishes nothing`, braceless
`group`, walks with invariants.
