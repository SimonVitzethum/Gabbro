# MUSE-REPORT-112 — Translator declaration (PLAN-ERWEITUNG.md §6 lane E3)

Lane 112, 2026-09-12. The DECLARATION side of translators: a library declares,
per run-time function, a total effect-free map from the region AST to the payload.
Running it needs the compile-time evaluator (lane 111/E5) — not this lane.

## What was built

**Surface (`dokumente/SYNTAX.md` §7.2, new `translatordecl` EBNF rule, vocabulary
`translator` + `for`):**

```gabbro
translator build for kernel(region : KernelTab) -> KernelTab
    effects { pure }
    costs <= 8 ops
    decreases region.words
{
    return region;
}
```

One translator per `library fn`, in the same module, linked with `for`. Grammar fixes
what the signature promises (one parameter, a Gabbro block — `P044` for anything
else, the same rule that holds a `library fn` to real code) and leaves what must be
REFUSED to the checker (missing/impure `effects`, missing `decreases`, missing or
foreign result).

**Parser (`crates/gabbro-syntax`):** `Kw::Translator`, `Kw::For` (both `ctx`, each
with its reason block); `FnDecl.translator_fuer: Option<Ident>`; `translatordecl()`
parsing into an ordinary `ItemArt::Funktion`, so every pass checks the body like any
function body; `Kw::Translator` in the `pub` list, the item dispatch and
`faengt_item_an`.

**Checker (`crates/gabbro-check/src/namen.rs`, lane numbers N200–N204):**

| code | rule | site |
|---|---|---|
| `N200` | `library fn` with a payload type and no translator | the function (skipped when no `payload` clause — `P043` already fires) |
| `N201` | a second translator for one function, or one naming no library function | the translator |
| `N202` | translator without exactly `effects { pure }` | the translator |
| `N203` | translator without `decreases` | the translator |
| `N204` | translator result naming another table than the payload (or no table); skipped when the payload itself names no table (`N060`) | the translator |

Plus: a translator hull reaching `extern`/`raw`/`prim`/`asm` falls under the
existing `N059` (same rule, translator named); `N069` (resolved call, still refused —
nothing runs translators yet) now names the translator that WOULD run the region.

**Probes:** clean `beispiele/94-uebersetzer-erklaert.gab` (identity translator),
`beispiele/95-uebersetzer-vertrag.gab` (with `requires`); gift `870` (call → only
`N069`, naming the translator), `871` (`N200`), `872` (`N202`), `873` (`N203`),
`874` (`N204`); 10 new `translator_*` tests in `paesse.rs` (exact sets, incl.
`N201` duplicate/dangling, `N059`-on-translator, `P044`-on-translator, `N202`+`E001`
for a missing clause); `820` and `beispiele/80` gained translators (stay exact:
`N069`-only / clean); `N200`–`N204` in the `korpus.rs` BENANNT list; two measured
sentences in `saetze.rs` (`namen.uebersetzer_einzigkeit`, `namen.uebersetzer_signatur`).

**Registers:** PASSREGISTER.md lane entry (132 sentences / 124 measured / 335 codes /
280 claimed); README (78 clean, 590 poison, 335 diagnostics, 168 EBNF, 230/230 vocab,
blind row 78/170/24/12); DONE.md counts; TODO.md figures + E3 parentheticals;
`zaehle-wortschatz.py` mark 231→233; `pruefe-syntax.sh` VERBOTEN list lost `for`
(documented at the site — it is vocabulary now; the `for` loop stays refused by
`P035`, pinned by sprechprobe).

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (final, on the committed tree).
- `./lean-bau`: `Build completed successfully (61 jobs).` — no Lean files touched.
- Guardians green: wortschatz (230/230), syntax.sh ALL PASS (168 rules), kennungen
  ALL PASS (335), saetze 0, grammatiktafel 0/230 UNGEDECKT, todo README/TODO rows
  for my numbers.
- Emission: `94`/`95` emit C that `cc -Werror` accepts.

## Findings (measure, don't believe)

1. **A translator between two DIFFERENT tables has no checkable body today.**
   Measured: `M140` is nominal (a value of table `Q` never answers for table `P`),
   tables have no pure constructor (`M107`), and a carrier read under `pure` is
   `E010`. So only the identity shape (region AST already in payload form) passes
   the ordinary checker. The positive probes use it openly; SYNTAX.md §7.2 books
   the gap (translation-time value construction is lane E5's evaluator, served by
   lane E4's arena). The DECLARATION side built here does not need the gap closed:
   linkage, signature and result-typing are all checkable now.
2. **A new match arm answering `FnDecl` by value cost 32 KB of `item()` frame and
   broke the depth guard.** Measured with gdb: `item()` frame 57 KB (≈65 KB per
   nesting level), so 80 nested modules overflowed a 2 MB test thread before `P038`
   could fire (`die_beiden_wachen…` went red; baseline fits 80 levels). Fix: the
   translator arm returns through `translator_item() -> Erg<Item>`, so the `FnDecl`
   temporary lives in a helper frame that never nests with itself. Lesson for the
   next lane that adds an item form: big by-value declarations must not be built
   in `item()`'s frame.
3. **`for` as a contextual word needed two reader repairs:** the abolished-form gate
   (`for (i)` must stay `P035`) now reads name-usable words but skips places
   (`for = 1` stays an assignment — the wortschatz name test demands it); the
   syntax guardian's VERBOTEN list dropped `for` (above).
4. **Pre-existing drift, not mine (measured at baseline by stash):**
   `pruefe-klauseln.py` fails on E1's unread `LibraryCall.region` (no pass reads
   `.region`; my `translator_fuer` IS read by namen.rs); `pruefe-vergabe.py`
   breaches 23-vs-20 / 77-vs-68 without any of my codes among the candidates
   (baseline: 24/80); `pruefe-emission.sh` fails on stray roots (`Claude outputs/`,
   `halde.gab`); `pruefe-zahlen.py`'s self-figures jitter between runs (88/86
   entries, 180/181 unwatched vs booked 89/179). I rebooked nothing of others'.
5. **On the task text:** "its result type must equal the function's payload type" —
   implemented as same-table resolution (either side may be spelled through another
   module path); a `u32`-typed translator result against a broken (`N060`) payload
   pins no `N204` (one refusal per defect). Calls TO a translator are ordinary
   calls (it is an ordinary function for the checker) — not refused; running it at
   translation time is E5's stage to own.

## New names (Rust; no new Lean)

- `Kw::Translator`, `Kw::For` (`kw.rs`); `FnDecl.translator_fuer` (`ast.rs`);
  `Parser::translatordecl`, `Parser::translator_item` (`parse.rs`).
- `namen.rs`: `struct Uebersetzer`, `fn benannte_tabellen`,
  `fn pruefe_uebersetzer_signatur`; codes `N200`–`N204` (+ reused `N059`, `P044`).
- `saetze.rs`: `namen.uebersetzer_einzigkeit`, `namen.uebersetzer_signatur`.

## Open (for E5, not this lane)

Running translators (compile-time evaluator); translation-time value construction
for distinct tables (finding 1); error mapping region↔payload (lane E7); direct
calls to a translator are ordinary calls today (finding 5).
