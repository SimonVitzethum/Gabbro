# MUSE-REPORT-59: syscall surface document and guardians (lane S1)

Branch: `muse/59`. Scope: documents + Python guardians only (Rust-free,
Lean-free, per task). No existing theorem touched; `./lean-bau` not run
(no Lean change — nothing to build).

## What I did

1. **Guardians first (rule 14), then the document.**
   - `instrumente/pruefe-wortschatz.py`: counter-direction probe label table
     `ETIKETTEN` extended with `("Fremdkoerper", "Foreign")` and
     `("Systemrufe", "Syscalls")` — the new vocabulary row labels in both
     languages, before the document moved.
   - `instrumente/pruefe-englisch.py`: new `SYSCALL_WORTE`
     (`syscall abi arch number regs clobbers errors kernel`) + one speech-test
     line (`syscall-Worte bleiben frei: ja`): no future keyword may sit in the
     German function-word list.
   - `instrumente/pruefe-grammatiktafel.py`: read in full; needs no pattern
     change (registers are `pruefe-wortschatz.py` terminals, `zaehle-absagen`
     forms, checker `Absage::fehler` texts — all read, none copied).
2. **New `SYNTAX.md` §12.1 `syscall`** exactly per PLAN-SYSCALL.md §1:
   `syscalldecl` production in §1 beside `entrydecl` (same style:
   `abi/arch/number`, `regs in/out`, `clobbers`, `errors` with new `errmap`
   rule, `requires/ensures/effects`, `assume…falsifier | kernel path`),
   wired into `item`; checks (arch vs declared arch A005 / x86_64-only,
   register map G4/G7, total error map, assume-or-kernel); PLAN example
   verbatim as excerpt (ends with `…`, so `korpus::messe` treats it as
   excerpt, not translation unit); attribute/Lean row (`D.Ax` + `sysabi`);
   marked "specified, not yet implemented by the checker («SS-1»)" in the
   section head, the §1 comment, and the table row.
   Vocabulary table: new row `Fremdkoerper syscall abi number errors kernel`
   (`arch`/`regs`/`clobbers` already stood in the table); Lexis gets rule
   **G6b** naming the five as specified-not-lexed.

## Before / after numbers (every guardian that reads SYNTAX.md)

| guardian | before | after |
|---|---|---|
| `pruefe-wortschatz.py dokumente/SYNTAX.md` | 221 EBNF / 221 table + 4 Sonderformen, probes green | **226 / 226** + 4 Sonderformen, speech + counter-direction green |
| `pruefe-syntax.sh` EBNF branch | 161 rules, 0 open | **163 rules** (`syscalldecl`, `errmap`), 0 open; forbidden/prose/speech branches green; final `cargo build` stage ABBRUCH rc=127 (`cargo` not on PATH — environment, pre-existing, unchanged) |
| `pruefe-grammatiktafel.py` | not runnable here (`korpuslauf` needs `cargo`; `FileNotFoundError`, pre-existing) | unchanged — no pattern edit needed; new words are UNGEDECKT-by-construction until S7 corpus; S7 must re-run |
| `pruefe-englisch.py` | speech/readability/area probes green; ratchets red (7904/7881 comments, 1085/1069 instruments, 24/23 feeders, 1/0 sink) | probes green incl. new `syscall-Worte bleiben frei: ja`; ratchet figures **identical** (my added comment lines contribute 0 German lines, measured) |
| `pruefe-kennungen.py` | ALL PASS, 303 codes | ALL PASS, 303 codes (no new codes added) |
| `pruefe-zahlen.py` | unreachable here (register entry runs `cargo`; `FileNotFoundError`, pre-existing) | no entry change needed (State table is prose `**161**`/`**226…**` — not `KENNZAHL` bold-in-cell; verified the row carries no bold number) |
| `zaehle-wortschatz.py` (kw.rs/positions) | 224 words, 16 with reason, 346 positions / 225 terminals / 161 rules | **unchanged 224/16** (kw.rs untouched — S5 owns it), **363 positions / 230 terminals / 163 rules** |
| `./cargo-pruef` (S5 handoff) | exit 0, 0 failing (stashed baseline re-run) | **exit 101, 2 failing**: `wortschatz.rs::lexer_und_syntax_md_fuehren_denselben_wortschatz` + `::jedes_ebnf_terminal_ist_ein_wort`, both on exactly `{abi, errors, kernel, number, syscall}` — the specified-not-lexed set, nothing else; all other suites green |

## What remains open / handoff to S5+S7

- S5 must add the five `kw.rs` entries (+ `faengt_item_an` arm, parser,
  named refusal): then the two red `wortschatz.rs` tests and the
  `zaehle-wortschatz` marks move by construction. Until then the red is the
  receipt for G6b, booked in SYNTAX.md Lexis.
- S7 must add the corpus carrier(s) for the new words and re-run
  `pruefe-grammatiktafel.py` (needs `cargo`+`cc`; not runnable from this lane).
- State-table cells still say `**161**` rules (now 163) — prose, unguarded,
  deliberately left for the lane that can run the full `pruefe-syntax.sh`
  with cargo; the vocabulary cell was updated to 226 because
  `pruefe-wortschatz.py` is runnable here.

## What I believe is wrong in the task

- "Check with every guardian listed in CLAUDE.md that reads SYNTAX.md"
  over-counts: CLAUDE.md names no guardians explicitly; the actual
  SYNTAX.md readers found by grep are `pruefe-wortschatz.py`,
  `pruefe-grammatiktafel.py`, `pruefe-syntax.sh`, `pruefe-zahlen.py`
  (reach only), `korpus.rs` tests, `zaehle-wortschatz.py`,
  `fuzze-grenzen.py`, `leite-grammatik.py` — all covered above as runnable.
- The six-word list (`abi arch number regs clobbers errors`) misses
  `syscall` (header) and `kernel` (the pairing alternative): both are new
  terminals needing vocabulary rows and lexer entries. Shipped as eight
  words (`arch`/`regs`/`clobbers` pre-existing), G6b books five as
  specified-not-lexed.
- "Keep `pruefe-englisch.py` exactly as red as before" understates the
  instrument risk actually present: the guardian is red in four ratchets
  (comments 7904/7881, instruments 1085/1069, feeders 24/23, sink 1/0),
  and every added comment line could lift one. Measured: +0 lines.
- Rule 14 vs S1 scope tension is real: the vocabulary ratchets
  (`zaehle-wortschatz.py` marks, `wortschatz.rs` tests) count `kw.rs`,
  which S1 must not touch — so a pure-S1 tree MUST go red there. Resolved
  by documenting the red as the S5 handoff (G6b), not by weakening it.
