# MUSE-REPORT-59: syscall surface document, guardians, and the P042 refusal (lanes S1+S5 Silver)

Branch: `muse/59`. Reviewer feedback on the S1 commit (`87b4b7d`, red
`./cargo-pruef`) is closed in this same lane, in the smallest form the
review asked for. No Lean change — `./lean-bau` not run, nothing to build.

## What I did

1. **Guardians first (rule 14), then the document (S1, commit `87b4b7d`).**
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
   excerpt, not translation unit); attribute/Lean row (`D.Ax` + `sysabi`).
   Vocabulary table: new row `Fremdkoerper syscall abi number errors kernel`
   (`arch`/`regs`/`clobbers` already stood in the table); Lexis rule **G6b**.
3. **Reviewer gap closed (this commit): the five words are lexed, the item is
   refused by name.**
   - `crates/gabbro-syntax/src/kw.rs`: `Syscall Abi Sysnumber Errors Kernel`,
     all `ctx` (clause words, like every other clause word in the table), with
     the «SS-1» reason block the ratchet demands (why no existing form carries
     it: an `axiom`/`extern fn` throws away ABI binding, errno decoding, ghost
     OS state, kernel pairing).
   - `crates/gabbro-syntax/src/parse.rs`: `Art::Wort(Kw::Syscall)` arm in
     `item()` refuses as **`P042`** ("``syscall`` declarations are specified
     (SYNTAX.md §12.1) but not yet implemented") after skipping the whole item
     to its balancing `}`/`;` — one fault, one refusal, never silent, never a
     crash. `faengt_item_an` gains `Kw::Syscall` (recovery + corpus runner ask
     it too). Choice recorded: **context keyword, no `beispiele/07` rename** —
     `entry syscall …` names an entry (identifier at a name position, `ctx`
     stays one there); a rename would churn the corpus, the race probes, the
     docs and the dispatch-function name for zero grammar gain.
   - `crates/gabbro-syntax/tests/sprechprobe.rs`: `syscall_faellt_mit_einem_namen`
     — a `syscall …` item falls with exactly `["P042"]`, and
     `entry syscall vector …` stays clean.
   - `beispiele/gift/796-syscall-nicht-implementiert.gab`: poison probe
     (`-- erwartet: P042`, inside `module gift::…` per the corpus rule).
   - `crates/gabbro-check/src/saetze.rs`: `parser.syscall-bevor-s5` claims
     `P042` (Gemessen, probe 796); `tests/korpus.rs` `BENANNT` gains `P042`.
   - `instrumente/zaehle-wortschatz.py`: marks `224→229` / `208→212` with the
     ratchet's own ledger lines («SS-1», shared reason block — the second mark
     counts blocks, not lines, hence +4 not +0). Third mark unmoved (all five
     `ctx`).
   - `instrumente/pruefe-saetze.py`: mark `53→55`, decomposed in the comment:
     +1 mine (`P042` with its sentence, same commit), +1 inherited (`V012`,
     lane p26, merged 2026-09-11 with probes but no sentence — the base I
     branched from already carried it while booking 53).
   - Documents re-booked to the measured state: `SYNTAX.md` State table
     (**163** rules, 226/226, `P042`-wording, G6b rewritten: words ARE lexed,
     the ITEM is refused); `README.md` (304 diagnostics, 163 rules, 226/226,
     38 guardians, 550 poison files); `DONE.md` (550); `TODO.md`
     (163/226 prose, 89 Kennzahlen, strikethrough bookkeeping); the closed
     P1-finding row (`today 163 / 226`).

## Before / after numbers (every guardian that reads SYNTAX.md)

| guardian | S1 commit (`87b4b7d`) | now |
|---|---|---|
| `./cargo-pruef` | exit 101, 2 failing (`wortschatz.rs` on `{abi,errors,kernel,number,syscall}`) | **exit 0, 0 failing** (all suites green, incl. new `syscall_faellt_mit_einem_namen`) |
| `pruefe-wortschatz.py dokumente/SYNTAX.md` | 226/226 + 4 Sonderformen, both probes green | same, green |
| `pruefe-syntax.sh` (with `PATH=$HOME/.cargo/bin:$PATH`) | ALL PASS to `Warnungen`, then ABBRUCH rc=127 (no cargo on PATH) | **ALL PASS incl. `keine` warnings**: EBNF 163, 0 open; 226/226; gifts/prose/speech green |
| `pruefe-grammatiktafel.py` (same PATH) | not runnable (no cargo) | speech 17/17 green; **ROT 2/226 UNGEDECKT: `abi`, `errors`** (`niemand nennt es`, ctx). Rest green: `syscall`/`number`/`kernel` covered (`gesenkt`/`vom Pruefer`). Empfindlichkeit 1 (Marke 1), an-2: 18 (no ratchet) |
| `pruefe-englisch.py` | probes green + new line; ratchets red 7904/7881, 1085/1069, 24/23, 1/0 | probes green + new line; feeders **25/23** (+1 mine: the `P042` sentence name `parser.syscall-bevor-s5` trips the coarse feeder scan — renamed off the German stem, re-measured 24/23; comment/instrument/sink figures unchanged) |
| `pruefe-kennungen.py` | ALL PASS, 303 | **ALL PASS, 304** (`P042`, one file — the rule) |
| `pruefe-saetze.py` | 53-booked; run said 55 (incl. inherited `V012`) | **green at booked 55**: 118 sentences claim 249 codes, 55/304 without, 0 invented |
| `zaehle-wortschatz.py` | 224-booked vs 224 measured (kw.rs untouched); 363 positions / 230 terminals / 163 rules | **229/212/17 marks hold, speech ok**; 363/230/163 |
| `pruefe-zahlen.py` (same PATH) | 18 BEFUNDe (all pre-existing drift) | **same 18** — byte-identical finding set with and without my diff (stashed re-run): my tree adds zero findings; no SYNTAX.md number I changed is register-guarded (State table is prose, not `KENNZAHL`) |
| `pruefe-todo.py` (same PATH) | 13 BEFUNDe (7 stale 161/221 prose + README + DONE + 91-vs-89) | **ALL PASS** after re-booking README (304/163/226/38/550), DONE (550), TODO (163/226, 89) |
| `./emission-pruef` | — | **ABBRUCH at Differenztest beispiel19 step 8** (`verändertes Erzeugnis liefert dasselbe`) — byte-identical on the stashed base: pre-existing, not mine; full log `.tmp/emission.log` |

## What remains open / handoff to S5+S7

- S5-S7 implement the `syscalldecl` body behind `P042`: ABI table check, register
  map, total error map, assumption-or-kernel pairing, emitter stub + `CForm`
  ruling, corpus writer over `write`. The day a `syscall` item parses, probe 796
  goes red BY DESIGN (it pins today's refusal) and is re-cut as the first
  positive probe; the `P042` sentence is replaced by the rules that hold the
  clauses — not extended.
- `pruefe-grammatiktafel.py` stays ROT on `abi`/`errors` (2/226) until S7 writes
  corpus carriers that lower them or checker error texts that name them; the
  run above is the baseline (speech green, rest green).
- `pruefe-englisch.py` stays red on its four booked ratchets (comments,
  instruments, feeders incl. my +1 decomposition above, sink) — all pre-existing
  except the feeder delta, which is named here.
- `pruefe-zahlen.py` carries 18 pre-existing drift findings (RUECKLAUFWERTE,
  PASSREGISTER pre-V012 figures, README/TODO prose) — none mine, all reproduced
  on the stashed base.

## What I believe was wrong (task + review, measured)

- S1-as-scoped (documents + guardians, no `kw.rs`) forces a red
  `./cargo-pruef`: the `wortschatz.rs` lexer↔table tests count `kw.rs`, which
  S1 must not touch. The review's "smallest form" (lex the words, refuse the
  item as `P042`) resolves it without pre-empting S5: five `ctx` entries, one
  match arm, one code, one sentence, one probe — and `beispiele/07` untouched
  by construction.
- The review's clause-word list (`abi arch number regs clobbers errors`)
  misses the header (`syscall`) and the pairing alternative (`kernel`): both
  are terminals needing rows and lexer entries. Shipped as documented in S1.
- "Every guardian above as green as on master" is not attainable by
  re-booking alone where the base already drifted: `pruefe-zahlen.py` (18),
  `pruefe-englisch.py` ratchets (4), `pruefe-grammatiktafel.py` (2 UNGEDECKT),
  `./emission-pruef` (beispiel19 step 8) are red on the stashed base too.
  This lane re-books what it owns (README/DONE/TODO/PASSREGISTER/saetze-mark/
  wortschatz-marks) and names the rest with stash evidence instead of
  touching numbers it did not move.
