# MUSE-REPORT-88 — overflow operators, surface half (PLAN-BITS §4)

Lane 88, Rust lane. Wrapping `+%`, `-%`, `*%`, `<<%` and saturating `+|`
are lexed, parsed, checked, and lowered. The Lean model half already existed
(`Ueberlauf.lean`: `addW`/`subW`/`mulW`/`shlW`, `addS`); this lane adds no
Lean code and no Lean theorems.

## What was built

1. **Lexer/parser** (`gabbro-syntax/src/lex.rs`, `ast.rs`, `parse.rs`).
   New tokens `Z::PlusProzent` (`+%`), `Z::MinusProzent` (`-%`),
   `Z::SternProzent` (`*%`), `Z::SchiebLinksProzent` (`<<%`),
   `Z::PlusStrich` (`+|`), longest-match-first. New `BinOp` variants
   `PlusWrap`, `MinusWrap`, `MalWrap`, `SchiebLinksWrap`, `PlusSat`, each at
   the precedence of its base operator (`addexpr` for the `+` family,
   `mulexpr` for `*%`, `bitexpr` for `<<%`).
2. **Checker** (`gabbro-check/src/m1.rs`, `typen.rs`).
   `typen::exact_wrap_n` answers `N` for ranges exactly `0 .. 2^N-1`
   (`gemeinsame_form` is now `pub` for the caller). `m1::wrapping_or_saturating`
   (+ `wrapping_shift`, `saturating`) answers the operand range and never
   takes `M104`: wrapping is defined mod 2^N, clamping fits by construction.
   New refusals `M153` (wrapping needs an exact unsigned range, names `+|`
   as the alternative; signed refused with the 5b sentence) and `M154`
   (saturating needs one shared range). A literal operand adopts the other's
   range when its value lies in it; two literals wrap in the common width.
   New sentence `m1.umlauf_saettigung` in `saetze.rs` covers both codes
   (`pruefe-saetze.py` back at its mark: 120 sentences, 55 without).
3. **Lowering** (`gabbro-check/src/emit.rs`). Wrapping computes on the
   unsigned storage type, masked to `N` bits below full width
   (`(uint16_t)(((uint32_t)(a) + (uint32_t)(b)) & 8191)`); full width needs
   no mask. Saturating calls one of two file-scope helpers
   (`_gabbro_sat_u`/`_gabbro_sat_i`, bounds as arguments) with an explicit
   `if` compare — no `?:` (census NEVER list), no builtins, no `__int128`
   (the 64-bit bodies never form the overflowing sum). Ranges are re-derived
   from declarations at the site (`storage`, `intty_interval`,
   `constexpr_value`, `wrap_side`/`wrap_form`/`wrap_shift_form`,
   `saturation_facts`); where nothing derives, the site is `C001`, never
   guessed. Helpers are emitted only when the syntactic pre-scan
   (`needs_saturation`) finds `+|`.
4. **Exhaustive-match arms**: `fremdverengung::zeichen`, `opsruf::zeichen`
   (+ `ALLE` list), `m1::op_zeichen`, `emit::{rechnet, ist_bitop, op_text}`,
   `umgebung` const-eval (new ops answer `None` — the modulus lives in
   types, not values), `lean.rs` (`Err`, no `Expr` constructor exists),
   `refinement.rs` (`NoTerm`, theory imports `Main`).
5. **Guardians first**: 5 probes in `miss-grammatikdeckung.py` (all score
   `REFUSES` with `M153`/`M154` — carried verdicts); `SYNTAX.md` EBNF +
   operator-attribute table. `leite-grammatik.py --formen` derives the same
   five form IDs mechanically, so the registers join.
6. **Tests**: `crates/gabbro-check/tests/overflow.rs`, 7 tests — checker
   acceptance (u32 shapes, u13 sugar, literal adoption, signed saturation),
   poison probes (`M153` on `u32 in 0..5` and signed, `M154` on two ranges,
   `M104` on a wide shift amount), emitted mask/call shapes, and a
   compile-and-run value test (15 cases: wrap, 13-bit mask, clamp high/low).

## Verification results

- `./cargo-pruef`: `== exit 0; failing tests: 0` (incl. the 7 new tests).
- `./lean-bau`: `Build completed successfully (50 jobs)` (no Lean changes).
- `zaehle-c-formen.py`: `MARKE_TABELLE 66 = 66`, `MARKE_UNERLAUBT 31 = 31`.
- `pruefe-wortschatz.py`: 226/226 unchanged (operators are no words).
  `pruefe-saetze.py`: 55 without, at mark. `pruefe-kennungen.py`: ALL PASS.
- `./emission-pruef`: red at stage 9, signature `222 von 222 emittierenden
  Dateien uebersetzen` — every emitting file compiles (gcc and clang).
  The remaining FUNDs are file-count drift on corpus files this lane never
  touched (beispiele 73 vs 70, messung 132 vs 73, gift 8 vs 2, new roots,
  umgekehrte Proben 2 vs 4). Byte-identity argument: no `.gab` file in the
  repo contains an adjacent new spelling (grep-proved), every new code path
  keys on the new AST nodes, and no existing refusal was removed — so no
  existing verdict or byte could move. Pre-existing, not new.
- `pruefe-englisch.py` (exit 1) and `pruefe-todo.py` (12 findings) are red
  on pre-existing drift: English counts are byte-identical before/after this
  diff (7905/1085/1 — my added lines contain zero flagged German words, my
  identifiers are English), TODO findings are README/DONE/TODO number drift
  in files I never touched (EBNF rule patterns: worktree == HEAD).

## CUTS (not proved / open)

- Saturating/wrapping sites the emitter cannot read (two-literal `+|`,
  literal-left `<<%`, unresolvable exotic shapes) are `C001`, not lowered.
- New ops are not const-folded (`umgebung` answers `None`) and not carried
  by the Lean/Isabelle certificate channels (refused by name).
- No compound-assignment forms (`+%=`, `+|=`, …) — not asked for.
- Rule 13: this lane adds no Lean theorems, so no `_zeuge` companions exist;
  the joint positive+poison+value coverage is the Rust test suite above.

## Where I believe the task text needs sharpening

- "`+|` on any integer range; result range = the operand range": with two
  *different* ranges there is no "the" range. Implemented: one shared range
  required (`M154`), literals adopting. Clamping into anything else would
  invent the interval.
- "wrapping only when both operands have an exact range": for `<<%` the
  amount cannot be exact — it is bounded `0 .. N-1`, matching Lean `shlW`'s
  `Zahl 0 w`. Implemented and documented in `SYNTAX.md`.
- "vocabulary/grammar table count the new tokens": operators are not
  vocabulary words (`pruefe-wortschatz` counts `[A-Za-z_]` terminals only —
  correctly unchanged). The covering guardians are `leite-grammatik.py`
  (mechanical) and `miss-grammatikdeckung.py` (hand probes, added).
