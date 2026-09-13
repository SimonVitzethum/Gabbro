# MUSE-REPORT-160 (lane 160, T3 part 4: source text to the G program in Lean)

## What was built

New file `grammatik/Grammatik/Parser/Uebersetze.lean` (2114 lines),
registered in `grammatik/Grammatik.lean` as `Grammatik.Parser.Uebersetze`.
It closes the loop from the Lean surface parser (lanes 135/154/157) to
the declaration/program shape the Rust exporter `gabbro lean-g`
(lane 144, `crates/gabbro-check/src/lean_g.rs`) produces, in two stages:

1. **Surface to U** (`elabU : List SItemTief -> Except String UProg`):
   a generic elaborator over exactly the fragment `lean_g.rs` exports --
   tables (count + integer range per slot field), locks with `Held`,
   `impl` fns with pointer/index/range params, comparison contracts over
   slot reads/`old`/`result`/literals (plus `true`/`false`/`and`/`or`/`not`),
   straight-line bodies of slot writes, direct calls, trailing return.
   Every other form is an explicit `.error` (plain `String`, no new
   diagnostic codes). Two passes like the exporter: heads (params, result
   range, held set, effects with the one-directional `locks`-without-`Held`
   refusal and writes dedup), then contracts and bodies (guard check,
   `rw`-to-`r` fresh pointer, caller/callee held-set equality, fall-off rule).
2. **U to G** (`lowerProg : UProg -> Except String
   (Programm G104_referenz.gD x List G104_referenz.GFn)`): assembles G terms
   over the exporter's declaration universe, with the signature data
   cross-checked against `gD` entry by entry.

## Theorems (all closed pins, no premises, no `_zeuge` needed)

- `u104lex`: comment-free 104 source lexes to the hand-written token
  literal `tt104` (`by decide`, 3200000 heartbeats).
- `u104parse`: `beqTopTief (parseTopTief tt104) (.ok items104) = true`
  (`by decide`, default budget).
- `u104elab`: `beqElabU (elabU items104) (.ok uExp104) = true` (`by decide`;
  new `beqU*` Bool equalities in lane style, since `Except` has no
  `DecidableEq` here).
- `u104lower`: `lowerProg uExp104 = .ok (gP, gFs)` (`rfl`; proof
  irrelevance covers the proof terms).
- `u104data`: 16-conjunct agreement in the shape of `export104_data`
  (elaborated count/field range/lock rank/params/held/writes against
  `r4D`, `by refine ⟨rfl, ...⟩`).
- `u104fragment` / `u104fuss`: `programmImFragmentG` / `fussOrtGB` on the
  Lean-parsed program (`by decide`).
- `#print axioms` for all seven: only `[propext, Classical.choice,
  Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

Last `./lean-bau` result line: `Build completed successfully (148 jobs).`

## What remains open / findings

- The single whole-pipeline `decide` is split per the task (lane-135
  finding); chaining the four stage pins is prose, as in `Export104.lean`.
- Lowering is keyed to the `gD` universe (`Konto`/`M`/`stand`/
  `einzahlen`/`lies`); everything else errors. Restrictions beyond `elabU`
  (one call per body, no post-call calls, empty `lies` bodies, the
  `lies`-only call, bare same-range return): see the file's CUTS block,
  which also lists every deliberate divergence from `lean_g.rs`
  (bare-word types refused, slot extras refused, `use`/nested modules
  refused; the refused rows, one-directional locks check, writes dedup,
  fresh pointer, fall-off, ignored `reads`/`costs`/`section`/`payload`
  are mirrored exactly).
- Two findings for other lanes: (a) with `open G104_referenz`, short names
  (`gD.params g_einzahlen`, `Expr gD ...`) mis-elaborate while fully
  qualified names work (minimal repro was confirmed and removed; the file
  qualifies everything); (b) kernel `decide` on a `beq` goal goes silently
  stuck (not false) when any helper in the chain is broken -- fix the
  elaboration errors first.
- Nothing in the task looks wrong; the heartbeat split it sanctions was
  sufficient (only the lex pin needed raised heartbeats).

Commits on `muse/160`: `a7a5e6b8` (elaborator + lowering),
`2f2a31ad` (tokens + lex pin), `cbcda459` (parse/elab/lower/data/checks).
No codes, gifts or examples used. No files outside the new Lean file plus
the one import line were touched.
