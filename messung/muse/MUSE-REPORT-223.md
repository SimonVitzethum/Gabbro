# MUSE-REPORT-223 — Costs on extern/syscall, trusted with named assumption (K003)

Lane 223, TODO §-1 wave A. Scope: trusted `costs <= N ops` on `extern`/`syscall`
declarations. Reserves: N396–400 / gifts 1057–1061. Used: gifts 1057–1058, no N codes.

## Result in one line

The clause + trust mechanism for the `extern` edge already exists in
`kosten.rs` (the `syscall` edge was closed by the lane-114 rule with `N322`
and probes 986/987). I measured the full matrix empirically, found no gap
that justifies a new refusal, and therefore used no N code: missing `costs`
where the caller promises them stays `K003`, `forever` without total stays
`K003`. What this lane adds is the missing pin: two gift probes (1057/1058),
one both-directions Rust test, and the trust booking in the `kosten.summation`
sentence. `./cargo-pruef` ends with zero failing tests.

## What was already there (verified, not assumed)

- `extern fn … costs <= N ops` parses and is widespread in the corpus
  (e.g. `beispiele/63-druckt.gab`, 35 corpus files declare an `extern fn`).
- `kosten.rs` collects EVERY `ItemArt::Funktion` with a constant `costs` into
  `deklariert` (`kostenkarten`, `pass`, `durchgangskosten`, `bericht`,
  `abgeleitete_kosten`) regardless of body kind — so a bodiless `extern fn`
  prices its callers exactly like a bodied `fn`. The number is never held
  against a body (there is none): pure trust, like `effects`.
- `ruf()` prices the call at exactly the declared number (no dispatch step —
  the `syscall` edge prices `1 + fa`; the asymmetry is booked in
  `syscall.kosten`'s vorbehalt and pinned by 987 vs my 1058).
- A caller promising costs over a costless `extern` meets `K003`
  ("the call to `stumm` declares no `costs`"). A caller promising nothing
  stays silent (omission keeps its old meaning, lane 191).

## Measured matrix (all with the built `gabbro` binary, exit codes checked)

| case | verdict |
|---|---|
| caller `costs <= 7` over `extern` with `costs <= 5` (`let`+call+load = 7) | 0 errors |
| same caller at `costs <= 6` | exactly one `K001`, "promises <= 6 ops, the body costs 7" |
| caller `costs <= 7` over `extern` WITHOUT `costs` | exactly one `K003` |
| caller with NO `costs` over costless `extern` | silent |
| `retry bounded 60` over costed `extern` (`durchgangskosten` divides) | 0 errors, 1 hint (`S007` on the watchdog name) |
| caller `costs <= 100` over a `forever` function without `costs` | exactly one `K003` |
| cross-module mirror (`use` + qualified call over costed `extern`) | 0 errors |
| `extern` with SYMBOLIC `costs <= 4 + 1 * n` + promising caller | `K003` ("declares no `costs`") |
| clean shape emits C accepted by `cc -Werror -fsyntax-only` | yes (counterfactual for 1057's `allein`) |

The symbolic row: a symbolic trusted bound is silently treated as missing
(`deklariert` is constant-only) and the `K003` TEXT then says "declares no
`costs`" where a clause stands but reads as no single number. Outcome-honest
(a refusal, never a silent pass), text-imprecise. I deliberately did NOT build
a symbolic-trust mechanism or an `N396`: constant bounds are the shape lanes
229/234 need ("a trusted `costs` upper bound on a foreign edge" — the
`HashMap<String, i128>` maps and `kostenkarten` already carry `extern`
entries, so the shape they build on is present), and symbolic foreign bounds
belong to lane 229's traverse-totals mechanism, explicitly not mine. No corpus
`extern` carries symbolic `costs` (measured by grep), so nothing in the tree
depends on the sharper reading.

## Files added/changed (no checker logic touched)

- `beispiele/gift/1057-extern-ohne-kosten.gab` (new, `-- erwartet: K003 allein`):
  poison — promising caller over costless `extern`. `allein` half 2 holds the
  same way as 986's (checker-refused tree emits nothing; `cc` accepts the
  output), and the counterfactual (drop `K003` → clean check + `cc`-valid C)
  was measured on the costed twin.
- `beispiele/gift/1058-extern-kosten-zaehlen.gab` (new, `-- erwartet: K001`):
  the positive-direction pin — exactly one `K001` whose arithmetic proves the
  edge counts the declared 5 with no dispatch step (at `fa`-style `1 + 5` the
  body would cost 8, not 7). Mirror of 987.
- `crates/gabbro-check/tests/paesse.rs`: new test
  `trusted_extern_costs_count_at_callers` — both directions for all three
  shapes (K003 over missing / silent omission / K001 at 6 / silent at 7 /
  silent bounded retry over the edge). The clean directions are what gift
  files cannot pin.
- `crates/gabbro-check/src/saetze.rs`: `kosten.summation` vorbehalt gains the
  trust clause (extern counts exactly the declared number, never held against
  a body; missing clause meets `K003`) and `gemessen_an` books 1057/1058 plus
  the paesse test. `kennungen` untouched — no new code, no new sentence needed.
- `kosten.rs`, `lean_g.rs`, `emit.rs`, `MARKE_EMIT*`, Lean files, OS tables:
  untouched. No Linux constant enters the tree (no new decls of any kind).

Reserves left unused, on purpose: N396–400 (no genuinely new refusal
measured), gifts 1059–1061, no example numbers (mine reserves none, and a new
`beispiele/` file would move `MARKE_EMIT`, which I must not touch).

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (final run after the brace
  fix below; baseline before changes was also green).
- `python3 instrumente/pruefe-saetze.py`: exit 0 —
  `416 Kennungen, 170 Saetze, 55 ohne Satz, 0 erfunden`.
- Emission marks: both new gift files do NOT emit (`gabbro emit` exit 1,
  empty output), so `MARKE_EMIT_G` stays 18 and no other mark can move (no
  `beispiele/` root files, no emitter/checker change). `./emission-pruef`
  (the multi-hour full run) was not re-run; the argument above is why it
  cannot drift. The merger re-measures marks anyway.
- Corpus verdict diff: zero moves on existing files (no checker-code change;
  the green `beispiele.rs` suite over the whole corpus, old + 2 new files, is
  the measurement). Only intended additions: the two gift files.
- Mid-work failure, fixed: my first `paesse.rs` version passed a bare string
  literal with `{{` escapes (no `format!` call) to `faellt_nicht`, yielding a
  spurious `P006`. Fixed by singling the braces; full suite green after.

## The named-assumption text (for the ONE list — report only, `Spec.lean` untouched)

Proposed entry beside `(c) GutO / AxVertragO` (it constrains the same foreign
code, on the time leg `ZeitAb` rather than the frame/contract legs):

> * (c) `AxKostenO E.fa O` (proposed name) — every foreign body (`extern fn`,
>   and by the same rule every `syscall` declaration) executes in at most the
>   declared number of machine steps: exactly the trusted `costs <= N ops` at
>   an `extern` call (the declaration is trusted to include its own dispatch),
>   `1 + fa` at a `syscall` call (the `§1` dispatch step, never zero —
>   `fremd_kein_null_*`, `KostenG.lean` §13). The checker counts the number, it
>   does not re-measure the foreign body; a missing clause where a caller
>   promises costs is refused (`K003` at the call, `N322` at a `syscall`
>   declaration), never priced at zero. Symbolic bounds name no single number
>   the trip-count division could divide by and are refused the same way. Like
>   `AxVertragO`, a false number is a false NAMED assumption, visible in the
>   declaration — the time leg carries it the way the contract leg carries
>   `ensures`.

Model-side note for the Lean lanes (not built here): `KostenG.lean` §13
already parametrises the foreign table (`fa : D.Ax → Nat`) and docks it at
`ZeitAb`; its header still says a `syscall` "carries no `costs` clause by
grammar" (`beispiele/96`) — stale since the lane-114 clause (`costs <= 8 ops`
on `write` in beispiele/74, /90, /96 and gift 987). Reading `fa` off the
`extern`/`syscall` syntax on the Rust side is done (`deklariert`/`fremd`
maps); the booked remainder is the engine re-verification over the foreign
table (`hS1`/`hS2` over `kostenTiefF`), which is Lean work for another lane.

## Open / not mine

- Symbolic trusted bounds on foreign edges (text-imprecise `K003` message
  above) — lane 229 territory; corpus has zero instances.
- The engine re-verification with the foreign table (Lean, see note above).
- `./emission-pruef` full re-run left to the merger's re-measurement (marks
  provably unmoved, see above).

## Task critique (rule 9: what I believe is wrong)

- The task's framing ("Allow a trusted costs clause…") reads as if the
  mechanism is missing; for `extern` it has existed for a long time (corpus
  externs carry `costs`, `kosten.rs` prices them). The real gap was the
  missing pin (no 986/987 analogue for `extern`), which is what I built.
  Nothing in the task is wrong enough to block on, but a future task should
  say "pin the extern edge" rather than "allow the clause".
- The lane prompt's wave text (reference fixture, Lean witnesses, rule 13)
  does not apply to this Rust lane — no Lean work, no syntax universals, so
  no `_zeuge` companions exist by design. Stating this explicitly so the
  merge gate does not look for them.
