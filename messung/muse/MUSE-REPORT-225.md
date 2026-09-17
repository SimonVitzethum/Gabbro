# MUSE-REPORT-225 — never-bodies accepted: `asm` + `forever` for `-> never`

Lane 225 (TODO §-1 wave A). Scope: checker acceptance for diverging bodies of
`-> never` functions in `namen.rs` (`asm_never` region) + `saetze.rs` + probes.
`emit.rs`, Lean, `MARKE_EMIT*` untouched.

## What was measured first

Probed every honest `-> never` body shape against the unchanged checker AND
emitter before writing anything (`target/debug/gabbro pruefe/emit`):

| shape | checker today | emitter today |
|---|---|---|
| `asm`, declared arch/effects/costs, no `out { result }` | silent (S009 skips non-`Block`) | **C001** (`hat_ergebnis` arm) |
| `asm` + `out { result }` | **N321** | **C001** (N321 arm) |
| `asm` without arch/effects/costs | **A001/A002/A003** | — |
| `forever` (labelled or not), bounded `per_pass`, diverging watchdog, no total `costs` | silent (S009 `endet_immer`) | lowers (`for (;;)` + watchdog pin), `cc -Werror` clean |
| `forever` + total `costs` | **K003** | — |
| `forever` with returning watchdog | **S006** | — |
| `forever` left via `leave` | **S009** (fall-off-the-end) | — |
| body ending in call to `-> never` routine | silent | lowers, `cc` clean |

Conclusion: the checker already accepts every honest never-body (silence by
omission); the end-to-end wall is the emitter's `C001` on never-`asm` (lane
235's lowering). So this lane makes **zero checker behavior change** and pins
the acceptance with sentences + probes instead of leaving it unsaid. N321 is
byte-identical and unmoved.

## What was built

- **Sentences** (`crates/gabbro-check/src/saetze.rs`):
  - `namen.asm_never` (extended vorbehalt + gemessen_an): books the checker half
    of the open honest shape without moving the N321 line.
  - `namen.asm_never_angenommen` (new, `kennungen: &[]`): a `-> never` `asm`
    body with declared arch/effects/costs and no `out { result }` is accepted;
    the text is unchecked by construction, the divergence evidence is the
    `-> never` declaration itself (callers read all three spellings, so no
    extra word is demanded).
  - `namen.never_forever_angenommen` (new, `kennungen: &[]`): a `-> never` body
    ending in an un-leavable `forever` (leave-binding read by `verlassen`) with
    `per_pass bounded` + diverging `on_exceeded` exit and no total `costs` is
    accepted; `S006`/`K003`/`S009`-fallthrough stay refused.
- **Doc comment** (`crates/gabbro-check/src/namen.rs`, N321 arm): acceptance
  half + handoff appended. Comment only, no behavior change.
- **Poison gifts** (`beispiele/gift/`, reserved numbers 1062–1066, all refused
  so none emit and no `MARKE_EMIT*` counter moves):
  - `1062-never-forever-mit-kosten.gab` (`-- erwartet: K003`)
  - `1063-never-forever-mit-kehrendem-waechter.gab` (`-- erwartet: S006`)
  - `1064-never-forever-mit-ausgang.gab` (`-- erwartet: S009`)
  - `1065-never-asm-ohne-kosten.gab` (`-- erwartet: A003`; doubles as the
    missing A003 probe the `namen.asm_versiegelt` sentence books as unmeasured)
  - `1066-never-asm-ohne-out.gab` (`-- erwartet: C001`; checker silent —
    the handoff pin for lane 235)
- **Tests** (`crates/gabbro-check/tests/paesse.rs`,
  `never_ruempfe_werden_angenommen_225`): four positives (halting `asm`,
  labelled `forever`, unlabelled `forever`, tail call — all error-free) plus
  exact-single-code pins mirroring gifts 1062–1065.

## Handoff to lanes 235/236 (exact, per accepted shape)

- Accepted never-`asm` without `out` (gift 1066): emitter `C001`,
  `hat_ergebnis` arm (`emit.rs`: "`asm` body returns a value but names no
  `out { result : … }`", fires because `f.ergebnis` is `Some` for `-> never`).
  235 lowers this (bare `__asm__` under the existing `_Noreturn` prototype, no
  `return result`).
- Constraint: the N321 shape (gifts 984/985, emitter `C001` N321 arm) stays
  refused on BOTH channels — 235 must not lower it.
- Accepted never-`forever` / tail-call shapes: lower today, `cc -Werror`
  clean (measured on all three); no handoff.

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (paesse 145 → 146 with the
  new test; everything else unchanged).
- `python3 instrumente/pruefe-saetze.py`: exit 0 (172 sentences, incl. the 2
  new ones). `pruefe-kennungen.py`, `pruefe-englisch.py`: exit 0.
- Gifts 984/985 re-verified green and unmoved (N321 + C001 as before).
- Corpus verdict diff: **zero** — no existing file changed verdict (no checker
  behavior change); five new poison gifts, all falling as designed; no new
  emitting file, so `MARKE_EMIT*` untouched (not run: `./emission-pruef`;
  nothing I changed can move its counts — no emitter, no emitting corpus file).
- Lean untouched (`grammatik/` not entered); `./lean-bau` not run, stays green
  by construction.

## Reserves and scope notes

- Diagnostic codes N401–405: **unused, returned as spare**. Every still-refused
  shape already has a measured code (N321/K003/S006/S009/A001–A004); new
  acceptances need no codes.
- Gift numbers 1062–1066: all consumed as above. Example pool untouched.

## Where the task is wrong or ambiguous (stated plainly)

1. The wave-5 boilerplate in the lane prompt ("independent reviewer, change no
   existing file") contradicts the lane-225 scope box, which explicitly assigns
   `namen.rs` + `saetze.rs` + probes. I followed the scope box.
2. "A `forever` with no exit argument at all stays refused": every parsed
   `forever` carries `on_exceeded` by construction (the parser mandates it), so
   the literal shape is unparseable. I read "exit" as the `on_exceeded`
   watchdog (the codebase's own word: "the watchdog is the exit at which the
   bound touches reality", S006) and pinned the nearest refused shapes instead
   (S006 returning watchdog, K003 total costs, S009 left loop). If "exit
   argument" meant the loop label, note that the UNLABELLED loop is the
   strongest divergence evidence (`endet_immer`: "an unnamed `forever` can be
   left by nothing at all") — refusing it would contradict documented
   semantics, so I accepted and pinned it.
3. The result is deliberately weaker than "newly accepted" in the
   behavior-change sense: the acceptance was already silence, now it is
   sentence + probe. The genuinely new acceptance (emitted C for never-`asm`)
   belongs to lane 235; this lane is its defined starting line.
