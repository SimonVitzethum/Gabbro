# MUSE-REPORT-75: H007 at the foreign-call boundary (checker repair)

Lane 75. A call to a body-less (`extern`) function whose declared
`reads`/`writes` effects touch a lock-protected place now owes that lock
HELD at the call site -- same diagnostic family H007, naming the call and
the effect clause. The reported race (`p-fremd.gab`: `extern fn fremd_setzt`
with `writes k.slots` called without `KAPPEN`, 0 errors) is now refused.

## What was done

**Fix -- `crates/gabbro-check/src/geteilt.rs` (only Rust file touched):**

- The H007 section now iterates module-aware (`fuer_jedes_item_im_modul`),
  builds an `Umgebung`, and snapshots every body-less callee
  (`FnRumpf::Keiner`: `extern` plus forward declarations) into an owned
  `FremdEffekte` (declared `reads`/`writes` places with clause text,
  self-taken `locks`, callee module + parameter types).
- New `Rufhalte` context (static per-function data: resolver, graph,
  foreign table, locks, RCU domains, module, function name), threaded through
  the existing `schutz` walk beside the `da` held set.
- New `ruf_h007` check at every call site the direct walk already inspects
  (`StmtArt::Ruf`, `Let`/`Return`/assignment values, call args, `Wenn`
  conditions, `let-else` calls) plus a `rufe_in` expression walker for calls
  nested in index/argument/`aligned`/count positions. For each declared
  callee place that a lock protects and that is neither held at the site
  (block, `effects { locks }` line, `requires Held`) nor taken by the callee
  itself (exclusive `locks` covers reads+writes, `locks shared` covers
  reads), it emits e.g.:
  `` `fremd_setzt` writes `k.slots` through its declared `writes k.slots`
  effect, and `ohne_sperre` does not hold `KAPPEN` which protects it ``
- New `effekt_trifft` place matcher with two disjuncts: the existing token
  match (`protects { K }` vs `writes K.slots`), and a type-directed one for
  whole-region effects against field-named `protects` (`writes k.slots` vs
  `protects { rechte }`): the effect root resolves through the callee's
  parameter types (else globals) to a table whose slot fields contain the
  entry, and the path must descend through `slots`. A bare pointer handle
  (`writes k`) stays silent. Unwrapping crosses pointers and named types
  (`tabellenname`).
- Gabbro callees are deliberately EXCLUDED (measured, not assumed): a Gabbro
  fn writing naked is already refused at its own body by this same rule, and
  one taking the lock itself forces the caller to declare it (`E008`, which
  H007 counts as held and `H011` redeems through the callee hull).
  Scratch probes in `.tmp/lane75/` (git-ignored): `probe-gabbro-selbst.gab`
  (self-taking callee, caller declares the line: 0 errors),
  `probe-gabbro-nackt.gab` (naked callee: H007 only at its own body, never
  doubled at the caller), `probe-fremd-sauber.gab` (call inside `locks`,
  self-taking extern with and without a held lock: 0 errors),
  `probe-fremd-ausnahmen.gab` (naked foreign read: H007 fires),
  `probe-bare-handle.gab` (bare `writes k`: silent).
- The H020 doc's booked remainder ("held set AT a call site ... next lanes")
  now points at `ruf_h007` for body-less callees.

**Probes (convention `-- erwartet: H007` followed):**

- `beispiele/gift/796-fremdruf-ohne-sperre.gab` (poison): the reported race
  in corpus form plus the honest `ordentlich` sibling (keeps H008 quiet).
  Result: exactly 1 error (H007), 0 hints.
- `beispiele/72-fremdruf-unter-sperre.gab` (positive): the guarded call and
  the self-taking extern. Result: 0 errors, 0 hints.
- Deleted the two reviewer copies `p-direkt.gab`, `p-fremd.gab` (were
  untracked in the repo root).

## Last `./cargo-pruef` result line

`== exit 0; failing tests: 0` (full `cargo build` + `cargo test
--no-fail-fast`; the beispiele/gift corpus tests run inside it, so every
existing example stays green and the two new probes behave as specified).

## What remains open (deliberately out of scope)

- `asm`-body callees: sealed hull, same trust shape as `extern`, not covered.
- Indirect calls through places (contract rules' territory) and calls in
  expressions the direct H007 walk never inspects (match scrutinee,
  exchange/narrow/await places): same blind spots as the direct rule.
- Strength at the call: caller holding a lock *shared* while the callee
  *writes* stays silent (no H001-through-call); a write under a shared
  self-taking (`locks shared` + `writes`) is still owed by the caller.
- Pure-RCU places have no lock, so foreign writes to them stay silent here
  (H010 does not see calls either).
- Chains are refused frame by frame: caller -> Gabbro mid -> extern is
  refused at mid's unguarded call site, which is where the guard belongs.

## Guardian / emission state (measured against a stashed baseline)

- `pruefe-kennungen.py`: ALL PASS (303 codes, H still 23 -- no new code).
- `pruefe-englisch.py`: my delta is zero (one German-in-comment line I added,
  via the identifier `Keiner`, was reworded; verified 0 German words in all
  added comment lines). The three broken ratchets (7905 vs 7881 comment
  lines, 1085 vs 1069 instruments, 1 vs 0 German sink at `main.rs:713`) are
  identical at baseline -- merged-wave drift, not mine.
- `pruefe-saetze.py`: exit 0. `pruefe-deckung.py`: UNCOVERED = 0.
- `pruefe-gruende.py`: 7 suspect / 138 carrying / 107 unclear -- exactly
  baseline. (Intermediate state moved H017 carrying->unclear: my new
  `"H007",` anchor truncated H017's 4000-char window, exposing borrowed text
  -- the guardian's own documented W16 class. Fixed by relocating the helper
  block after `orte_in`; counts prove no other code moved.)
- `pruefe-zahlen.py`: 21 of 22 BEFUND lines identical to baseline; the single
  delta is `Zeilenfortsetzungen` 3970 -> 3973 (my 3 `\`-continued diagnostic
  strings, in this file's own style) on a number booked at 3733 -- stale by
  237 before me. No green->red transition attributable to this lane.
- `./emission-pruef`: red at Stufe 9 BEFORE and AFTER (baseline log kept out
  of the commit at `.tmp/lane75/emission-baseline.log`). Pre-existing causes:
  `messung/proben/absenkung/*` C failures (`main` return type), booked-count
  drift (messung 73->133, gift 2->9, stray `Claude outputs/` + `halde.gab`
  roots), `NUR CLANG` on beispiele/66. My commit's emission delta, measured
  directly: both new files emit C that passes `cc` AND `clang`
  (`-std=c11 -Wall -Wextra -Werror -c`); after tracking, beispiele/ 71->72
  and gift-emitting 9->10 become good-case count marks. No compile failure
  is added. (One transient: a single `gabbro emit` of 796 exited 1 among
  6+ exit-0 runs of the same file/binary; not reproducible, reported as
  observed.)
- `mutiere-pruefer.py --anker` Sprechprobe and `pruefe-gestalt.py` (Lean
  counters): red identically at baseline -- pre-existing.

## On the task text

Nothing in the task turned out to be wrong. Two readings needed decisions:
"the caller must NOT hold it" is implemented as exemption (no H007), not as
a refusal -- holding plus a self-taking callee stays silent under the rank
rules, which skip the same lock (verified with a probe). "Check whether the
existing interprocedural rule already covers [Gabbro callees]" is answered:
yes (own-body H007 + E008/H011), hence the body-less-only scope, with probes
as evidence. Rule 14 (guardian patterns first): no new code and no German
text were added, and the one window-sensitive guardian (`pruefe-gruende.py`)
was re-measured after placement; no guardian pattern needed to move.
