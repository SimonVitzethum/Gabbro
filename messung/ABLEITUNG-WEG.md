# H021: the refused drop -- a call/pair edge the derivation cannot resolve

Worktree lane-131, base 6f26e76. The derivation (`ableitung.rs`) answers an
unresolvable edge with a lower bound (`unvollstaendig`) where `E009` stands beside
it as a hint -- and a hint is not a refusal. `H021` is the refusal: a body calling
a target with nothing to derive from, or an indirect call whose (place, contract)
pair stands outside every checked hull, falls here -- once per (caller, target),
at the caller's name.

## 1. The rule

A dropped edge falls with `H021` in exactly three shapes:

| reason | the edge | today |
|---|---|---|
| `Unbekannt` | body calls a target unknown to the graph (no `fn` item, no graph node) | fixpoint drops it with *"`ziel` is unknown to the graph"*; `E009` hint at most |
| `Stumm` | body calls a target with no body anywhere AND no declared `effects` | fixpoint drops it with *"`ziel` declares no `effects`"*, `E009` hint at most |
| `OhneVertrag` | indirect call through a place whose type carries no `effects` contract | hull is a lower bound that names itself (`E009` hint) |

```gabbro
extern fn stumm() costs <= 2 ops;   // no `effects` -> `E001` at the declaration...
impl fn rufer() effects { pure } costs <= 8 ops
{
    stumm();                        // ...and NOTHING at the call. `H021` falls here.
}
```

Deliberately NOT in the rule: an argument that is not a place (`unklar` in
`ersetze`). That shape is `E009`'s legitimate third state -- a bridge that cannot be
built is not a target that does not exist, and refusing it as `H021` would re-run
lane 103 (`H019`, withdrawn at integration: it fired on member/predicate shapes that
were never frame-bound). *A refusal that cannot tell those apart is a wider net, not
a stronger rule.* Pinned by `unklare_bruecke_bleibt_still`, with a non-vacuity
assertion (`unvollstaendig.is_some()`) so the silence cannot mean the bridge was
never needed.

## 2. Read-only investigation first (changed nowhere to learn this)

| site | what it supplies | verdict |
|---|---|---|
| `ableitung.rs` `eigen` | per-function own effects with `Weg::Rumpf` origins | the fixpoint's floor; untouched in behavior |
| `ableitung.rs` `ohne_rumpf` | no-body functions AND graph-only nodes | the edge; shared, not duplicated (see §6) |
| `ableitung.rs` `vertraglich` | graph-only subset (device transitions/handles, generated ops, `u8`..`i64` words) | compiler-supplied -- never `H021`, even when effect-less it is a different question |
| `ableitung.rs` `stumm` | no body AND no declared `effects` | the hole: the edge is dropped, only a lower bound recorded |
| `aufrufgraph.rs` `gehe`/`huelle` + `E009` in `wirkungen.rs` | unknown/imprecise edges become a HINWEIS, never a `Fehler` | why the hole is silent at `Fehler` level |
| `wirkungen.rs` `E001` | a non-`spec` function without an `effects` clause is refused AT THE DECLARATION | so a `stumm` `extern` always co-fires `E001` -- `H021` adds the caller's refusal, it does not replace the declaration's |
| `paarung.rs` `V001`/`V002` | the (atomic, payload) pair is judged GLOBALLY (`alle_erwartet`/`alle_publiziert`) | the pair half of `H021`: a pathless-but-paired shape is silent today (family `730`/`731`/`732`); the transitive refusal belongs to `paarung.rs` and is PINNED here, not built |

## 3. Assignment (verified free, 2026-09-11)

`H021`: zero hits across `crates/`, `beispiele/`, `instrumente/`, `messung/`,
`TODO.md`, `DONE.md`, `README.md`. (`H019` is free too -- withdrawn at integration;
it stays free: this lane does not re-spend a withdrawn number on a narrower rule.)

Probes `740`/`741`/`742`: no `74x` gift file exists; max gift number is `739`
(500 gift files before this lane). All three numbers were free.

## 4. Probes and verdicts (measured)

| probe | kind | verdict (measured) |
|---|---|---|
| `beispiele/gift/740-stumm-edge-pinned.gab` (`-- erwartet: E001`) | must fall: caller edge to a `stumm` target; twin `ruft_rand` (edge WITH a line, silent); declaration refusal carries the file | suite green (`contains E001`); `ableitung::pass` over the ACTUAL file yields exactly `["H021"]` (temporary file-loading test, reverted) |
| `beispiele/gift/741-resolvable-twin-silent.gab` (`-- erwartet: V001`) | must pass: body-to-body, `Rand`, conversion word, with-contract indirect (`beispiele/49` idiom), edge-paired publish/await; carrier orphan `w` carries the file | suite green (`contains V001`); `ableitung::pass` over the ACTUAL file yields `[]` -- the twin is silent under the rule too |
| `beispiele/gift/742-publish-side-pathless-pair.gab` (`-- erwartet: V001`) | boundary: publish-side pathless pair (mirror of `730`, which pins the await side); edge-paired counter-probe + two-hop boundary in-file; carrier orphan `w` carries the file | suite green (`contains V001`); derivation-side `pass` yields `[]` -- the pair half belongs to `paarung.rs` (pinned, not built) |

Wiring-compatibility, on record: every probe stays green AFTER wiring (the gift
harness asserts `contains`, and wiring only ADDS `H021` to `740`). The probes pin
today's silence without going red the day the wire lands.

## 5. Sprawl measurement (temporary wiring, reverted before commit)

The task's conditional requires knowing, not guessing. With a one-line temporary
wiring (`ableitung::pass(baum, absagen);` behind `wirkungen::pass` in `pruefe`,
REVERTED -- final diff touches neither `lib.rs` nor any other central file):

* `cargo test -p gabbro-check --test beispiele`: **25/25 green WITH the refusal
  wired** -- clean corpus draws ZERO `H021` (`jedes_beispiel_geht_sauber_durch`
  green), all gift green (incl. the three new probes and the `H020` purity pin
  `738`, which still falls with exactly `["H020"]`).
* The fallback trigger (clean corpus red) did NOT fire. The committed tree is still
  probes-plus-ready-rule, because the wire itself is central assembly (frozen for
  this lane) -- not because the rule sprawls. The rule is measured corpus-clean.

## 6. What stands in `ableitung.rs` (ONLY source file touched)

* `H021` const (assignment + free-verified + unwired-state on record).
* `Kantenbuch` + `erhebe_kantenbuch`: the no-body sets (`ohne_rumpf`,
  `vertraglich`, `stumm`) plus name spans plus graph-only declared sources, read
  ONCE and shared by the fixpoint and the refusal (no second reader -- `W7`).
  `leite_ab` was re-homed onto it with byte-identical behavior: `tests/ableitung.rs`
  8/8 green, beispiele suite 25/25 green.
* `Kantengrund` / `FehlendeKante` / `fehlende_kanten`: the refusal as a pure
  function -- same edges the fixpoint walks (`rufe`, `ruft`-without-args,
  `indirect`), keeping only unresolvable ends; one entry per (caller, target,
  reason), callers ordered.
* `pass`: the refusal over one unit -- one `H021` `Fehler` per dropped edge at the
  caller's name span (the granularity `E009` stands at), two notes per refusal.
* 7 unit tests in `#[cfg(test)] mod tests` (no new `tests/` files): must-fall
  (`Stumm` once at the caller + bookkeeping agreement; `Unbekannt`; `OhneVertrag`)
  + twins (`Rand`, body-to-body) + boundaries (conversion word, `unklar` bridge
  with non-vacuity assertion). 7/7 green.

## 7. What the wire needs (follow-up, central assembly)

1. One line in `lib.rs::pruefe`: `ableitung::pass(baum, absagen);` (measured
   position: behind `wirkungen::pass` -- see §5).
2. A `saetze.rs` sentence for `H021` (this lane adds none -- frozen).
3. `BENANNT`/watcher updates (this lane adds none -- frozen).
4. Single-file rule (`pruefe-kennungen.py`): `H021` fires from `ableitung.rs` ONLY.
   If the pair half is later built in `paarung.rs` as a transitive refusal, it
   needs its own code -- sharing `H021` across two passes would make every probe
   naming it ambiguous. `H021` here covers the derivation half (call edges and
   the (place, contract) pair).
