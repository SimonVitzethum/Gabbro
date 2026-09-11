# H019 -- WITHDRAWN on merge (a contract read outside the write frame)

**WITHDRAWN 2026-09-11 at central integration:** the rule as built fired
on established tested behavior (`paesse.rs`: literal-index M141 probes,
member-domain silence, predicate-name probes expect exact code sets or
silence -- H019 overlapped all three). Reads in contracts were never
frame-bound; the design need (stability, not refusal) stands proved in
`LesenStabil.lean`. Rule, probes (734-736), satz entry and BENANNT entry
reverted; this note stays as the record with the three counter-cases.

**Lane 103, 2026-09-11. Rule built in `crates/gabbro-check/src/m1.rs`
(`vertrag_rahmen_pruefen`, next to `ensures_pruefen`); probes
`beispiele/gift/734`-`/736`.**

## The premise

`grammatik/Grammatik/Extraktion.lean` discharges `HaengtAb` at the signature frame
under the premise `hT`/`hG`:

- `haengtAb_requires`: every `requires` place lies inside the function's writes,
- `haengtAb_ensures`: every `ensures` place lies inside the function's writes,
- `haengtAb_invariante`: every invariant place lies inside a covering frame.

The checker never asked for the `requires`/`ensures` half of that premise: before
this lane a `requires` naming a carrier the frame does not write passed with **zero
errors** (measured at `gift/734` before the build -- the same shape `H018` measured
at `gift/724`: a proof premise with no checker half).

## What the rule says

A `requires`/`ensures` read naming a **known world carrier** (table, global --
the `hT`/`hG` shape) outside the function's **declared write frame** falls as
`H019`, once per carrier per clause, at the clause span.

- The frame is the declared `effects` writes (`Schreibt`/`Veroeffentlicht`
  bases) -- the same register `M111` reads. `E008` already reconciles the body
  hull against that list, so no second hull read stands here.
- What counts as a read is `sammle_namen_pred` minus parameters, `result`,
  `Self`, `&f` and lock witnesses (none of which is a carrier), kept only
  where `ist_weltname` answers yes -- and constants and type names are out
  even then (`beispiele/07`: `BOOT_RAHMEN_UNTEN` is a `const u64` the world
  map answers for, and no state). An unknown name stays silent -- another
  rule owns the spelling mistake.
- A `reads` line covers nothing: the frame is the WRITE frame. `gift/736` pins
  that boundary (read declared, never written -- still falls), and its twin
  pins the carrier edge (a clause over a parameter only -- no footprint at
  all -- stays silent).

## What the rule does NOT do (open, not guessed)

1. **Invariants.** A `table`/`walk`/`group` item carries no `effects` list, so
   there is no declared frame to hold the footprint against -- and a `group`
   invariant by design names SEVERAL carriers (U007), so "stay within your own
   carrier" is not even the right sentence there. Loop `invariant` clauses
   inside bodies are unread for the same reason (no frame threaded through).
   The Lean half (`haengtAb_invariante`, at any covering frame) therefore still
   has no checker half. That is the pinned hole of this lane.
2. **Calls inside contracts.** A carrier reached through a `spec fn` call in
   the contract is not unfolded (same direction as `H018`: intraprocedural
   direct names only).
3. **Registers.** Device registers are no `Tab`/`Glob`, so the transition
   idiom `requires GSTS.RTPS == 1` over `effects { writes GCMD }`
   (`beispiele/09`, `/02`) stays silent by construction -- the corpus check
   below is the evidence, not the comment.

## Measurements

- `gift/734` (`requires`, hT): exactly one `H019` at the out-of-frame read, twin silent.
- `gift/735` (`ensures`, hT): exactly one `H019`; `M111` satisfied via `result`, silent.
- `gift/736` (`requires`, hG boundary): exactly one `H019` under a `reads` line;
  the parameter-only twin silent.
- Clean corpus: `cargo test -p gabbro-check --test beispiele` green -- no
  `beispiele/*.gab` names an out-of-frame contract carrier (the `beispiele/09`
  readers either write what they read or read params/registers).

## Registers touched

Checker (`m1.rs`) plus three probes plus this note. `saetze.rs`,
central assembly (`mutiere-pruefer.py`, BENANNT-class registers) and all counts
are central's -- deliberately untouched (lane scope).
