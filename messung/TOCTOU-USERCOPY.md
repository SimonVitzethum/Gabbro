# User-copy TOCTOU: the unguarded handoff is refused (V012)

Worktree `p26`, base `2dc02ad`, 2026-09-11. Scope: `crates/gabbro-check/src/paarung.rs`
(user-copy functions only), `beispiele/gift/784-768`, this note. The V-clock/pairing
remainder (`messung/V-UHREN.md`) belongs to another lane and is untouched here.

## 1. What stood open

`dokumente/SYNTAX.md:431-436` ("What stays future work"): the region check stands
beside the run -- the world is one flat mapping with no side partition, and no
statement transition discharges it. Booked in §16.2 item 12 ("user-copy hazard --
future work"). The Adressraum shape (`grammatik/Grammatik/Adressraum.lean`) proves
validated-copy safety (`gepruefteKopie_ohneToctou`) under the named single-copy
premise (`EinSnapshot`) and names the gap without it
(`laufSequenz_toctou_ohneSnapshot`): check over one triple paired with a copy over
another is the TOCTOU sequence, not a validated copy.

## 2. The discharge argument

The run cannot check ranges (no `exec` branch discharges `validiert`, cut C6), so
the discharge moves to the checker: **no accepted program performs an unguarded
user-copy handoff.** Where check and use stand in one body they are atomic under
the `EinSnapshot` premise; where they stand in two bodies the using body must
re-validate. Anything else is refused as `V012` at the handoff call. From accepted
programs the missing run-side range check is therefore unreachable *for this
shape* -- the checker refuses every program that would need it.

What this does NOT discharge (booked remainder, §5): the world partition itself
(C7 -- no `Seite` in `World`, no `exec` branch), length companions beside the
pointer, indirect handoffs, and foreign bodies.

## 3. The rule (V012)

For each `impl fn` with a block body, in one in-order walk with statement-granular
positions (each statement one position, sub-blocks in place):

- CHECK on `P` (`ptr<user, …>` parameter): a comparison (`BinOp::ist_vergleich`)
  mentioning `P`, or a `narrow` on `P`. Comparisons on user pointers are validation
  attempts by construction. Contracts (`requires`/`ensures`) never count.
- HANDOFF of `P`: a call with the bare name `P` as argument (the `R008`
  under-approximation: fields, locals, return values carry no declared space).
- GUARDED: the callee checks the receiving `user`-space parameter before its first
  use of it, or never touches it at all. A check after the first use, or on a
  different parameter, guards nothing.

`V012` fires at the call iff the caller checks `P` strictly before the handoff
AND the callee is a named Gabbro body that uses the received pointer uncovered.
Silent by statement: check and use in one body (atomic); re-validating callee;
handoff with no check beside it (`beispiele/68` -- pure forward, no TOCTOU shape);
`extern` callee (booked foreign-body gap -- the boundary kill already forces a
re-read after the call); indirect or unresolvable callee (W10 -- undecidable,
neither refused nor confirmed); receiving parameter not a `user` pointer
(`R008`/`M140` own that shape -- no double verdicts).

## 4. Evidence

| probe | shape | finding set (full `pruefe`) |
|---|---|---|
| `beispiele/gift/784-checked-user-pointer-handed-to-copy.gab` | comparison check, then handoff to copying callee | exactly one `V012`, 0 hints |
| `beispiele/gift/785-narrowed-user-pointer-handed-to-copy.gab` | `narrow` check, then handoff | exactly one `V012`, 0 hints |
| `beispiele/gift/786-checked-user-pointer-forwarded-twice.gab` | two-hop forward, use at the far end | exactly one `V012` at the FIRST hop; second hop silent (no check beside it) |

Unit twins in `paarung.rs` (`v012_tests`, pass-only): unguarded handoff falls once;
narrow variant falls once; same-body check+use silent; re-validating callee silent;
extern handoff silent; forward-without-check silent; check-on-other-parameter falls
once. Existing `v011_tests` unchanged and green.

Silence pins on existing corpus (full `pruefe`, zero `V012` each): `beispiele/68`
(the extern-forward pass side), `beispiele/gift/681`, `/761`, `/763` (their `R008`/
`R013` verdicts stand alone -- no second verdict beside them).

## 5. Recompute (server down -- local, scoped)

```bash
free -g   # gate: stay well under memory pressure before any rustc run
cargo test -p gabbro-check --no-fail-fast --lib paarung
cargo test -p gabbro-check --no-fail-fast --test beispiele
cargo run -q -p gabbro-cli -- pruefe beispiele/gift/784-checked-user-pointer-handed-to-copy.gab
cargo run -q -p gabbro-cli -- pruefe beispiele/gift/785-narrowed-user-pointer-handed-to-copy.gab
cargo run -q -p gabbro-cli -- pruefe beispiele/gift/786-checked-user-pointer-forwarded-twice.gab
```

No full `cargo test`, no `abnahme.py` from this lane (compute order: scoped only).

## 6. Remainder and risks

1. **Length companions untracked.** A check on a `u32` length travelling beside the
   pointer does not count as a check on the pointer. The rule sees the address half
   of the Adressraum triple, not the length half. A program that validates only the
   length and hands over the pointer stays silent.
2. **New code `V012` has no `Satz` yet.** `instrumente/pruefe-saetze.py` (full-run
   watcher, out of this lane's scope) will list it as unclaimed; the claim text is
   §3 above, ready to move into `saetze.rs` at integration.
3. **`V012` is the next free V number.** If the pairing lane claims the same number,
   integration renumbers one side -- the gift `-- erwartet:` lines move with it.
4. **Overwrite does not silence.** Writing the pointer between check and handoff
   still falls (the check covered the old value). Fail-closed by statement.
5. **Check-in-check positions.** A call nested inside the checked expression
   (`if f(q) != 0`) hands off at the check's own position; equal positions never
   precede, so it stays silent by construction.
