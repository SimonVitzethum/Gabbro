# Address-space rules outside `m1.rs`: survey, boundaries, and the gap left open

**Read-only investigation first, 2026-09-11, worktree `lane-138` on base `6f26e76`.**
Scope: `umgebung.rs` placement/space-equality and `bitlage.rs` bit-ranges (`M108`/`B24`
territory); a user-region declaration rule and/or validated-copy rule (`M151`, assigned
free) where the area supports it. Outcome: **probes-only plus this report** -- no new rule,
`M151` left unclaimed. The reasons are one per area below, each with the command that
reproduces it.

Verification for everything dynamic in this file is the one targeted run (no other builds):

```
CARGO_BUILD_JOBS=4 cargo test -p gabbro-check --test beispiele
```

---

## §1 Space equality is already repaired at base -- pinned, not rebuilt

The open post `Ein benannter Adressraum ist sich selbst ungleich` (`TODO.md`, from
`messung/K3-BEFUND.md` §4.2) no longer reproduces at `6f26e76`:

* `crates/gabbro-syntax/src/ast.rs` carries a hand-written `PartialEq for Raum` that narrows
  `Benannt` to the identifier TEXT (spans never match across declaration sites);
* `beispiele/68-named-space-matches-itself.gab` is the pass side (`user` to `user`, clean);
* `beispiele/gift/681-two-different-named-spaces-still-clash.gab` is the poison side
  (`user` to `kernel`, `R008`).

A repair that made every named space equal to every other would pass the first and let the
second through; the pair stands against exactly that failure mode. What the pair does NOT
pin is the boundary of the name comparison itself, so probe `761` does:

* `beispiele/gift/761-named-space-case-differs.gab` (`-- erwartet: R008`): `ptr<User, r>`
  handed to a `ptr<user, r>` parameter. Case differs by one bit; anything but an exact text
  comparison lets it through. The harness asserts the code is among the errors
  (contains, not exclusive) -- nothing here claims exclusivity.

## §2 Rights over named spaces -- probe 763

`R013` (`m3.rs`) compares access ATOMS, never spellings and never spaces, so the §1 repair
cannot disturb it -- but nothing measured that over a named space (`607` is `normal`). Probe
`763` is the same unsound direction (`r` at `rw`) over `user`:

* `beispiele/gift/763-user-rights-widen-at-a-call.gab` (`-- erwartet: R013`).

`R008` stays silent on it by construction (same word both sides), so the probe also pins
that the two rules do not overlap on named spaces. The narrowing counter-direction cannot
live in `gift/` (a file there must fall); it is covered for builtin spaces by
`tests/gestalt.rs` and needs no named twin, since the space word never enters the atom
comparison.

## §3 Bit-range boundaries -- probe 762 and unit pins in `bitlage.rs`

`B24` in the checker is `N007`/`N008` via `bitlage::lies`/`lage_pruefen`, surfaced by
`namen.rs`; the corpus pins the classes (`105`/`107`/`572`/`573` for `N007`, `106` for
`N008`). Probe `762` pins the overlap edge:

* `beispiele/gift/762-bit-ranges-touch-by-one-bit.gab` (`-- erwartet: N008`): `@[7:4]`
  against `@[4:0]` shares exactly bit 4. `106` overlaps by two bits; the clean touch beside
  it (`[7:4]`/`[3:0]`, one word, tiled) must stay silent.

The function-level edges live where the corpus cannot reach them -- a corpus file falls
identically for every wrong edge inside a class -- so `bitlage.rs::grenzen` pins four:
single bit at the top bit vs one past it, the reversed range, the one-bit touch, and the
exact tiling. Deliberately NOT built: a refusal over `Unklar` (bit layout on a
non-integer carrier). The emitter gives `bool @N` meaning (word width from the group's
integer fields; refusal only where no field says it), the clean corpus writes that form
(`format Pte` in `beispiele/03`/`07`), and the silence is documented `W10`. A rule there
would need the checker's grouping to relearn the emitter's -- sprawl against a working
form.

## §4 Placement (`backed`, `M108` territory): collected here, enforced elsewhere

`umgebung.rs` collects `kapazitaeten` and `hinterlegungen`; the refusal below `backed`
(`M108`) lives in `m1.rs`, which a sibling lane owns this turn. Two structural facts close
the door on a declaration-side twin in owned files:

1. `umgebung.rs` emits no `Absage` anywhere -- it is pure collection (`grep -n Absage`
   finds only a comment). A rule needs a refusal channel.
2. Passes are wired explicitly in `lib.rs::pruefe`, which is central and out of scope.
   `bitlage.rs` rules surface only because `namen.rs` already forwards every `Befund`
   from `lies`/`lage_pruefen`; no caller forwards anything comparable from `umgebung.rs`.

A helper without a caller is dead code, and a second implementation of an existing refusal
is the divergence this tree refuses twice (`W7`). So: no placement rule from this lane.

## §5 The validated-copy rule (`M151`): gap pinned, number left free

Static survey, reproducible with one search:

```
grep -rn '\.raum' crates/gabbro-check/src/*.rs
```

Readers of a pointer's space at CHECK time: `m3.rs` (`R008` call-space match, `R001`
`raum == Dma`) and nothing else. `geteilt.rs` reads `Dma`/`Mmio` for effects, `manifest.rs`
and `namen.rs` read the `entrust` space word, the rest is the emitter. **No pass reads
`z.raum` at a dereference/use site**: a direct field read through `ptr<user, r>` is
space-blind wherever the checker looks. That is the validated-copy hole -- use without
`access_ok`/mask/copy -- and the refusal belongs at the use site, which is `m1.rs`
territory (sibling-owned this turn).

`M151` is therefore NOT claimed by this lane: no `Absage` carries it, no probe expects
it. Suggested shape for the owning lane, from `messung/k3-fragmente/K03-copy-from-user-iter.gab`:
refuse a dereference of `ptr<Benannt, …>` outside a validated-copy callee, with the
`681`/`68` pair as the template (poison launders, clean passes through the validator).
The dynamic measurement -- which codes fire on a direct user dereference today, if any --
is theirs to run; this report asserts only the static half above.

## §6 Register

| probe | expects | pins |
|---|---|---|
| `beispiele/gift/761-named-space-case-differs.gab` | `R008` | name comparison is exact text |
| `beispiele/gift/762-bit-ranges-touch-by-one-bit.gab` | `N008` | one shared bit is overlap |
| `beispiele/gift/763-user-rights-widen-at-a-call.gab` | `R013` | rights widening over `user` |
| `beispiele/68-named-space-matches-itself.gab` (existing) | clean | must-pass: repair does not over-fire |
| `bitlage.rs::grenzen` (new unit pins) | pass | top-bit, reversed, touch, tiling edges |

Touched: `bitlage.rs` (tests only), three gift probes, this file. Explicitly untouched:
`m1.rs` (sibling), `lib.rs`/`saetze.rs`/`mutiere-pruefer.py`/harness/anchors (central),
`umgebung.rs` (surveyed, nothing to add without a caller).
