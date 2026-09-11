# CPU-device seam: publish/await pairing (mechanised)

Status: MECHANISATION NOTE, base `2dc02ad`, branch `p24-ziel`, 2026-09-11.
It mechanises the guard-handoff half of the open item at
`dokumente/SYNTAX.md:1637-1640` (16.2 (3): "the seam CPU-device has no
mechanised model"). The doorbell-register mapping and the full-run
interleaving stay cut (C3/C4/C6 in `grammatik/Grammatik/Geraet.lean`);
this note changes no checker, no axiom layer, and no number booked elsewhere.

## 1. Model argument

The transfer discipline is a publish/await pairing across the seam, added as
section 12 of `grammatik/Grammatik/Geraet.lean` (lines 758-833, appended only;
lines 1-757 untouched):

- `SeamPublish` — the CPU publish half: the driver hands the DMA-visible
  buffer over (`gibt W` at `k`). It names the guard and the handoff index.
- `SeamAwait` — the CPU await half: the driver takes the buffer back
  (`nimmt W` at `m`). It names the guard and the take-back index.
- `SeamPair` — the pairing: one publish, one device write (`dma` at `j`),
  one await, with `publish < write < await`. The pair is the discipline
  around the named content assumption, not a replacement for it.
- `SeamPair.wache` — the bridge: every pair is a guarded window
  (`GeraetWache`), so section 4 applies unchanged.

What is proved (order half):

- `seam_pair_ordered` — the pair preserves order across the seam: publish
  precedes await through the device write (`devVor`, `devNach`, transitivity).
- `seam_pair_race_free` — the pair preserves race-freedom: a CPU access
  ordered against the pair endpoints is ordered against the device write.
  The endpoint half (`haussen`) stays the driver obligation, as in
  `geraet_ohne_wettlauf`.

What stays assumed (content half):

- `dma_inhalt` stays the NAMED hardware assumption, untouched at line 204;
  no new axiom was added. `seam_handoff` is the umbrella: ordering proved,
  content taken as hypothesis. Events carry no values, so no run fact
  derives content — the split is structural.

## 2. Axiom split (expected `#print axioms` output)

- `seam_pair_ordered`, `seam_pair_race_free`:
  `[propext, Classical.choice, Quot.sound]` — no `dma_inhalt`.
- `seam_handoff`:
  `[propext, Classical.choice, Quot.sound, dma_inhalt]` — ordering proved,
  content assumed, never mixed silently.

## 3. Recompute commands

Server down, so local with the `free -g` gate; scoped check only (no full
test, no `abnahme`, no `lake build`). Import oleans are borrowed from the
main-checkout build at the same base (`2dc02ad`); the checked source is this
worktree. `Wettlauf.lean` is byte-identical at that base, so the borrow
measures this file, not a mixture.

```bash
free -g   # gate: proceed only with headroom; measured 11 GB available
LEAN_PATH=/home/simon/Dokumente/Gabbro/grammatik/.lake/build/lib/lean:/home/simon/Dokumente/Gabbro/programmlogik/.lake/build/lib/lean \
  lean grammatik/Grammatik/Geraet.lean
grep -nE "sorry" grammatik/Grammatik/Geraet.lean  # expect: no match
```

Measured 2026-09-11: exit 0, zero warnings, zero `sorry`, axiom split as
in section 2.

## 4. What did not change (limits)

- Append-only: 76 insertions, 0 deletions; the file-header index still
  lists sections 1-11 only (updating it would edit shared lines).
- The `SYNTAX.md:1637-1640` checkbox is left untouched — closing it is
  review business, not part of this scope.
- Chain (`KetteGeordnetM`) and doorbell analogues of the pair are future
  work; the pair covers one window, which is exactly the unit the chain
  links compose.
