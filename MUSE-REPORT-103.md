# MUSE-REPORT-103 (lane 103, D6: watches for globals)

## What was done

New file `grammatik/Grammatik/WacheGlobal.lean` (import wired at the end
of `grammatik/Grammatik.lean`), full `./lean-bau` green.

**Main theorem** `wache_global_aus_schuld` — the mirror of
`wache_aus_schuld` (`InterferenzAllgemein.lean:1481`) for globals, same
conclusion shape at `.inr x`:

```
theorem wache_global_aus_schuld (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (x₀ : D.Glob) (L : D.Lock)
    (hGuardG : Sum.inl L ∈ D.gbraucht x₀)
    (g : Faden) (hg : g ∈ J.faeden)
    (hW : TraegerSchreibt (J.code g) (.inr x₀) = true)
    (hTouch : ∀ f ∈ J.faeden, TraegerSchreibt (J.code f) (.inr x₀) = true →
      WaechterGehalten (J.code f) (.inr x₀)) :
    L ∈ D.haelt (J.code g)
```

Proof: `hTouch g hg hW` gives `WaechterGehalten` at `.inr x₀`; applied
to `hGuardG` it puts `Res.held L` in `Signatur.anfang`; membership in
the `haelt.map`-half (the `konsumiert`-half is mark-shaped, impossible)
is exactly `L ∈ D.haelt`. Every premise is applied positionally; no
premise is a bare `Prop`; no syntax quantification (only `Faden`,
bounded by `∈ J.faeden`), so the statement is non-vacuous by
construction. Axioms: `[propext, Classical.choice, Quot.sound]`.

**Witness** `wache_global_aus_schuld_zeuge`: instantiates all premises
jointly on a local declaration `gD` (one table, one guarded global, one
lock, one function writing both — `refD` has `Glob := Empty`, so the
task's allowed local extension was used). Chain `gJ`: one thread, two
worlds, one step moving the global `0 → 5` (recorded as a `gzugriff`
event), empty `Lauf` for the `Gesittet`/`BeschraenkteVerschraenkung`
fields (same shape as `kette_aus_lauf_start`). The existential also
carries `(∃ f t, gD.schreibt f t = true)` and
`J.welten[0]? ≠ J.welten[1]?`, both proved. Axioms: standard triple.
Supporting names: `gD`, `gCode`, `gGuardInst`, `gWriteInst`,
`gTabWrite`, `gAnfang`, `gSlots`, `gGlobs0`, `gGlobs1`, `gW0`, `gW1`,
`gNb`, `gEintritt`, `gGes`, `gBeschr`, `gSchritt`, `gEintritt0`, `gJ`.

## Verification

- `./lean-probe grammatik/Grammatik/WacheGlobal.lean`: 0 errors.
- `./lean-bau` last line: `Build completed successfully (54 jobs).`
- `pruefe-kennungen.py`: ALL PASS. `pruefe-englisch.py` fails on
  pre-existing Rust ratchets (booked 7881 vs 7905 checker comment
  lines); my files are not mentioned anywhere in its output.

## What remains open

- The per-body checker proof of `hTouch` (every body writing `x`
  establishes `WaechterGehalten` at `.inr x`) is a premise, mirroring
  how `wache_aus_schuld` carries coverage as a premise. Per-step it
  rides on `fremdDisziplin_gilt` from `TraegerInv.disziplin`.
- No dynamic (world-held) analogue for oracle global writes is stated;
  it would route via `hgd` + `HeldGenau` (cf. `FremdSperre.lean`).

## Findings / task feedback

1. **The exact `J.hSchuld`-based mirror is impossible, by
   construction.** `SchuldnerHaelt`, `schuldet`, and U003
   (`D.invarianten_gehalten`) quantify over TABLE carriers only
   (`D.traeger : Inv → List Tab`); there is no global
   invariant-carrier list, hence no global coverage premise to mirror
   `hCov`. The mirror routes via the touch rule instead. The
   SATZKARTE §8 D6 sketch (`J.hSchuld` + `(global coverage)`) names
   things that do not exist for globals and should be reworded toward
   the touch discipline.
2. **No falsifying constructor.** Constructor survey: every syntactic
   global writer carries `gdarf` — `assignGlob`/`publish` via `hL`,
   `Block.awaits` via `hL` (it writes the received value through
   `schreibGlob`), `axiomCall` via `hgd`. All but the oracle write
   record a `gzugriff` event. The oracle write records none, but the
   mirror is static (declared holds) and needs no event, so nothing
   falsifies the theorem as stated.
