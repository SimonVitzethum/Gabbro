# Emitter name resolution is scope-blind (measured, open)

Status: measured 2026-09-11 at central integration; reverted refusal,
kept evidence. The `zeigerArithmetik` refusal (lane-142) fired on plain
`u32` arithmetic and was withdrawn the same day -- not because pointer
arithmetic is fine, but because the tree it fired on was misresolved.

## The instance

`messung/netz/udp-echo.gab:113` (`falter` checksum fold):

```
let a : u32 = (s & 65535) + (s >> 16);
let b : u32 = (a & 65535) + (a >> 16);
```

The refusal named pointer arithmetic. A temporary instrument (applied,
measured, reverted byte-identical) printed the resolved operand types
at the firing site:

```
tacA=Some("ArpTabelle *") tacB=Some("ArpTabelle *")
```

`a` is a `u32` local of `falte`; `ArpTabelle *` is the parameter type
of a DIFFERENT function (`arp_suchen`/`arp_lernen`, same parameter
name). An isolated copy of `falte` emits clean -- the misresolution
needs the whole unit.

## The mechanism

`wert_ctyp` answers a bare name from the unit-global `parametertyp`
map before consulting `lokaltyp` (`emit.rs`, `ExprArt::Ort` arm). Both
maps are global across functions by construction; `lokale_lets` skips
any `let` whose name stands in global `parametertyp`, so the local
never even reaches `lokaltyp`. The code's own comment at the map
(`emit.rs`, `baumsicht`) says it outright: a map from NAME to declared
type that knows nothing about scope.

The checker forbids the within-function collision (`N001`: `let`
shadowing a parameter is refused), so the order is unobservable inside
one body -- every instance of this bug is cross-function pollution of
exactly this shape: foreign parameter type wins over own local.

Precedent in the same file (2026-08-31): loop variables against
parameters, fixed by remembering names plus `ist_laufvariable`, after
an attempt (blind `parametertyp.remove`) was cut for answering only
half the question. Per-function scoping of the resolution (via
`eigene_sicht`, which already builds per-function views but does not
scope these maps) is the fix direction; the `baumsicht`/`index into T`
case constrains it (that site needs the map and must keep working).

## What waits on the fix

- The withdrawn `zeigerArithmetik` refusal (both the `Binaer` arm and
  the `+=`/`-=` arm) plus its two probes: return together with a
  same-day green run of the full suite, `zaehle-netz.py`, and the
  corpus emission sweep.
- `tafel_nicht_geschlossen` rests on `.zeigerArithmetik .offen` again
  (flipped back with this note as the reason).
- Acceptance for the fix (falsifiable, in this order): `udp-echo.gab`
  emits; the full suite stays green; a same-name cross-function probe
  (local `u32` vs foreign `ptr`) resolves to the local; the 08-31
  loop-variable cases keep their behavior.

Counts: no new watcher numbers from this note alone (prose + code
spans, no bold table cells).
