# A Gabbro program, and a specification written by hand in Lean 4

**Two `.gab` files are one program.** `lager.gab` declares the table; `betrieb.gab` writes
into it and reaches the declaration through `use`. Neither file alone is a program, and a
specification is about a program.

```bash
gabbro lean beispiel/lager.gab beispiel/betrieb.gab > GabbroProgram.lean
lean -o GabbroProgram.olean GabbroProgram.lean
lean Spec.lean          # the specification, hand-written -- goes through
lean SpecGift.lean      # three poisoned ones -- all three fall
```

## What the export carries, and what it does not

It carries the **program**: every body as a `Stmt` datum, every precondition it can say, and
the shape of every declared place. **It carries no specification.** What is to hold is said
in `Spec.lean`, in Lean, by a person -- and that file is not generated and never read by the
emitter.

*That is the whole reason a hand-written specification is worth having:* `Spec.lean` states
`nur_dieses_fach`, a frame property with a **quantifier**, and a `spec fn` in Gabbro cannot
express one. It is proved.

## The three poisons, and why each falls

| | |
|---|---|
| `gift1` | the specification demands `menge = 5`; the body writes `0` |
| `gift2` | it demands that EVERY compartment stays untouched -- including the one being cleared |
| `gift3` | it names `gewicht`, a field no table declares |

**The third is the one to watch.** It falls, but with *"unsolved goals"* -- which reads like a
fault in the program rather than in the specification. `instrumente/pruefe-lean-programm.sh`
holds every place a specification names against `GabbroProgram.places` and says the true
thing instead.

> **And what no dictionary catches:** a typo from one REAL field to another. `menge` where
> `sperrig` was meant proves a true statement about the wrong place. *The check bounds the
> hazard, it does not remove it.*
