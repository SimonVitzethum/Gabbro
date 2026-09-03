# The counter-probe the baseline gate did not have

**Written 2026-09-04.** `messung/RESCUED-BASELINE-DEPTH.md` and the rescued change in
`instrumente/fuzze-erzeuger.py` (`kaputte_basis`, now `kaputte_basislinien`) ran on this tree
for the first time and reported **zero broken baselines**. A "0" on a first run is not yet a
measurement — *without a counter-direction, "nothing is there" and "nothing is being
measured" are indistinguishable*, the same reason every other net in this file already
carries one (`sprechprobe(cc, arb)`, five groups before this one). This is that
counter-direction, done twice: once for real, against the actual pipeline on
`ki-pc-fisch-101`, and once permanently, wired into `sprechprobe()` itself.

## Part 1 — a real baseline, broken and restored, both recorded literally

The gate's own comment names the property precisely: *"a baseline whose C the compiler
rejects is either a bad fixture or a live emitter defect, and no test inside this file can
tell those apart."* Finding a genuinely new C-compile failure through the real 66-form
sweep would mean finding a fifth live emitter defect after `D1`–`D6` closed the tree's
known population (`RESCUED-BASELINE-DEPTH.md`'s own "0" is corroborated, not staged) — that
is a defect hunt, not a counter-probe of the REPORTING mechanism, and it was not attempted.

Instead, the demonstration targets the exact question at stake — *does the print statement
under `== BASELINE ==` notice and report when `kaputte_basislinien` is non-empty* — by
forcing one **already computed, already real** baseline result to look broken, right where
`main()` reads it, with a five-line, clearly labelled, temporary edit:

```python
    # >>> TEMPORARY COUNTER-PROBE (messung/BASELINE-GEGENPROBE.md) -- reverted before commit.
    for _cp_f, _cp_e in basis.items():
        if _cp_e.get("debug") in ("LOWER", "LOWER-EMPTY"):
            _cp_e["uebersetzt"] = False
            print(f"   [COUNTER-PROBE] forcing `{_cp_f}`'s baseline to LOOK broken")
            break
    # <<< END TEMPORARY COUNTER-PROBE
```

Every stage in front of this line still ran for real: `gabbro pruefe`, `gabbro emit`, and
`cc` all executed exactly as they do on every other run. Only the one flag the reporting
logic reads is flipped, on one already-genuine result, after the real compile already
succeeded — so this exercises the gate's own noticing-and-printing machinery and nothing
else.

Command, run three times from `gabbro-sammel` on `ki-pc-fisch-101` (110 GB RAM, 16 cores;
`cargo build` and `cargo build --release` both green beforehand):

```
python3 instrumente/fuzze-erzeuger.py --debug target/debug/gabbro --release target/release/gabbro --cc cc
```

**Before** (committed source, unmodified):

```
== BASELINE -- every form's known-good value, through checker AND emitter ==
   66 of 66 baselines accepted; 61 of them lower to C, 5 are refused by name at the baseline itself
   61 of those 61 COMPILE under the gate -- 0 do not, and each one is a FORM-LEVEL defect:
      none. Every lowered baseline compiles, so every shape-2 finding below
      is the swept VALUE's own doing.
```

**Broken** (the five-line edit above applied, `rsync`'d, run again — no other change):

```
== BASELINE -- every form's known-good value, through checker AND emitter ==
   [COUNTER-PROBE] forcing `acc-percpu`'s baseline to LOOK broken
   66 of 66 baselines accepted; 61 of them lower to C, 5 are refused by name at the baseline itself
   60 of those 61 COMPILE under the gate -- 1 do not, and each one is a FORM-LEVEL defect:
      acc-percpu             baseline `8`  ?
```

The gate fired: the count moved (`61 of 61` → `60 of 61`), the form was named
(`acc-percpu`), and the finding line printed under its own heading rather than merging
into "0" silently.

**Restored.** `git checkout -- instrumente/fuzze-erzeuger.py`, then verified byte-for-byte
before the file went back to the server:

```
$ md5sum instrumente/fuzze-erzeuger.py                              (local, post-checkout)
847c75f16ab0a9ab8b3dd9d0c8c54aa9  instrumente/fuzze-erzeuger.py
$ ssh ki-pc-fisch-101 md5sum gabbro-sammel/instrumente/fuzze-erzeuger.py   (after rsync)
847c75f16ab0a9ab8b3dd9d0c8c54aa9  gabbro-sammel/instrumente/fuzze-erzeuger.py
```

Run a third time, same command, same binaries:

```
== BASELINE -- every form's known-good value, through checker AND emitter ==
   66 of 66 baselines accepted; 61 of them lower to C, 5 are refused by name at the baseline itself
   61 of those 61 COMPILE under the gate -- 0 do not, and each one is a FORM-LEVEL defect:
      none. Every lowered baseline compiles, so every shape-2 finding below
      is the swept VALUE's own doing.
```

Quiet again. The only diff against the first ("before") run's full output is two temp
directory names (`/tmp/tmpXXXXXX`, fresh per invocation) — the full sweep result
(`3443 of 3584 accepted cases kept the emitter's promise`) is identical in both directions,
because the underlying object never changed; only the report's sensitivity was being
tested.

## Part 2 — wired permanently, over an invented population

A real break-and-restore answers "did it fire *this once*"; it does not stay behind to
answer the question again next run, and CLAUDE.md's own lesson about a measurement that
depends on someone noticing applies here as much as anywhere: *"a guardian nobody drives is
indistinguishable from one that does not exist."* So the same question is now asked on
every run, cheaply, the way every other net in this file already is (`sprechprobe(cc, arb)`
runs before every sweep and needs no build of its own beyond the two binaries the sweep
already requires).

Two permanent changes, committed:

1. **`kaputte_basislinien(basis)`** — the list comprehension `main()` used inline is now a
   named, three-line pure function (`instrumente/fuzze-erzeuger.py`), taking exactly the
   shape of `basis` the real sweep builds and returning exactly what it used to. `main()`
   calls it in place of the inline comprehension; behaviour is unchanged (see the fourth run
   below).

2. **Three new directions in `sprechprobe()`**, over hand-built, invented `basis` dicts —
   the same style `kollisionen`'s four directions already use two screens up in the same
   function, never a real `.gab` file or a real `cc` call:

   * a baseline that **compiles** (`debug: LOWER` / `LOWER-EMPTY`, `uebersetzt: True`) must
     **not** be reported;
   * a baseline that **lowers and does not compile** (`debug: LOWER`, `uebersetzt: False`)
     **must** be reported — the one shape this whole document exists to catch;
   * a baseline the **checker refused** (`debug: REFUSE …`) must **not** land in this
     bucket — that is `kaputt`'s "THE GENERATOR IS BROKEN" abort two screens up, a different
     question, and folding the two together would hide which one needs fixing.

Confirmed against the mutated function directly (not through the real pipeline — this is
the point of an invented-fixture speech test):

```
gut     -> []
leer    -> []
kaputt  -> [('f', {'debug': 'LOWER', 'uebersetzt': False})]
refuse  -> []
```

And confirmed the new probe actually CATCHES a regression, not merely a well-worded
assertion: `kaputte_basislinien`'s guard was mutated from `and not e.get("uebersetzt")` to
`and e.get("uebersetzt")` (inverting the sense) in a throwaway copy, and the two new
`sprechprobe()` conditions were re-evaluated against it —

```
MUTATED kaputte_basislinien(kaputt) -> []
MUTATED kaputte_basislinien(gut)    -> [('f', {'debug': 'LOWER', 'uebersetzt': True})]
would sprechprobe() catch this mutation? True
```

— both directions flip, and both are directions `sprechprobe()` now checks.

**Fourth run**, permanent code in place, full sweep, `ki-pc-fisch-101`, same binaries:

```
== SPEECH TEST -- what must fall, falls ==
   20 probes, both directions: the compile gate, `-Wpedantic`, the oracle over
   decimal / hex / signed literals, the COLLISION oracle in all four of its
   directions, net 6, net 7, net 8's DEADLINE over a process that outlives it and
   one that does not, and the BASELINE GATE below over an invented population.
   All spoke.

== BASELINE -- every form's known-good value, through checker AND emitter ==
   66 of 66 baselines accepted; 61 of them lower to C, 5 are refused by name at the baseline itself
   61 of those 61 COMPILE under the gate -- 0 do not, and each one is a FORM-LEVEL defect:
      none. Every lowered baseline compiles, so every shape-2 finding below
      is the swept VALUE's own doing.

== 3443 of 3584 accepted cases kept the emitter's promise ==
   shapes 1-4: 141   nets 5-8: 63   unbooked: 0   stale bookings: 0
```

Identical to the original clean run in every count that matters — the refactor changed
nothing about what is measured, only added a way to prove the measurement can still fire.

## Verdict

**The gate does measure what it claims.** It was silent before because the tree it ran
against is, today, genuinely clean at this depth (corroborating
`RESCUED-BASELINE-DEPTH.md`'s "0", not merely repeating it) — not because the reporting
path is broken or unreachable. Both directions are now recorded literally above, and the
permanent probe means the next person does not have to take this document's word for it:
`fuzze-erzeuger.py --debug … --release … --cc cc` re-asks the question, over an invented
population, on every single run, before it touches the real 66 baselines at all.

`instrumente/pruefe-waechter.py` already tracked `fuzze-erzeuger.py` (it is one of six
guardians named in `SCHWER` — expensive, excluded from `--lauf`, but statically checked all
the same) and read it `ok` across all four/five static requirements before this change; it
still does after (`59 von 59 tragen die vier STATISCHEN`, re-run against this tree). Nothing
here changes which population `pruefe-waechter.py` counts against — `fuzze-erzeuger.py` was
already in it, and stays in it.
