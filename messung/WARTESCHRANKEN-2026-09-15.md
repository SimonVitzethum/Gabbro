# Waiting bounds, measured on the corpus (2026-09-15)

*PLAN-ZIELSATZ §8: "a green theorem over a number nobody can put in a data sheet is not a
result." This file books the number of `wartezeit_schranke` (Lebendigkeit.lean) for every
corpus program that declares `held` on a lock, with the growth over rank levels shown.*

## 1. The theorem and its number

`wartezeit_schranke` (grammatik/Grammatik/Lebendigkeit.lean): on a scheduled run of machine G
under the runtime assumption `LaufzeitAnnahme R F` (FIFO/ticket lock + fairness window `F`),
the hold-time premise `Haltezeit R h k`, `HardwareImAbschnitt R`, the contenders
`Anwaerter R Ts` and the goal theorem's premises, a thread standing at `locks L` at scheduler
step `n0` takes `L` before step `n0 + wartezeit L`, with

```
S(L)  = h(L)·F + k(L)·Wn(L)                     one critical section
Wn(L) = max { W(L') | rang L < rang L' }  (0 if none)
W(L)  = (c(L) - 1)·(S(L) + F) + F               c(L) = |Ts L|, the contenders
```

recursive over ranks (`wF`, fuel = number of locks). Units: **scheduler steps** = steps of
machine G of ANY thread (plus stutters). `h(L)` is in **own G steps** of the holder,
`k(L)` counts nested acquisitions per section.

**How to read it as time.** If the `c` contenders run in lockstep (every contender gets one
step in every `F = c` scheduler steps -- round robin over the contenders, or `c` cores
running in parallel with no preemption), `W/F` is the waiting time in the waiting thread's
OWN steps. For a flat lock this is `(c-1)·(h+1) + 1` -- the textbook ticket-lock bound.

## 2. Method (what was computed, and how)

* **By hand from the declarations, for every program.** `gabbro lean-g` is not used: its
  export carries no `held` (the Lean `Deklaration` has no field for it, KostenG header), so an
  `#eval` over the export would still need the numbers typed in by hand.
* Per lock: `rank` and `held` from the `lock` declaration; `k` = the number of `locks`
  statements a section of `L` executes (read from the source; every nested `locks` in the
  corpus sits directly in the outer block, outside loops); `c` from the program's threads:
  `concurrent { … }` starts reaching `locks L` (exactly `c`), `entry … stack … per cpu` roots
  reaching it (`c = P`, the core count), or none (a library module: the embedding's threads
  decide `c`).
* `h(L) = held(L)`, i.e. **one G step per operation**. This identification is NOT proved
  (§5, F-units): `K002` checks the block's operations against `held`; the G-step count of
  the block is at most operations + `zusatz` (KostenG TARGET 3), a remainder not in `held`.
* The evaluator (mirrors `wF` line by line; cross-checked: the witness gives 32 = `lW_eq`):

```python
def wartezeit(locks, c, F):            # locks: name -> (rank, h, k)
    def wF(n, L):
        if n == 0: return 0
        r, h, k = locks[L]
        wn = max([wF(n-1, M) for M in locks if locks[M][0] > r] or [0])
        return (c(L) - 1) * (h * F + k * wn + F) + F
    return {L: wF(len(locks), L) for L in locks}
```

## 3. The witness (`LebendigkeitZeuge.lean`, proved)

| program | lock | c | F | h (G steps) | k | W (proved) | actual wait on the run |
|---|---|---|---|---|---|---|---|
| fixture `mP` (MehrfadenZeuge) | `()` | 2 | 4 | 6 | 0 | **32** (`lW_eq`) | 10 (step 5 → 15) |

Here `h = 6` is counted on the run in G steps (take, call, two writes, return, close are
before the release; the release is the 6th own step while holding) -- not taken from a
`held` declaration.

## 4. The corpus: 28 programs declare `held`

### 4.1 19 programs with an acquisition point (`locks L { … }`)

W in scheduler steps with `F = c`, and in brackets `W/F` = the waiting thread's own steps.

| program | lock | rank | held | k | contenders | c = 2 | c = 4 | c = 64 |
|---|---|---|---|---|---|---|---|---|
| 04-schleifen | PLANER | 1 | 300 | 0 | library | 604 (302) | 3,616 (904) | 1,213,696 (18,964) |
| 05-nebenlaeufigkeit | KAPPEN | 0 | 400 | **1** | library | 1,208 (604) | 12,064 (3,016) | **52,678,144 (823,096)** |
| 05-nebenlaeufigkeit | SPEICHER | 1 | 200 | 0 | library | 404 (202) | 2,416 (604) | 810,496 (12,664) |
| 10-geteilte-sperre ¹ | KAPPEN | 0 | 3 / shared 4 | 0 | library | 12 (6) | 64 (16) | 20,224 (316) |
| 13-zeuge-mit-staerke ¹ | KAPPEN | 0 | 8 / shared 8 | 0 | library | 20 (10) | 112 (28) | 36,352 (568) |
| 17-gruppe-ueber-zwei-sperren | PUNKTE | 1 | 40 | **1** | library | 168 (84) | 1,984 (496) | **10,584,064 (165,376)** |
| 17-gruppe-ueber-zwei-sperren | PLAN | 2 | 40 | 0 | library | 84 (42) | 496 (124) | 165,376 (2,584) |
| 18-vorfahren | TOPO | 1 | 800 | 0 | library | 1,604 (802) | 9,616 (2,404) | 3,229,696 (50,464) |
| 31-rcu | SCHREIBER | 3 | 100 | 0 | library | 204 (102) | 1,216 (304) | 407,296 (6,364) |
| 39-auftragsdienst | WARTESCHLANGE | 0 | 20000 | 0 | library (a `forever` service) | 40,004 (20,002) | 240,016 (60,004) | 80,644,096 (1,260,064) |
| 42-zaehlwerk ² | SCHREIBER | 3 | 20000 | 0 | library | 40,004 (20,002) | 240,016 (60,004) | 80,644,096 (1,260,064) |
| 48-grund-mit-erzeuger | GRIFFE | 0 | 400 | 0 | library | 804 (402) | 4,816 (1,204) | 1,616,896 (25,264) |
| 57-faedenhalt | FAEDEN | 0 | 800 | 0 | entry `halt_ipi`, per cpu: c = P | 1,604 (802) | 9,616 (2,404) | 3,229,696 (50,464) |
| 59-eintritt-nimmt-maskierte-sperre | TAKT | 0 | 40 | 0 | entry `zeitgeber`, per cpu | 84 (42) | 496 (124) | 165,376 (2,584) |
| 59-eintritt-nimmt-maskierte-sperre | RING | 0 | 40 | 0 | entry `systemruf`, per cpu | 84 (42) | 496 (124) | 165,376 (2,584) |
| 72-fremdruf-unter-sperre | KAPPEN | 0 | 50 | 0 | library | 104 (52) | 616 (154) | 205,696 (3,214) |
| 109-lockfree-entry-roots | L | 0 | 100 | 0 | entry `entry_a`, per cpu | 204 (102) | 1,216 (304) | 407,296 (6,364) |
| 109-lockfree-entry-roots | M | 1 | 100 | 0 | entry `entry_b`, per cpu | 204 (102) | 1,216 (304) | 407,296 (6,364) |
| 110-fussgarantie | ZAEHLER | 0 | 8 | 0 | library | 20 (10) | 112 (28) | 36,352 (568) |
| 111-rufzulassung | ZAEHLER | 0 | 8 | 0 | library | 20 (10) | 112 (28) | 36,352 (568) |
| 119-sperrinvariante-bloecke | K | 0 | 50 | 0 | library | 104 (52) | 616 (154) | 205,696 (3,214) |
| 124-two-threads-private | L | 0 | 100 | 0 | `concurrent { hauptA, hauptB }`: **c = 2** | **204 (102)** | -- | -- |
| 125-read-under-lock | WACHE | 0 | 64 | 0 | `concurrent { lese_schreibe, setze_null }`: **c = 2** | **132 (66)** | -- | -- |

¹ `locks shared`: machine G has no reader mode (`Res` has only `held`); the theorem covers
exclusive acquisition only. The row treats every acquisition as exclusive with
`h = max(held, shared held)` -- a number for writers under that reading, not a theorem about
readers.

² `sammeldienst` executes `STAND_FERTIG awaits { stand }` INSIDE `locks SCHREIBER`, and
`platz_melden` runs `retry melden until abgeholt >= 1` (bounded 1024, waiting for a reader)
inside it. The awaits is a named hardware stop while it is invisible: `HardwareImAbschnitt`
is a real assumption for this program, and **the visibility wait is not in W**.

### 4.2 9 programs without an acquisition point

| program | why no waiting bound |
|---|---|
| 01-tabelle, 09-ohne-zeiger, 50-verfeinerung, 53-zwei-orte, 55-kindkette, 56-auftragsring, 104-referenz, 118-sperrinvariante-erhaltung | library functions with `requires Held(L)` only; the `locks` that takes `L` is in the (absent) caller, whose `K002` check and whose W belong to the caller's program |
| 108-disjoint-start-locks | `concurrent { read_a, read_c }` with starts holding `L`/`M` by SIGNATURE: each lock is held for the whole thread's life; no other thread takes it (`StartExklusiv`), so nobody waits. `wartezeit_schranke` does not apply: its premise "starts hold no lock" fails. |

## 5. Growth over rank levels

**The corpus is at most two levels deep** (05: KAPPEN ⊃ SPEICHER; 17: PUNKTE ⊃ PLAN). At
`c = F = 4` the outer bound is 12,064 (05) and 1,984 (17) scheduler steps; at `c = F = 64` it
is 52,678,144 and 10,584,064 -- per waiting thread 823,096 and 165,376 own steps, against
12,664 and 2,584 one level up. The factor per level is `(c-1)·k`.

A synthetic chain (every level `held = 100`, one nested acquisition per section), outer lock:

| depth | c = F = 4: W (W/F) | c = F = 64: W (W/F) |
|---|---|---|
| 1 | 1,216 (304) | 407,296 (6,364) |
| 2 | 4,864 (1,216) | 26,066,944 (407,296) |
| 3 | 15,808 (3,952) | 1,642,624,768 (25,666,012) |
| 4 | 48,640 (12,160) | **103,485,767,680 (1,616,965,120)** |

## 6. What the numbers say, plainly

* **Flat locks (k = 0): a data-sheet number, given `c` and the step unit.** `W/F =
  (c-1)·(held+1) + 1` own steps: 125 with two threads waits at most 66 steps, 59 on 64
  cores at most 2,584.
* **Nested locks: astronomical from three levels at realistic core counts.** 1.6·10⁹ own
  steps at depth 4 on 64 cores; already 8·10⁵ for 05 at depth 2 on 64 cores.
* **`F` is the other multiplier, and in a time-sliced system it is astronomical by itself.**
  The rows assume lockstep (`F = c`). A holder that can be preempted by a scheduler with
  quantum `q` G steps and `T` runnable threads gives `F ≈ T·q`; with `q ≈ 10⁷` (10 ms at one
  operation per ns) every row grows by seven orders of magnitude. Only the `masks irqs`
  locks (01, 05 KAPPEN, 53, 57, 59 TAKT) make the lockstep reading plausible for the holder.
* **Units.** `h = held` assumes one G step per operation. `K002` bounds operations; G also
  takes steps the checker prices at `0` (TARGET 3, F1-F9: branch unfolds, returns, the take
  and release themselves). The true `h` is `held + zusatz(body)`; not proved.
* **Contenders.** 14 of the 19 programs are library modules: `c` is a deployment parameter,
  not a program fact. Only 124 and 125 (`concurrent`) fix it; the entries of 57, 59 and 109
  fix it per core.

## 7. What would shrink them

1. **Dominance (the big one).** If every acquisition of the inner lock `L'` happens while
   holding `L` (05: SPEICHER only under KAPPEN; 17: PLAN only under PUNKTE), no thread
   ahead of the holder at `L'` exists -- they would all need `L` -- so the nested wait is at
   most `F`, not `W(L')`. Recomputed with `Wn = F`: 05 KAPPEN at `c = 64` falls from
   823,096 to **25,327** own steps, 17 PUNKTE from 165,376 to **2,647**, and the depth-4
   chain from 1.6·10⁹ to **6,427** -- flat in the depth. Decidable by the checker (every
   `locks L'` has `L` in its static holdings; every signature holding `L'` holds `L`); the
   theorem needs a per-lock contender set "among threads not holding `L`", which is `0` then.
2. **Per-lock contenders from the call graphs.** The theorem already takes `Ts L` per lock;
   the checker's `reachB` from the declared starts and entries gives it. `Anwaerter` is a
   premise today, not derived from `reachB` (§8).
3. **The computed block cost instead of the declared `held`.** `K002` computes the block's
   cost and compares it with `held`; the computed number is a valid `h` and often far
   smaller (the 2026-09-11 binary gives 1,027 for 42's `platz_melden` against `held <=
   20000`, 768 for 18's TOPO against 800 -- that binary predates lane 139's change to
   kosten.rs and was NOT re-run, so these two are illustrations, not measurements).
4. **`k` per section instead of "every own step may be a nested wait"** -- already in the
   theorem (`k(L)`); the corpus has `k ≤ 1`.
5. **Non-preemptible critical sections** (`masks irqs`) as the class in which the fairness
   window of a holder is the core count; for the rest, `F` must be named per scheduler.

## 8. What is proved and what is not

Proved (no `sorry`, no new axiom; `#print axioms`: `propext`, `Classical.choice`,
`Quot.sound`): `wartezeit_kern`, `wartezeit_schranke`, `sperre_schritt`,
`schritt_sperre_art`, `nimmt_an_sperre`, `ende_ret_kein_schritt`, and on the fixture
`lLauf`, `lZeuge`, `wartezeit_zeuge` (every premise discharged, bound 32, actual wait 10).

Premises that are NOT derived:
* `Haltezeit` (hold time in G steps) -- from `K002` it needs the ops-to-steps bridge and a
  potential bound for a `locks` body as a residue segment (`frame_schritte_beschraenkt`
  bounds frames, not blocks).
* `Anwaerter` (contenders) -- from `reachB` it needs the invariant "every frame of thread
  `t` runs a function reachable from `t`'s start" plus "a `locks L` head is a sub-term of
  that function's body".
* `LaufzeitAnnahme` (FIFO + `F`) and `HardwareImAbschnitt` -- assumptions by design; they go
  into the ONE assumption list (PLAN-ZIELSATZ §8).
