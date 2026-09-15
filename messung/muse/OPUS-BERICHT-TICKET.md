# OPUS report: the runtime's ticket lock stops being a premise

*2026-09-15, Opus agent (worktree `agent-af1ce634cd4e4d775`), built on `ki-pc-fisch-101`
(`~/gabbro-opus-tick`). Task: turn the named premise "`L_nimm`/`L_gib` behave as
`sperrAbstrakt`" into a theorem about the lock the runtime actually implements.*

**New files:** `grammatik/Grammatik/CTicket.lean` (the lock, generic over the unit; 932 lines),
`grammatik/Grammatik/Schlusssatz124Ticket.lean` (`beispiele/124` with the lock inlined, and the
contended witness; 166 lines). **Edited:** `grammatik/Grammatik.lean` (two imports),
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` (§7 header, §7.4 table, §7.6 item 3, new §7.7),
`dokumente/NICHTINTERFERENZ.md` (§10, the ONE list), `dokumente/SATZKARTE.md` (new §32; §26.2
and §26.6 cross-referenced). **Untouched:** `Parser/`, `Kette*.lean`, `KorrespondenzAllg.lean`,
`CParser/`, `emit.rs`, the MARKE counters, `CNebenlaeufig.lean`, `Schlusssatz124.lean`.

## 1. Which step was the smaller one, and why (task item 1)

Two routes were open. **Bridging to the ticket lock already in the tree is NOT the smaller
step**, and the measurement says why:

| | `Lebendigkeit.FifoSperre` | what stage (b) needs |
|---|---|---|
| lives over | infinite scheduled runs of machine **G** (`PlanLauf`, `AnSperre`, `offen …spur`) | configurations of the **C** semantics (`KonfC`, `Halter`, `SperrOp`, `SperrSem`) |
| shared definitions | **none** of the above appears in `CNebenlaeufig.lean` | — |
| says | acquisitions happen in arrival ORDER (liveness) | an acquire is SAFE: only a free lock, only the holder releases |
| is | an **assumption** (`LaufzeitAnnahme R F`), naming no counter | to be **discharged** |

Bridging would have meant inventing a G-to-C lock-order correspondence *and* writing the two
counters anyway. So the lock is written where the premise stands — in the interleaved C
semantics — as the four instructions the implementation has. The FIFO property of
`Lebendigkeit` then comes back out as a **theorem** in local form (`ticket_fifo`: while an
earlier ticket is outstanding, a later one cannot be served).

**The C the trust base supplies** (the emitter writes only the two prototypes, `emit.rs`
`ItemArt::Lock`: *"the primitive itself is trust base, not product"*):

```c
typedef struct { _Atomic unsigned next; _Atomic unsigned now; } L_wort;
static L_wort L;
void L_nimm(void) {
    unsigned my = atomic_fetch_add_explicit(&L.next, 1u, memory_order_relaxed);
    while (atomic_load_explicit(&L.now, memory_order_acquire) != my) ;   /* spin */
}
void L_gib(void) {
    unsigned n = atomic_load_explicit(&L.now, memory_order_relaxed);
    atomic_store_explicit(&L.now, n + 1u, memory_order_release);
}
```

Four instructions, four rules (`TSchritt`), one SC step each — finer than the one step per
`L_nimm()` call of `CNebenlaeufig.lean`: `zieht` (the `fetch_add`), `dreht` (a spin load that
finds `now != my`: nothing changes), `tritt` (the spin load that finds `now == my`: `L_nimm`
returns, and this is the one instruction at which the caller becomes the holder), `gibt` (the
release store). The thread's `my` is `TZust.zieht` (the local of `L_nimm`, live only inside the
call); its position between the return of `L_nimm` and the call of `L_gib` is `TZust.haelt` —
the caller's program counter, not a word of the lock.

## 2. What is proved (task item 2)

| theorem | statement |
|---|---|
| `tinv_schritt`, `zStart_inv` | the invariant `TInv` holds at the start and survives every instruction: `now ≤ next`; drawn tickets distinct and in `[now, next)`; **while somebody is inside `L`, every drawn ticket is strictly above `now`** (that last clause is what says "`now` is the holder's own ticket" without storing it anywhere) |
| `ticket_ausschluss`, `erreichbarT_exklusiv` | **mutual exclusion**: two threads never stand inside one lock, on every reachable state |
| `tritt_frei` | at the instruction where an acquire completes, nobody is inside the lock — this is where exclusion is earned |
| `ticket_nicht_wiedereintritt` | the lock is not re-entrant and does not pretend to be (a second `L_nimm` by the holder draws a ticket above `now` and spins forever) |
| `ticket_fifo` | **nobody overtakes a waiting thread** |
| `ticketLP_sperrAbstrakt` | **the refinement**: every abstract step the ticket lock induces is a `sperrAbstrakt` step |
| `ticket_frame` | a lock call leaves program memory alone and touches no other lock's holder entry or counters |
| `spinnt_nur` | a thread whose ticket is not served can only spin: every step it can take leaves its C configuration where it was |
| `schrittT_proj`, `erreichbarT_erreichbarC` | the emitted C **with the lock inlined** (`SchrittT`) reaches no configuration the abstract semantics does not reach: a spin is a stutter, everything else is a step of `SchrittC E sperrAbstrakt` |
| `schlusssatz_124_ticket` | for 124: mutual exclusion, `konto[0] == konto[1]` while nobody is inside, `privA[0] == 7` after `hauptA` returns — **with no premise about the lock** |

### The premise text that disappears, word for word

`schlusssatz_124` carries `LaufzeitC c124 [2,3] st0 K0 LP`, a structure with two fields. The
one that is gone in `schlusssatz_124_ticket` is

```
sperre : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h'
```

— i.e. "`L_nimm` fires only on a free lock and makes the caller its holder; `L_gib` fires only
for the holder and frees it; program memory untouched".

**What remains a premise:** `faeden : FadenStartC c124 [2,3] st0 K0` (threads start only at the
declared roots, each root at most once, from the declared initial memory, with no lock held —
still the runtime's), the `forever` budget `passes`, and — for a statement about the REAL
machine rather than the SC semantics — `DRFSC`.

**The theorem got strictly stronger, never weaker.** `schlusssatz_124` is unchanged: it still
quantifies over every `LP` and still carries `LaufzeitC`; not a line of `CNebenlaeufig.lean` or
`Schlusssatz124.lean` was touched, and `sperrAbstrakt` was not weakened. The new theorem is an
instance with one premise discharged, so the tree carries the general statement AND the
premise-free one for the lock that ships.

## 3. The witness (task item 3)

`ticket_zeuge_124`: a **23-step run** of the emitted C of `beispiele/124` with the lock inlined
(thread 0 runs `hauptA`, thread 1 `hauptB`), machine-checked as an indexed `LaufT`:

* steps 8–9: thread 1 draws ticket **0**, thread 0 draws ticket **1**;
* at `ks 10` the lock is **free** (`halter 0 = none`, nobody inside) **and thread 0 still
  cannot take it** — every step it can make leaves its C configuration where it was
  (`spinnt_nur`) — while `sperrAbstrakt` would admit its acquire, exhibited in the same
  statement (`∃ h', sperrAbstrakt 0 (.nimm 0) (ks 10).k.halter h'`);
* step 10: thread 0 spins (`dreht`); step **11**: thread 1 enters (`ts 11 = 1`,
  `ls 11 = .sperre (.nimm 0)`), and while it is inside, every step of thread 0 is again a
  stutter;
* steps 12–14: thread 1 runs `setze(70)` and releases; step **15**: only now does thread 0
  enter (`ts 15 = 0`, `ls 15 = .sperre (.nimm 0)`). **The acquisitions are in TICKET order, not
  in arrival-at-the-spin order** — thread 0 reached `L_nimm()` first and went second;
* steps 16–22: thread 0 runs `setze(30)`, releases, calls `pruefeA()`, both threads return;
* at `ks 23`: nobody is inside the lock, `konto[0] == konto[1]` and `privA[0] == 7` — both **by
  the theorem** (`schlusssatz_124_ticket`), read in the C through the relation — and
  `privA[0]` was `0` at the start.

This is the ticket-lock counterpart of `schlusssatz_124_zeuge`, and it contends harder: in the
old witness thread 1 simply "cannot step" while the lock is held; here the blocked thread is
*busy*, and the run shows both that it cannot get in while the lock is held **and** that it
cannot get in while the lock is free but its ticket is not served.

## 4. Two findings (task item 4)

The refinement DOES go through — but two halves of what the assumption list said about the lock
do not, and neither was repaired by weakening `sperrAbstrakt`.

### Finding 1 — the ticket lock reveals MORE than held or free (`ticket_mehr_als_frei`)

`sperrAbstrakt_nur_eigen` says: whether a call can proceed depends on that lock's holder entry
and on nothing else. **That is a theorem about the specification, and it is false of the
implementation.** The witness: two concrete states with the *same* abstract holder table (the
lock free in both) and one thread whose acquire completes in the one and cannot complete in the
other, because another thread drew the earlier ticket.

*Which step fails:* the acquire. Its enabledness is `now == my`, and `my - now` is the number of
requests that arrived before the caller's — the **arrival order of the other threads**, not
"held or free".

*Why stage (b) is unharmed:* the refinement runs implementation → specification. The concrete
lock has FEWER runs than the spec allows, and safety is preserved downward. What is NOT allowed
is to carry the NI-facing clause to the C: a noninterference claim about the emitted binary
cannot lean on "the lock reveals nothing but held or free", because the lock it would run on
does not have that property. *A lock that had it would have to serve waiters in an order
independent of their arrival.* Recorded in `NICHTINTERFERENZ.md` §10 as exactly that.

### Finding 2 — the release performs no check (`gib_ohne_wache`)

`L_gib` is an unguarded `now++`. It succeeds for any caller. The guard `L ∈ haelt t` on the rule
`gibt` is the CALLER's position between its `L_nimm` and its `L_gib` — a guarantee of the
**checker's lock discipline** (the emitter writes `L_gib()` only where the holder stands, W6),
not of the runtime.

*Which step fails without it:* the `.gib` half of `ticketLP_sperrAbstrakt`. `sperrAbstrakt`
demands `h L = some t` for a release; the hardware demands nothing. The witness runs it: from a
state where thread 1 is inside lock 0 and thread 2 waits on ticket 1, **one unguarded `now++`
by a thread that holds nothing** makes `TInv` false (`¬ TInv (gibtRoh zDrin 0)`) and lets thread
2 in while thread 1 is still inside — `0 ∈ haelt 1 ∧ 0 ∈ haelt 2 ∧ 1 ≠ 2`, mutual exclusion
gone.

*What the runtime would have to do differently to carry it alone:* keep the holder's identity in
the lock (`_Atomic unsigned besitzer`) and compare on release — one more word and one more
branch per release. That is precisely the check W6 declines to emit because the checker already
decided it. So the obligation "every `L_gib()` call is made by the holder" belongs in the ONE
list as a **checker guarantee**, which is where it now stands, rather than silently inside a
runtime assumption.

## 5. Standards and cost

* **Axioms.** `tinv_schritt`, `ticket_fifo`, `spinnt_nur`, `tritt_frei`,
  `ticketLP_sperrAbstrakt`, `ticket_frame`, `ticket_mehr_als_frei`, `gib_ohne_wache`,
  `schrittT_proj`, `erreichbarT_erreichbarC`, `erreichbarT_exklusiv`: `propext`, `Quot.sound`.
  `abs_eindeutig`: `Quot.sound`. `ticket_ausschluss`, `ticket_nicht_wiedereintritt`: none.
  `schlusssatz_124_ticket`, `ticket_zeuge_124`: `propext`, `Classical.choice`, `Quot.sound`.
  **`gabbro_ziel` unchanged**: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no
  `native_decide`, no new `axiom` (grepped over both files).
* **Build.** `lake build` over the whole library on `ki-pc-fisch-101`, queued through
  `~/gabbro-muse/bin/lean-slot`: **251 jobs, green**. The two new files cost **0,39 s and
  0,28 s**; the library's build cost is unchanged (no finding here).
* **Text guardians, measured against the baseline, not assumed.** `pruefe-zahlen.py` and
  `pruefe-todo.py` exit `1` on this branch — and they exit `1` on the same tree with my changes
  stashed away (`git stash -u`, both run, `git stash pop`). Their findings are the German
  comment ratchet in `crates/` (7892 booked, 7942 measured) and `TODO.md` entries; I touched
  neither. Nothing here moved them in either direction.

## 6. What remains (added to PLAN §7.6 / §7.7 and SATZKARTE §32.6)

1. **Race freedom at the ticket granularity.** `RennfreiC` is carried at the granularity of
   `SchrittC`. Transferring it to a `LaufT` needs the stutter-free compression of a ticket run
   into an SC run (`dreht`, `zieht` are stutters; the remaining steps keep their order) — pure
   index arithmetic, not written. Reachability and the two C-memory legs are carried.
2. **Wraparound.** The counters are `Nat` here and `unsigned` there; the model is the
   implementation as long as fewer than 2^32 tickets are outstanding for one lock.
3. **The orderings.** That the acquire-load and the release-store make the two instructions
   synchronisation points, and that every interleaving of them is SC, stays the named premise
   `DRFSC`.
4. **The bridge to the waiting bound.** `ticket_fifo` is the local form of
   `Lebendigkeit.FifoSperre`; connecting it to that predicate needs the G-level ↔ C-level lock
   correspondence, which stage (b) has only through the simulation relation of one program.
