# OPUS report — a lock chosen by the data

*Opus agent, branch `worktree-agent-a27cee17ec031bf3a`, 2026-09-16. All Lean and `cargo`
runs on `ki-pc-fisch-101:gabbro-opus-str2`. Not merged, not pushed.*

**The verdict, in one line: (b) — stripe the TABLES, not the locks. It needs no new
language, it checks today, and it was measured. (a) is sugar with no reach, and per-carrier
lock striping is (c)-impossible for a reason the model states rather than implies.**

---

## 0. The question and where it came from

A firewall is being written in Gabbro outside this tree (`/home/ubuntu/brandmauer`). Its
connection table is 1024 buckets × 4 slots, and every worker thread hits it on every packet.
`messung/BEFUNDE-bm3.md` F6 records that per-bucket-group locks could not be written:

> `requires Held` names a FIXED set, but which stripe lock a packet needs is data (the hash).
> […] One table, one lock (`VSPERRE protects { Verbindung, Stand } rank 0`), honestly coarse.
> If a later measurement shows the lock is the bottleneck, the honest upgrade is N stripe
> TABLES (disjoint carriers, one lock each) — not N locks on one carrier.

A coarse lock over a connection table is a firewall that does not scale past one core. This
lane decided what Gabbro can honestly offer instead — with the model in hand, not by taste.

---

## 1. The wall, measured: **it is not a refusal, it is a silence**

The firewall lane wrote that `E247` killed per-bucket locks. **That is not what happens.**
The smallest program in this tree that wants a lock per stripe is six lines of body, and the
measurement is worse than a refusal.

```gabbro
lock SPERRE protects { Verbindung } rank 0 held <= 64 ops;

impl fn suche(eimer : u32 in 0 .. 3, s : index into Verbindung) -> u32 in 0 .. 3
    requires Held(SPERRE[eimer])
    effects { reads Verbindung.slots, locks SPERRE }
    costs   <= 64 ops
{
    locks SPERRE {
        let v : u32 in 0 .. 3 = Verbindung.slots[s].zustand;
        return v;
    }
}
```

`gabbro pruefe`, verbatim, against the checker **before** this lane's change:

```
beispiele/gift/1050-held-mit-index.gab: 5 items, 0 errors, 0 hints
  M1 saw 4 expressions, 0 of them without a type (100 % coverage)
```

**Zero errors over a file whose only lock guard is a lock that does not exist.** And
`cc -std=c11 -Wall -Wextra -Werror -fsyntax-only` accepts the C it emits. Nothing catches
it — not the checker, not the compiler.

### 1.1 Where the clause went

`heldpred = "Held" "(" ident [ "," "shared" ] ")"` (`SYNTAX.md`). The bracket does not fit,
so `atompred` (`crates/gabbro-syntax/src/parse.rs:2726`) backtracks — and `versuch`
(`parse.rs:178`) restores the position **and truncates the refusals**. The words are then
re-read as an ordinary call inside an expression. The only channel in the whole toolchain
that mentions the clause at all is `gabbro lean`, in a doc comment over the body:

```
/-- `suche` -- the body, statement by statement.

    DROPPED from the precondition (a hypothesis fewer makes the goal harder,
    never the proof wrong): requires #1 (call-in-expression) -/
```

and `suche_pre` carries the parameter shapes and nothing else.

### 1.2 And it does not vanish cleanly — the phantom lock

`aufrufgraph::held_aus_expr` (`crates/gabbro-check/src/aufrufgraph.rs:1117`) pushes
`Ort::text()` of the argument into the held-lock set, and `Ort::text()` renders an index as
the literal `[…]`. Eight passes read that set. Two `concurrent` starts written this way drew,
in one run:

```
error: [N240] p2-phantom.gab:30:18: thread starts concurrent member `w0` and concurrent
member `w1` share a signature-held lock: `probe::phantom::w0` requires Held(SPERRE[…])
and `probe::phantom::w1` requires Held(SPERRE[…]) -- two threads never start holding one lock

hint: [H008] p2-phantom.gab:12:6: `SPERRE` protects ["Verbindung"] but is taken nowhere
```

**Two beliefs about one word, in one report.** `N240` refuses on a lock named `SPERRE[…]`
that no declaration carries, while `H008` says `SPERRE` is taken nowhere. The comment above
`held_aus_expr` predicted the class in 2026-08-31 — *"inert is not absent: it put an entry
into the held set that no declaration carries, and the next reader to compare by COUNT
rather than by name would have read it"* — and the reader that read it compares by NAME,
with a name that matches only itself.

The second malformed shape fails differently again: `Held(waehle(eimer))` has a non-`Ort`
argument, so nothing is pushed at all, and the file draws one `H007` — the right verdict
with the wrong reason ("`suche` does not hold it", of a function whose author wrote a guard).

---

## 2. What `Held(L[i])` would have to mean — answered in the model

New file **`grammatik/Grammatik/Sperrstreifen.lean`** (409 lines, no `sorry`, no
`native_decide`, no new `axiom`).

### 2.1 `darf` is CONJUNCTIVE, and that is the whole answer

`darf t Λ = ∀ w ∈ D.braucht t, Res.von D w ∈ Λ` (`Syntax.lean:244`) — **a ∀, not an ∃**.
`Ereignis.gut (.zugriff t w Λ h) = darf D t Λ ∧ HeldIn Λ h` (`Satz.lean:263`). Therefore:

| theorem | says |
|---|---|
| `zugriff_haelt_jeden_waechter` | every **good access event** to a carrier records **every** guard lock of that carrier as really held |
| `gzugriff_haelt_jeden_waechter` | the same for a global |
| `streifensperren_kosten_alle` | for a carrier with **two** guards, **both** are held at every access — F6, as a theorem |
| `darf_verlangt_jeden_waechter` | the static half: a hand that admits an access names every guard |
| **`ziel_haelt_jeden_waechter`** | **the same over the conclusion of `gabbro_ziel` itself**, through `Ziel.speicherSicher` (`SpurInv`, `RennfreiVoll.lean:249`) |

So the answer to *"what would `Held(L[i])` have to mean for the goal theorem to still hold?"*
is exact and unwelcome:

> **At the granularity of a carrier, `Held(L[i])` can only mean
> `Held(L[0]) ∧ … ∧ Held(L[N-1])` — the conjunction, not a choice.** N stripe locks over one
> table are N takes on every packet path and the same exclusion as one. They are strictly
> worse than the coarse lock, not better.

And the rule that would make it a choice is not available: a checker rule letting a
signature name ONE stripe lock while an access to the whole table proceeds would **falsify**
`Ziel.speicherSicher` on a reachable machine. The leg would have to go, and it is one of the
four the owner's goal names.

### 2.2 Why the granularity cannot simply be relaxed (what would have to change first)

Not claimed: that sub-carrier locking is impossible in principle. Claimed, and written in
the file's header: it is not expressible in **this** `Deklaration`.

* `Bewacht`, `darf`, `SperrInv.orte`, `TraegerSchreibt`, `fussOrteG`, `SchreibGetrennt`,
  `Getrennt` and `ZugriffG` all key on `c : D.Tab ⊕ D.Glob`. The **unit of race freedom is
  the carrier**: `RennfreiBis` demands `∃ L, Bewacht c L ∧ GeordnetG ms fs L i j` for two
  cross-thread accesses to ONE `c`. Two threads writing `Verbindung.slots[3]` and
  `Verbindung.slots[7]` are two accesses to `inl Verbindung`.
* `Expr.slot t f i hL` carries `hL : darf D t Λ` **beside** a runtime index
  `i : Expr D Γ Λ (.index (D.count t))`. The guard witness is part of the intrinsic typing
  derivation and cannot depend on `i`'s value. Making `Held(L[i])` mean "the region `i`"
  turns `Expr` from an intrinsically-typed syntax into a dependent Hoare logic.
* `SperrInvLokal` would have to read "reads only its stripe", with `TraegerGleich` refined to
  a region equality; `Ereignis.zugriff` would have to record the region.

That is a different model, not a rule. The NOT-CLAIMED list in `Zielsatz/Spec.lean` would
have to be rewritten for it, and every leg of `Ziel` that quantifies a carrier re-proved.

### 2.3 The positive side: the striped shape is admissible with nothing changed

Two concrete, non-degenerate declarations (real tables, real locks, distinct):

* **`grobD`** — ONE table, TWO locks (the shape F6 rejected):
  `grob_eine_reicht_nicht` / `grob_andere_reicht_auch_nicht` (neither lock alone admits the
  access) and `grob_braucht_beide` (both together do).
* **`strD`** — TWO tables, TWO locks, one each:
  `streifen_getrennt` (lock 0 admits stripe 0 and refuses stripe 1, and the other way round —
  **two threads, two hands, two carriers, at the same time**),
  `streifen_waechter_disjunkt` (no lock guards both stripes, so `RennfreiBis`'s `∃ L` never
  has to be met across stripes),
  `streifen_sperrInvOk` (`SperrInvOk` holds — i.e. the checker component
  `AkzeptiertSpec.sperrOrte` is satisfiable on the striped family, so the shape is admissible
  for `gabbro_ziel` with **no change to the statement**).
* And the honest counterpoint `grob_sperrInvOk`: the coarse-striped family is *also*
  well-formed. **`SperrInvOk` is not the obstruction; `darf` is.** The model does not forbid
  two locks on one carrier — it makes them cost both.

### 2.4 One price nobody had written down

`Ereignis.gut (.nimmt L h)` demands a **strict** rank rise over everything held (`H006`).
`gleicher_rang_kein_zweiter`: with `rang L = rang M`, no good `.nimmt` of `L` exists while
`M` is held. `streifen_nur_eine_richtung`: on `strD` (ranks 0 and 1) a thread holding stripe
lock `false` may still take `true`, never the reverse.

**Consequence for the firewall:** the packet path is fine either way — it takes exactly one
stripe lock. But an **aging sweep** over all stripes must take them one after another (which
is what you want: it blocks one stripe at a time), or the stripes need distinct ranks and
then the nesting has exactly one legal direction.

### 2.5 Axioms, measured

```
'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Unchanged, standard three.** Every new theorem depends on `propext` alone except
`ziel_haelt_jeden_waechter`, which inherits the goal theorem's three through `Ziel`. Full
`lake build Grammatik` green (`Grammatik.lean` gains one import).

---

## 3. The decision: **(b), striped TABLES**

### Why not (a) — a constant-foldable lock index

**It is sugar, and it does not reach the case.** With a compile-time-constant index,
`Held(L[3])` ≡ `Held(L3)`: no new expressiveness, and the firewall's bucket index is a
runtime hash, so nothing there becomes writable. Worse, it would not even help a program
that *could* constant-fold: the table would still be ONE carrier guarded by `L0…L15`, and
§2.1 says every access then holds all sixteen. **(a) buys a nicer spelling for a shape that
does not scale.**

### Why not (c) — "it cannot be done honestly today"

Because it **can**, for the thing the firewall actually needs, and saying otherwise would be
the easy answer. What *cannot* be done honestly today is per-carrier lock striping, and §2
says exactly which part of the model forbids it and what would have to change first. Those
are two different claims and the report keeps them apart.

### Why (b)

Striped tables give every carrier exactly one guard and make the guard sets disjoint. That is
the parallelism, and it is expressible **now**. The trick is that the stripe is data but the
**lock in each branch is not**: the checker never decides which lock a value picks; it reads
N branches, each naming one constant lock and one constant table.

---

## 4. The payoff, on the real program

In scratch (`.kratz-str2/`, generated by `.kratz-str2/gen-striped.py`, not committed; the firewall project was not
touched): the same 4096-entry connection table — canonical 5-tuple, XOR-fold hash, 4-slot
bucket scan unrolled, per-direction timestamp, refuse-when-full with counters — written
coarse and striped 2 / 4 / 8 ways.

| variant | source lines | items | `pruefe` | packet path, computed ops | `_nimm`/`_gib` pairs **per packet** | threads in the table at once |
|---|---|---|---|---|---|---|
| coarse (1 table, 1 lock) | 165 | 13 | 0 errors, 0 hints | **366** | 1 | **1** |
| 2 stripes | 297 | 21 | 0 errors, 0 hints | 372 (+6) | 1 | **2** |
| 4 stripes | 547 | 37 | 0 errors, 0 hints | 376 (+10) | 1 | **4** |
| 8 stripes | 1047 | 69 | 0 errors, 0 hints | **384 (+18)** | 1 | **8** |

Every variant emits and compiles clean at **-O0 and -O2** (`cc -std=c11 -Wall -Wextra
-Werror`): 194 / 340 / 638 / 1234 lines of C.

**What it buys, in one sentence: eight times the concurrency in the table for 4.9 % more ops
on the packet path** (366 → 384) **and 6.3× the source** (165 → 1047 lines, ≈126 lines per
stripe).

The emitted packet path is exactly what a hand-written striped table looks like — one branch
chain, one take:

```c
    uint32_t streifen = h % STREIFEN;
    uint32_t roh_eimer = (h / STREIFEN) % EIMER_JE;
    if (!(roh_eimer < EIMER_JE)) { return 0; }
    uint32_t eimer = roh_eimer;
    uint32_t antwort = 0;
    if (streifen == 0) {
        S0_nimm();
        { antwort = eimer_0(eimer, a, b, pa, pb, iprot, jetzt); }
        S0_gib();
    } else {
        if (streifen == 1) { S1_nimm(); { … } S1_gib(); } else { … }
    }
    return antwort;
```

The lock path per packet is therefore **one acquire, one release, plus the dispatch**: a `%`,
a `/`, and at most N−1 integer compares (the if/else chain is linear, not a jump table — the
honest cost, and the reason the +18 at eight stripes is dispatch and not locking).

### Two prices, both measured, neither hidden

1. **Anything that shared the lock stripes with it.** The firewall's `Stand` counter table
   lives under `VSPERRE`. Kept global under `S0…S7`, it would be ONE carrier with eight
   guards, and by §2.1 every access holds all eight — the coarse lock back again, in
   disguise. The striped version gives each stripe its own `Stand<k>`.
2. **N distinct worker roots.** The first honest attempt wrote `concurrent { suche, suche }`
   and was refused:

   ```
   error: [N304] … concurrent member `suche` and concurrent member `suche` run one routine
   `suche`, and it is not idle -- it holds a lock, declares a reason, writes a carrier, or
   carries a footprint
   ```

   `Laufzeit.einmal` (`Zielsatz/Spec.lean:548`) admits one thread per busy start, and
   *"one thread per busy start (SMP-symmetric code running one start on several cores is
   outside (d))"* is in the NOT-CLAIMED list. **SMP symmetry has to be spelled out**: N
   near-identical worker roots. This is a second wall, independent of locks, and it is the
   one a firewall driver meets first.

### The negative control

Dropping one `requires Held(S0)` from the striped file is refused four ways — the discipline
is real and not an artefact of the shape:

```
hint:  [E247] `V0` is read by the body of `suche0` but no signature lock guarding it is held…
error: [H020] `V0.slots[…].schluessel` is protected by `S0`, and no guard is held at this write…
error: [H020] `V0.slots[…].zustand` …
error: [H011] `suche0` declares `locks S0` but never takes it
error: [N291] `V0` is read by the body of `suche0` … and it is not thread-local -- another
       started thread writes it
```

---

## 5. What was built

| what | where |
|---|---|
| The model side | `grammatik/Grammatik/Sperrstreifen.lean` (new), `grammatik/Grammatik.lean` (+1 import) |
| The checker rule **N390** | `crates/gabbro-check/src/domaene.rs` (`held_form_pruefen`, called from the `Vergleich` and `Element` arms of `aus_pred`) |
| Its sentence | `crates/gabbro-check/src/saetze.rs`, `d.heldform` |
| Poison probes | `beispiele/gift/1050-held-mit-index.gab` (`-- erwartet: N390 allein`), `beispiele/gift/1051-held-ueber-einen-ruf.gab` (`-- erwartet: N390`) |
| Positive probe | `beispiele/146-sperrstreifen.gab` (four tables, four locks, a dispatch, four roots) |
| Ledger | `messung/KENNZAHLEN.md`: gift-only grammar cells `25 → 24` |

**N390 refuses a SHAPE; it does not offer one** — and that is said in its own reservation.
The scaling shape needs no rule at all. What the rule buys is that the person who writes the
striped guard the wrong way is told so, at the words, with the way out — instead of getting
`0 errors, 0 hints` over a lock that does not exist.

Verbatim, on the poison probe:

```
error: [N390] beispiele/gift/1050-held-mit-index.gab:46:14: `Held(…)` in `requires` names the
place `SPERRE[…]`, and a lock guard names a DECLARED lock and nothing else -- a lock picked by
a value is not one a signature can promise
   46 |     requires Held(SPERRE[eimer])
      |              ^^^^^^^^^^^^^^^^^^^
      = the rule is `Held "(" ident [ "," "shared" ] ")"`; anything else backtracks out of it
        and is re-read as a call in an expression -- it then reaches no pass, `gabbro lean`
        DROPS it from `<fn>_pre`, and what is left behind is a lock name no declaration
        carries, which `N240` and `N303` read and print
      = a table striped over N locks is not N choices but one conjunction: every access needs
        EVERY guard of its carrier (`H007`). What scales is N TABLES with one lock each,
        chosen by a dispatch whose branches name constant locks -- one `locks` take per call,
        N threads in the structure at once
```

`1 errors, 0 hints` — the code falls **alone**, and the `allein` contract is measured: without
the rule the emitted C passes `cc -Werror -fsyntax-only`.

---

## 6. Guardians, measured before and after

Baseline taken on the same tree with this lane's changes stashed; binary rebuilt for both runs.

| guardian | before | after | what moved |
|---|---|---|---|
| `cargo test --no-fail-fast` | — | **1081 passed, 0 failed** | — |
| `pruefe-saetze.py` | exit 0 | **exit 0** | 411 → 412 codes, 165 → 166 sentences, **55 without a sentence: unchanged** (`MARKE = 55` holds — the code and its sentence arrived together) |
| `pruefe-kennungen.py` | exit 0 | **exit 0** | 411 → 412, `N: 127 → 128`; one code, one file |
| `pruefe-vergabe.py` | exit 0 | **exit 0** | 432 → 433 sites, 347 → 348 codes; `MARKE = 35` candidates unchanged |
| `pruefe-gruende.py` | exit 0 | **exit 0** | `tragend` 178 → 179, `verdaechtig` 9 unchanged — the new text reasons about the PROMISE |
| `pruefe-englisch.py` | exit 1 | exit 1 (**pre-existing**) | `MARKE_ZUBRINGER` count **unchanged at 30**: two prose pieces first tripped it (a quoted Lean identifier and a hyphenated filename) and were rephrased |
| `zaehle-gifttreffer.py` | exit 1 | exit 1 (**pre-existing**) | 686 → 688 probes, `sauber` 497 → **498** (1050 falls alone), `begleitet` 142 → 143 (1051 falls beside `H007`/`H008`, by design and documented in the probe) |
| `pruefe-zahlen.py` | exit 1 | exit 1 (**pre-existing**) | the one figure this lane moved that was **correct before** — gift-only grammar cells 25 → 24 — is updated in `KENNZAHLEN.md` and green again. Every other delta is a ledger that was already stale at baseline. |
| `pruefe-todo.py` | exit 1 | exit 1 (**pre-existing**) | README counters drift further (114 → 115 examples, 686 → 688 gifts, 411 → 412 codes); they were already wrong by ~20 at baseline and belong to the merger |
| `pruefe-emission.sh` | — | **ALL PASS** with one bump | `MARKE_EMIT=114` → **115** (`beispiele/146`). Measured by provisionally bumping on the server: *"EMISSION: ALL PASS -- 37 durchgestochen, 276 von 276 uebersetzen"*. **The counter is NOT changed on this branch** — AGENTS.md §5 reserves the emission counters for the merger. Without the bump the run stops at stage 9 with `FUND: 115 statt 114`, which is the good case and still a finding. |
| `lake build Grammatik` | — | **green** | — |
| `#print axioms gabbro_ziel` | `propext, Classical.choice, Quot.sound` | **identical** | — |

---

## 7. What I did NOT do, and what I would hand on

* **Nothing in `/home/ubuntu/brandmauer` was touched.** The striped table lives in this
  lane's scratch. Whether the firewall takes it is operations' call, and it costs ≈126 source
  lines per stripe.
* **No contention measurement.** "Eight threads in the table at once" is a statement about
  the lock structure, not about throughput: the workers still share a memory bus, the hash
  may bunch, and `4.9 % more ops` is `gabbro kosten`'s count, not a nanosecond. The firewall
  lane's own note stands — *"whether the coarse lock costs throughput is open until the
  driver exists"* — and the striped table's `voll`/`treffer` counters are now per stripe,
  which is also the instrument for measuring stripe balance.
* **`N390` is by NAME.** A user function called `Held` in a contract is refused. That is the
  same coarseness `D021`'s existing `Held`/`Has` exemption carries, and it errs toward a
  refusal.
* **The phantom lock name is now unreachable from a contract, but `held_aus_expr` still
  builds it.** N390 refuses the shape before any consumer reads the set, so nothing prints
  `SPERRE[…]` any more — but the push at `aufrufgraph.rs:1130` is still there and would still
  fire if another producer of malformed `Held` expressions appeared. Dropping it is the
  conservative direction (fewer locks held means more refusals); it is a one-line follow-up
  and I left it, so that one change is measured at a time.
* **`Laufzeit.einmal` is the wall behind the wall.** Every SMP-symmetric worker pool in
  Gabbro today is N copies of one routine. That is a bigger ceiling for a firewall than the
  lock was, it is in the NOT-CLAIMED list of `Zielsatz/Spec.lean`, and it is worth its own
  lane.
