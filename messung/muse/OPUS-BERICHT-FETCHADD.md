# OPUS-BERICHT-FETCHADD — the emitter's `atomic_fetch_*` arm, and where it stops

*Opus lane `fetchadd`, 2026-09-15. Branch `worktree-agent-a571af7f659029c5f`, from master
`f470f344`. Server directory `gabbro-opus-fadd`. Follows `messung/muse/MUSE-REPORT-201.md`
(the ticket lock written in Gabbro) and TODO.md §0.*

---

## 0. Verdict up front, in the order it matters

1. **The arm is built, and it is a THIRD of what the headline asked for.**
   `t | m`, `t & m` and `t ^ m` in an `exchange update` body now lower to ONE
   `atomic_fetch_or/and/xor_explicit` — no loop, no pass counter, no fail-stop exit.
   **`atomic_fetch_add` and `atomic_fetch_sub` are NOT built, and not because the table is short: they are unreachable in
   today's language.** §1 is the table, §2 is the proof.
2. **`laufzeit/sperre.gab` is byte-for-byte unchanged, and so is the whole rest of
   the tree.** Measured over **1018 `.gab` files** emitted with the old and the new
   emitter: the baseline contains **0** occurrences of `atomic_fetch` anywhere, and
   exactly **one** file's C differs after the change — the new example `134`. The
   ticket draw is still a 64-pass CAS loop. **0 of `CTicket.lean`'s four instructions
   moved** (§3).
3. **Nothing was given up to get here.** No refusal was lifted, no check dropped,
   no bound weakened. `bounded … ops on_exceeded …` is still demanded at the
   construct even where the lowering is one instruction; the fall-through check
   still runs; the `never` exit is still required. The clauses lose their
   *consequence*, not their obligation.
4. **The one thing that would unlock fetch-add is named with its price** (§2.3), and
   it is **not built**, because building it means deciding a question this lane was
   told to measure rather than answer: whether `t +% 1` over an `exchange` binder may
   resolve its modulus from the atomic's own declaration.
5. Side finding, repaired: an `exchange` result nothing reads back produced C that
   **does not compile** — out of BOTH lowerings, before and after this lane (§5).
6. **Second side finding, and it is another lane's:** `./instrumente/pruefe-emission.sh`
   was **already red on `master f470f344`** — `laufzeit/sperre.gab` (lane 201) is a sixth
   emitting root that nobody booked, the guardian left with `1`, and stage 10 never ran.
   Measured at the baseline with this lane's diff stashed; repaired here by booking
   `laufzeit/` as a root **with a ratchet of its own** rather than by raising the
   catch-all (§4a).

---

## 1. THE TABLE — which update bodies lower to `atomic_fetch_*`

Measured first, on `probe/p1.gab` … `p4.gab` (server `gabbro-opus-fadd/probe/`),
**before a line of the arm was written**. The C11 column is §7.17.7.5: *"Atomically
replaces the value pointed to by `object` with the result of the computation applied
to the value pointed to by `object` and the given operand… Returns, atomically, the
value pointed to by `object` immediately before the effects"* — and the key word in
the name matches the operator (`add` `+`, `sub` `-`, `or` `|`, `xor` `^`, `and` `&`).
An `exchange update` binds the OLD value, so the return side agrees by construction.

`X` is the atomic, `t` the `exchange` binder, `m` a translation-time constant, `T`
the atomic's C type.

| # | body | lowers to | C11 semantics beside it | why here |
|---|---|---|---|---|
| 1 | `return t \| m;` | `atomic_fetch_or_explicit(&X, (T)(m), ord)` | `*X = *X \| m`, old returned; bitwise, no overflow question | **IN.** Checks clean (`u32 \| u8` leaves no range). Commutative, so `m \| t` is the same row. |
| 2 | `return t & m;` | `atomic_fetch_and_explicit(&X, (T)(m), ord)` | `*X = *X & m`, old returned | **IN**, same reasons. |
| 3 | `return t ^ m;` | `atomic_fetch_xor_explicit(&X, (T)(m), ord)` | `*X = *X ^ m`, old returned | **IN**, same reasons. *Not in `SPRACHE.md`'s written table (`t+1`, `t-1`, `t\|m`, `t&m`) — it is the fourth bitwise fetch C11 defines and the same argument covers it; §6 books the doc line.* |
| 4 | `return t + 1;` | **CAS loop, and the file does not even emit** | `atomic_fetch_add` wraps silently (signed included: C11 converts to unsigned, computes, converts back — no UB) | **UNREACHABLE.** `M104` + `M101` at the checker, for every atomic type. §2.1. |
| 5 | `return t - 1;` | **CAS loop, file does not emit** | `atomic_fetch_sub`, same | **UNREACHABLE**, same interval argument. §2.1. |
| 6 | `return t +% 1;` `return t -% 1;` | **CAS loop — and `C001`, so no C at all** | exactly `atomic_fetch_add/sub`: both wrap by definition | **OUT, and this is the row that costs something.** §2.2/§2.3. |
| 7 | `return m - t;` | CAS loop | `atomic_fetch_sub(&X, t)` computes `X - t`, **not** `m - t` | **OUT.** Subtraction is not commutative; a table that commuted would give this body a different operation and nothing would say so. |
| 8 | `return t \| t;` | CAS loop | — | **OUT.** The operand would be `t`, a name that lives only inside the loop the arm would have removed. |
| 9 | `return t \| p;` (`p` a parameter) | CAS loop | — | **OUT.** In the loop the body runs once per pass; as a fetch operand once. For a constant those are the same value by construction; for a runtime value only if the emitter reasons about what may change between passes — and it would be doing that silently. |
| 10 | `return t >> 1;` `return t * m;` … | CAS loop | C11 has no such fetch | **OUT.** Not a fetch form in any C. |
| 11 | `if t < N { return t + 1; } return t;` | CAS loop | — | **OUT.** The whole corpus shape (`beispiele/05`, `41`, `42`). Not one operation; no single instruction computes it. |
| 12 | `return t;` | CAS loop | — | **OUT.** Not a binary shape. (`messung/proben/absenkung/probe-absenkung-exchange.gab` — unchanged, byte for byte.) |
| 13 | any body, `atomic … : bool` / `f32` / `f64` | CAS loop | C11 defines `atomic_fetch_*` for **integer** atomics only | **OUT.** The word list (`uint8_t`…`int64_t`, the eight `ganzzahlwort` writes) is part of the table, not a formality. |

**The ordering column**, derived from the emitter's own map (`Namen::atomics`, which
holds the declared STORE side and the load side derived from it) and from nothing
else. A CAS loop can spend two orders — it has a load and a store. One RMW
instruction has one argument and must carry their **join**:

| declaration | `Namen::atomics` pair | fetch order |
|---|---|---|
| `relaxed`, or no ordering word | (relaxed, relaxed) | `memory_order_relaxed` |
| `release` | (release, acquire) | `memory_order_acq_rel` |
| `acquire` | (release, acquire) | `memory_order_acq_rel` |
| `seq` | (seq_cst, seq_cst) | `memory_order_seq_cst` |

A pair not in that table is a **CAS loop, not a guess** — `holordnung` returns
`None`. The `Atomic` arm of `sammle_namen` was repaired once for exactly this class
(a catch-all that chose a memory model by default), and this table is written the
same way.

**What the arm does NOT keep from the loop, and what it keeps:**

| loop has | fetch arm | |
|---|---|---|
| pass counter `_ciN` | gone | the C has no pass to count |
| `on_exceeded f()` call | gone | nothing to exceed |
| pre-loop `atomic_load_explicit` | gone | the RMW reads |
| `atomic_compare_exchange_weak_explicit` | replaced by the one fetch | |
| `bounded … ops on_exceeded …` **clauses required at the construct** | **KEPT** | a construct that drops its own clauses when the generator finds a shortcut makes the shortcut a language rule |
| `on_exceeded` must name a `never` function | **KEPT** | a bound whose exit returns is a number without a consequence |
| body must `return` on every path | **KEPT** | (trivially satisfied by a single `return`) |
| `publishes`/`awaits` comment lines | **KEPT**, byte for byte | what the C carries, the C says |

---

## 2. Why `atomic_fetch_add` is not here — the measurement

### 2.1 The checked operators are unreachable, and it is an interval argument, not a sample

An `update` body without a side condition must answer **in the atomic's own type, for
every value the atomic can hold** — it is applied to whatever the load found. A
checked `t + 1` shifts the interval by one, so it would need
`[lo+1, hi+1] ⊆ [lo, hi]`, which is false for every non-empty interval. Likewise
`t - 1` needs `[lo-1, hi-1] ⊆ [lo, hi]`. **There is no atomic type, ranged or not,
signed or unsigned, narrow or wide, for which checked `±1` is writable.**

Measured (`probe/p1.gab`, `probe/p2.gab`, and the two poison rows of
`crates/gabbro-check/tests/holform.rs`):

```
atomic NEXT : u32 relaxed;              { return t + 1; }
  -> error [M104] `u32 + u8 in 1 .. 1` leaves the width of the result type
  -> error [M101] the return value requires `u32`, the value has `u32 in 1 .. 4294967296`
     `gabbro emit`: 2 errors -- NO C WRITTEN.

atomic GESTUFT : u32 in 0 .. 1000 relaxed;   { return t + 1; }
  -> error [M101] ... the same rule, one error nearer.

{ return t + 2; }  -> M104, M101 -- the literal is not what refuses it.
```

**M1 is right and this lane does not touch it.** An emitter arm for `+` would be
dead code: no file can reach it.

### 2.2 The wrapping operators are the ones that MATCH C11, and they are refused

`atomic_fetch_add` wraps silently by definition; so does `t +% 1`. They are the same
operation. And `laufzeit/sperre.gab` writes exactly that shape — by way of a helper,
because the direct form is refused:

```
atomic NEXT : u32 relaxed;              { return t +% 1; }
  -> gabbro pruefe: 0 errors
  -> gabbro emit:  error [C001] no lowering: wrapping `+%` over operands whose exact
                   ranges cannot be read off their declarations -- both sides need an
                   exact unsigned range `0 .. 2^N - 1` on one storage width
```

The cause, read off the emitter: `wrap_side` resolves a bare name through `ort_typ`,
which looks in `statiken` and `parametertyp` — **statics and parameters only**. An
`exchange` binder is in neither. That is why lane 201 had to move the wrap into
`impl fn folge(x : u32)`: a PARAMETER resolves.

### 2.3 What lifting it would cost, exactly — and why this lane did not

**The refusal protects something real.** `+%` wraps at the operands' *exact* range,
not at the storage word. Two cases the same C type cannot tell apart:

| declaration | `t +% 1` means | `atomic_fetch_add(&X, 1)` means | verdict |
|---|---|---|---|
| `atomic NEXT : u32` | mod 2^32 | mod 2^32 | **the same operation** |
| `atomic Z : u32 in 0 .. 65535` | mod 2^16 | mod 2^32 | **a DIFFERENT operation, silently** |

So a fetch-add arm for `+%` is only sound where the wrap modulus equals the storage
width. **That is decidable here** — an `exchange update(t)` binds `t` at exactly the
atomic's declared type, and the atomic's declaration is the one place the range IS
readable. Feeding that type into `wrap_side` would run the *same* exactness test
(`exact_wrap_n`, `n <= bits`, the literal inside the range) with better information;
the narrow case above would still refuse.

**It is still two changes, not one,** and the second is the one this lane was told
not to make:

1. it lifts a live `C001` (an acceptance where there was a refusal), and it lifts it
   for the CAS-loop path too, not only for the fetch path — `t +% 1` over a binder
   would start lowering as a masked wrap in every `update` body;
2. the task set for this lane names "a wrapping form" among the bodies that must
   **not** become a fetch-add, and building the opposite of that on my own judgement
   would be answering a question I was asked to measure.

**So: measured, named, not built.** The whole change would be: resolve an `exchange`
binder's type from `Namen::atomics` at the `Update` arm, hand it to `wrap_side`, and
add rows 4′/5′ to the table above **gated on `n == storage bits`** with a poison probe
on `u32 in 0 .. 65535`. It is the owner's call, and it is the only thing between the
ticket draw and wait-freedom.

> A wait-free primitive bought by guessing a modulus is not an improvement. This one
> would not be a guess — but it is a decision, and a decision is not a lowering.

---

## 3. `laufzeit/sperre.gab` re-emitted, beside `CTicket.lean`'s four instructions

Re-emitted with the new emitter: `7 items, 0 errors, 2 hints` (the two standing
`E247`, unchanged), and the C is **byte-identical to lane 201's** — verified as part
of the 1018-file comparison in §4. The ticket draw's body is `return folge(t);`, a
CALL, which is not a fetch form in any reading of the table.

`CTicket.lean`'s trust-base C (file head, lines 19–31) beside the emitted C:

| # | `CTicket.lean` instruction | emitted C after this lane | verdict | moved? |
|---|---|---|---|---|
| 1 | `zieht`: `my = atomic_fetch_add_explicit(&L.next, 1u, relaxed)` — ONE step, never fails | `nimm`: `load_relaxed(NEXT)` + `folge` + `compare_exchange_weak_relaxed` in `for(;;)`, max 64 passes, then `_Noreturn warte_aufgegeben()` | **DIFFERS**, exactly as lane 201 measured. Orderings match (relaxed/relaxed), wrap matches (mod 2^32). Wait-freedom absent; fail-stop after 64 lost races, so still no duplicated ticket. | **NO.** §2 is why. |
| 2 | `dreht`: `load_acquire(&L.now) != my`, nothing changes | counted `for` with empty body over `!(atomic_load_explicit(&NOW, acquire) == my)`, bound `_r1 < 1431655765u` | **MATCHES, with a bound** | no — this lane does not touch `retry` |
| 3 | `tritt`: `load_acquire(&L.now) == my`, `L_nimm` returns | loop exit, fall out of `nimm`; overrun calls `warte_aufgegeben()` | **MATCHES, with the same bound** | no |
| 4 | `gibt`: `atomic_store(&L.now, now+1, release)` — ONE store | `gib`: `n = atomic_load_explicit(&NOW, acquire); atomic_store_explicit(&NOW, folge(n), release)` | **DIFFERS by the extra load** (matches the trust-base C, which is also load+store; the load order is `acquire` where the trust base uses `relaxed` — stronger, and `publishes nothing`) | **NO, and this lane does not touch it at all.** `NOW = folge(n)` is a `publishstmt`, not an `exchange`; no line of the fetch arm is on that path. |

**So the count is: 2 of 4 match (with bounds), 2 differ, and this lane moved
neither.** The release store's extra load is exactly the other known difference lane
201 named, and the change made here does not reach it — said plainly, because a lane
that repairs one half is easy to read as having repaired both.

---

## 4. Guardians — before and after, from a clean tree, on `fisch`

All runs in `~/gabbro-opus-fadd`, `export PATH=$HOME/.cargo/bin:$PATH`.

**Corpus emission, the load-bearing measurement.** Every `.gab` under `beispiele/`,
`messung/`, `messungen/`, `programmlogik/`, `laufzeit/`, `dokumente/` emitted twice —
once with `git show HEAD:crates/gabbro-check/src/emit.rs` in place, once with this
lane's — and the two trees of C compared file by file:

```
emitted 1018   (baseline)      grep -rl atomic_fetch  ->  0 files
emitted 1018   (this lane)     grep -rl atomic_fetch  ->  1 file
diff -rq /tmp/c-alt /tmp/c-neu
  Files .../beispiele_134-holende-bitzuege.gab.c differ     <- the new example
  (nothing else)
```

*The baseline's `0` is lane 201's finding measured over the whole tree and not only
over `sperre.gab`: the emitter had no `atomic_fetch_*` anywhere.*

**Counters.** `MARKE_EMIT` 113 → **114**, dated and reasoned in
`instrumente/pruefe-emission.sh` beside the previous entries, for the one new
emitting corpus file. `MARKE_EMIT_G`, `_M`, `_N`, `MARKE_UMGEKEHRT` untouched: this
lane adds no refusal, no poison file and no `messung/` probe.

### 4a. And the emission guardian was ALREADY RED on master — measured, not reasoned

Running it at the baseline (this lane's diff stashed, the tree rebuilt, the probe
`.gab` files moved out of the tree so the population is the real one):

```
  265 von 265 emittierenden Dateien uebersetzen; 0 benannte Ausnahmen,
  (113 beispiele/, 18 beispiele/gift/, 132 messung/*/, 2 messungen/,
   1 programmlogik/, 1 sonst -- SECHS Marken)
  NEUE WURZEL EMITTIERT: 1 Dateien ausserhalb der fuenf gebuchten Wurzeln
                         emittieren, gebucht sind 0 ... laufzeit/sperre.gab
== EMISSION: die REGEL haelt nicht -- eine neue Form ist am C-Uebersetzer vorbei ==
== ABGESCHNITTEN in: Stufe 9 -- Ruecklaufwert 1 ==
EXIT=1
```

**`master f470f344` leaves this guardian with `1`, and stage 10 (the library chain)
never runs.** The cause is not this lane: lane 201 added `laufzeit/sperre.gab`, a
SIXTH root, and the `MARKE_EMIT_X` catch-all noticed it and said so by name — which is
exactly what that mark exists for. Nobody booked it.

**Repaired here, and not by raising the catch-all.** `laufzeit/` becomes the sixth
BOOKED root, with `MARKE_EMIT_L=1` and a `ratsche` of its own; `MARKE_EMIT_X` stays at
`0` with the reason written beside it. The difference matters: a root that lives in the
catch-all has no ratchet, so a file *leaving* the emission there would go unseen — and
a mark that only ever rises is the half of `W16` that reads like a measurement.
`laufzeit/start.c` is C, not `.gab`, so it counts nowhere.

*This is another lane's debt paid in passing, and it is booked as such in the file's
own comment style, dated, with the baseline measurement named.* Without it, "the
emission guardian ends ALL PASS" would have been unreachable from this branch for a
reason that has nothing to do with `atomic_fetch_*`.

**`cargo test --no-fail-fast`** — see §7 for the run log.
**`./instrumente/pruefe-emission.sh`** — see §7.

---

## 5. The side finding, and it is a `cc` defect that predates this lane

**An `exchange` result nothing reads back produces C that does not compile.**
Measured on `probe/p3.gab`, 2026-09-15, with the OLD emitter:

```
error: variable 'alt' set but not used [-Werror=unused-but-set-variable]
    uint32_t alt;                     <- the bounded CAS loop's declaration
```

and with the new arm, the same hole one warning over:

```
error: unused variable 'alt' [-Werror=unused-variable]
    uint32_t alt = atomic_fetch_or_explicit(...);
```

**Both families fell, so this is not a cost of the new arm — it is a gap the new arm
made visible.** An `exchange` binding is the third name that binds outside
`sammle_lets` (beside `awaits` and `alloc`), so the shared unread-`let` set could not
carry it. `Austritt::stille_exchanges` now does, collected **recursively** (every
`exchange` in the corpus stands inside a nested block — `beispiele/41-handschlag.gab`
inside an `if` — so a top-level-only walk, which is what the `awaits` list does, would
answer "nothing to silence" for exactly the shapes that occur). All **three**
`exchange` lowerings read it: the loop, the fetch instruction, and the
compare-exchange.

**Byte-identical over the corpus**: every `exchange` in `beispiele/` reads its result,
so nothing gained a `(void)` line — confirmed by the 1018-file diff in §4.

---

## 6. Diff, and the reserved numbers

| file | what |
|---|---|
| `crates/gabbro-check/src/emit.rs` | `holform` (the table), `ohne_klammern`, `holordnung` (the ordering join), the `«C4c»` block in the `XForm::Update` arm, `Austritt::stille_exchanges` and its three readers |
| `crates/gabbro-check/tests/holform.rs` | **new, 28 tests** — a positive probe for every arm and a poison probe for every boundary row of §1 |
| `beispiele/134-holende-bitzuege.gab` | **new** — the three fetch forms and, in the same unit, the saturating body that keeps its loop |
| `instrumente/pruefe-emission.sh` | `MARKE_EMIT` 113 → 114 for example `134`; **`laufzeit/` booked as the sixth root** (`MARKE_EMIT_L=1`, its own `ratsche`, `MARKE_EMIT_X` stays `0`) — both dated with their reasons, §4a |
| `messung/muse/OPUS-BERICHT-FETCHADD.md` | this report |

**Reserved and USED:** example number **134**.
**Reserved and NOT used, still free:** diagnostic codes **N370–N379** (this lane adds
no refusal — the arm only decides between two lowerings, and where it declines, the
existing `C001` or the existing loop answers); gift numbers **1030–1039** (no new
poison file: every poison row is a *lowering* assertion, which only the emitted C can
carry, so they live in `tests/holform.rs`); example numbers **135–139**.

**Not touched:** `Parser/`, `crates/gabbro-check/src/m1.rs`,
`crates/gabbro-check/src/saetze.rs`, `messung/schreibprobe/`, `grammatik/` (no Lean
written, so no `sorry`, no `native_decide`, no new `axiom` — and `pruefe-exportlean.py`
/ `pruefe-genlean.py` have nothing new to elaborate or to compare).

**One documentation line is OWED and is not written here:** `SPRACHE.md` Part III §1
writes the pattern table as `t+1`, `t-1`, `t|m`, `t&m`, `max` via `accumulates`. What
the emitter now has is `t|m`, `t&m`, **`t^m`**, and NOT `t+1`/`t-1`. The doc and the
emitter therefore still disagree, in the opposite direction from lane 201's Finding 2:
the doc promises two rows that cannot exist and misses one that does. *Seven guardians
read document text and four go silently blind when it moves* (CLAUDE.md), so the
patterns come before the prose — booked as a follow-up rather than done in passing.

---

## 7. Runs

Both on `ki-pc-fisch-101`, in `~/gabbro-opus-fadd`, sequentially (never beside each
other — `cargo test` and a guardian that calls `cargo run` in one tree measure a
mixture):

```
cargo test --no-fail-fast         -> exit 0.  61 suites, 1081 passed, 0 FAILED, 1 ignored.
                                     Of those, 28 are the new `tests/holform.rs`.
./instrumente/pruefe-emission.sh  -> exit 0.
    == EMISSION: ALL PASS -- 37 durchgestochen, 266 von 266 uebersetzen,
       2 umgekehrte Probe(n) ==
    (114 beispiele/, 18 beispiele/gift/, 132 messung/*/,
      2 messungen/, 1 programmlogik/, 1 laufzeit/, 0 sonst -- SIEBEN Marken)
    ASan (stage 6b): 36 units under -fsanitize=address,undefined, no finding.
```

*Baseline of the same guardian: `EXIT=1`, cut off in stage 9 — see §4a.* So the pair
is `red before, ALL PASS after`, and the difference is one booked root plus one booked
corpus file, each with its date and reason.

**One caveat on the population, stated because it is the measuring apparatus.** The
server tree is synced without `.git`, so `git ls-files` fails and stage 9 falls back to
its directory blacklist — it says so out loud (*"falling back to the directory
blacklist alone, untracked .gab files included"*). The first run of this lane therefore
counted `probe/p3.gab` and `probe/p4.gab` as new emitting roots; they were moved out of
the tree (`~/fadd-proben/`) and every number quoted above and in §4a is from a tree
with no scratch `.gab` in it. On a real checkout, where `git ls-files` works, the
tracked population and this fallback population are the same set. *A guardian that
names its own fallback is the good case; the bad one would have counted two scratch
files into a mark.*

**`cargo test` needed the Lean caches seeded, and that is worth writing down.**
`AGENTS.md` §6 names `cp -a ~/gabbro-muse/stage/lake3 …/grammatik/.lake`, and
`grammatik/` is not the directory `gabbro prove` builds — **`programmlogik/` is**, and
it has no staged cache. Without it, `cargo test` reaches
`erstnamen.rs::jeder_erstname_tut_dasselbe_wie_sein_zweitname` (which runs every
subcommand under both names, `prove` included) and starts a fresh
`git clone https://github.com/leanprover-community/mathlib4`, then a mathlib build
from source. Measured 2026-09-15: **two Opus trees stalled there at once**, one for
19 minutes and one for 13, both at ~430 MB of a clone, with no test output in
between. Seeding from an idle finished tree
(`cp -a ~/gabbro-opus-tv/programmlogik/.lake …`, 7.5 GB) turned the same run into
minutes. *An instruction that names one of two cache directories reads like it names
both.*

Standing, environmental, and NOT caused by this lane: `gabbro prove` then reports
`RED  Duty16ByOpsAmFeld … Body.olean, incompatible header`, while
`lake build Gabbro.Body` in the same directory says `Build completed successfully`.
Both spellings of the subcommand report it identically, which is why the test is
green — it compares two spellings, not the verdict. Worth a look by whoever owns
`prove`; it is not this arm.

**Guardians run beside the two above** (local, from a clean tree, before AND after —
each number identical on both sides, so this lane moved none of them):

| guardian | before | after |
|---|---|---|
| `pruefe-kennungen.py` | ALL PASS (411 codes) | ALL PASS (411 codes) |
| `pruefe-ctext.py` | 2 of 2 pins byte-identical | 2 of 2 pins byte-identical |
| `pruefe-englisch.py` | 3 ratchets broken, 7958 German comment lines, 30 feeders, 5 sinks | **the same 3, the same 7958 / 30 / 5** — over 266 MORE comment lines, of which zero are German |
| `pruefe-zahlen.py` | **27** findings | **27** findings |
| `pruefe-todo.py` | 14 findings | 14 findings (none names this lane's files) |

*The broken ratchets and the 27 are inherited from master and were measured at HEAD
with the lane's diff stashed — the point of the column is that the pair is equal, not
that either is green.* `pruefe-exportlean.py` / `pruefe-genlean.py` have nothing new
to look at (no Lean written, no generated file touched) and both abort on the
timestamp rule against a locally fetched binary, which is the measuring apparatus and
not a finding (CLAUDE.md: *a tool that measures the time instead of the content errs
in both directions*).

---

## 8. What was NOT measured

- **Nothing was run.** The fetch instructions were compiled (`cc -std=c11 -Wall
  -Wextra -Werror` at `-O0` **and** `-O2`, gcc on x86_64) and never executed under
  contention. Wait-freedom is a property of the instruction C11 names, not something
  this lane observed.
- **No disassembly, and the word "wait-free" is therefore NOT claimed.** C11 makes
  `atomic_fetch_*` one read-modify-write operation on the abstract machine, so the
  emitted C has no loop and no bound — that is the whole claim. What the TARGET makes
  of it is the target's business: on x86_64 `add` is `lock xadd`, while `or`/`and`/`xor`
  **with a used old value** have no single instruction and become a `cmpxchg` loop in
  the code generator. *The three arms this lane built are exactly the three where that
  is true.* The first draft of the emitted comment said "ONE wait-free instruction";
  it now says "ONE C11 read-modify-write", and names the machine question in the same
  breath. Worth one lane with `objdump`.
- **No Lean.** The correspondence between `atomic_fetch_or_explicit` and the model's
  RMW step is not proved; `CFormen*.lean`/`CSemantik.lean` do not yet carry a fetch
  form. §3's table is read off two texts, as lane 201's was.
- **No `-O1`, no second compiler, no other architecture.**
- **The `acq_rel` join is derived, not validated against the model.** It is the join
  of the two halves the emitter's own map names; that this is what `A10`
  (`release_stellt_sichtbarkeit_her`) wants of an RMW is an argument in §1, not a
  theorem.
- **The mutation catalogue was not extended.** `mutiere-pruefer.py` has no anchor for
  the new arm; a mutation that turns `atomic_fetch_or_explicit` into
  `atomic_fetch_and_explicit` would be caught by `tests/holform.rs`, and one that
  deletes the arm entirely would be caught by four of its rows — but that is an
  argument, and the catalogue is a measurement.
