# The plumbing census — 2026-09-07

**Base:** `master` at `241d20d` (*212 reserved words become 17*). Server directory
`gabbro-klempner`. **Question:** of everything the checker demands from a program that is
already CORRECT, how much could a mechanical procedure have discharged?

**Denominator, stated once and used throughout:** the **70 tracked clean examples**

```bash
git ls-files 'beispiele/*.gab' | grep -v '/gift/' | wc -l     # 70
```

Every number below carries the command that produced it. Where an instrument measures
something other than its object, that is said at the number and not in a footnote.

---

## 0. The three registers, and the test for each — stated BEFORE the sort

| | test |
|---|---|
| **P — plumbing** | there is a **deterministic procedure, no search and no user input**, that derives the missing fact from declarations already in the file. If the procedure can be named and it terminates, the site is `P`. The user is doing the compiler's work. |
| **L — the user's own logic** | the fact is **not determined** by what is written: two programs the compiler cannot tell apart differ in whether it holds. The demand is right and it stays. |
| **R — a rule or a design decision** | the language declines **on purpose**, and the decision is written down. This is not a demand on the user at all — the gap *is* the answer. |

*A fourth thing turned up that fits none of the three, and it is named as such rather than
forced into one: a site where the checker has no obligation to raise, but where its own
count books one anyway.* That is a defect in the instrument, and it is the largest single
class in the census.

---

## 1. The unperturbed run — the corpus is silent, and that is the problem

```bash
for f in $(git ls-files 'beispiele/*.gab' | grep -v '/gift/'); do
  ./target/release/gabbro pruefe "$f"; done
```

**70 of 70 files: `0 errors, 0 hints`, exit 0.** No diagnostic fires on a correct program —
so "what the checker demands" cannot be read off a run. It has to be measured against a
perturbation, or read off the two places where the checker itself admits it fell short.
Those two places are the coverage figures it prints beside every result.

```
M1 saw 1278 expressions, 84 of them without a type   (93.43 % coverage)   -- 67 of 70 files
gabbro kosten: 179 bodies computed, 9 open           (95.21 %)            -- 188 bodies
```

*Three of the seventy files print `M1 saw no expression` — they have no function body. The
coverage denominator is 67 files, not 70.* (W25: the number proves its denominator, not its
label.)

---

## 2. `gabbro kosten` — 9 open, and all nine are the SAME sentence

```bash
for f in $(git ls-files 'beispiele/*.gab' | grep -v '/gift/'); do
  ./target/release/gabbro kosten "$f"; done | grep OFFEN | sort | uniq -c
```

```
      9 OFFEN  --  -- a `forever` loop has no total cost -- its promise is `per_pass`, not `costs`
```

**All 9 are `R`, and the register is closed.** A `forever` loop has no total cost; saying so
is the answer, not a gap. **0 of 9 are plumbing.** The 95.21 % is therefore not 4.79 % short
of anything — it is at its ceiling, and the ceiling is 95.21 % by construction.

*This is the one register in the census with nothing left in it.*

---

## 3. The 84 untyped expressions — named, not counted

The checker counts what it cannot type but does not say where. It does now, under a probe
that **retracts in lockstep with the counter** — the first version printed **86** against
the counter's 84, because `nan_moeglich` walks a condition a second time and un-counts it
afterwards (`m1.rs:2744-2747`). *An instrument that counts a speculative walk the object
throws away is measuring the checker's second look.* With the retraction wired in, probe and
counter agree at **84**, and only then is the list the 84.

| n | % | class | register |
|---:|---:|---|---|
| **33** | 39.3 | **a call to something that returns nothing** | **not a gap — see §4** |
| **24** | 28.6 | **the `traverse` binder** | **P** |
| **19** | 22.6 | bare `None` | **P** |
| 3 | 3.6 | `Some(x)` | **P** |
| 3 | 3.6 | `lenof(m)` inside a cost bound | **P** |
| 1 | 1.2 | a `match` pattern binder (`Kette(i)`) | **P** |
| 1 | 1.2 | a mixed-width addition `u64 + u16` | see §6 |
| **84** | | | |

**50 of 84 (59.5 %) are `P`. 0 are `L`.** Not one of the eighty-four is a place where the
user knows something the compiler cannot.

---

## 4. The largest class is not a gap at all — `Typ::Unbekannt` names two states

**33 of the 84 are calls, and every one of the 33 calls something declared with no `->`.**

```
extern fn speicher_freigeben(p : Pa) effects { writes halde } costs <= 64 ops;
transition wurzel_setzen { GCMD.SRTP: 0 -> 1 }
pub senden: fn(u8)
Verzeichnis::insert(v, i)                    -- a generated `ops` word
```

`ruf_roh` ends at `sig.ergebnis.clone().unwrap_or(Typ::Unbekannt)` (`m1.rs:2343`), and
`buche` books `Unbekannt` as *"without a type"*. **A void call has no type because there is
nothing to type.** It is not a coverage hole, and no procedure can close it.

**And the conflation is not only a counting error.** `m1.rs:2241` states the other half in
its own words — *"`Unbekannt` is compatible with everything"*. Measured:

```gabbro
extern fn tue(x : u8) effects { writes halde } costs <= 4 ops;   -- returns NOTHING
let x = tue(k);
return x + 4294967295;   -- 0 errors
tue(tue(k));             -- 0 errors -- a void call where `u8` is demanded
T.slots[i].a             -- 0 errors -- `i` from a void call, no M103
if q { … }               -- 0 errors -- `q` from a void call
```

`gabbro pruefe`: **0 errors.** Four rules step aside at once.

> **The emitter holds where the checker does not.** `gabbro emit` on the same file:
> `C001: no lowering: 'let' without a resolvable type`, exit 1. *The class is real; the
> exposure is bounded by a net one stage later.*

**Register: this is a defect in the instrument, and the number that suffers is the
denominator.** 33 of the 84 were never obligations.

---

## 5. The largest genuine `P` — the `traverse` binder, 24 sites, and it is a live hole

`m1.rs:1295-1297`, one line:

```rust
Schleife::Traverse(t) => {
    innen.lokal.insert(t.variable.text.clone(), Typ::Unbekannt);
```

**The binder of every traversal is bound to `Unbekannt` on purpose.** It is `P` by the test
in §0, and the procedure is not merely nameable — **it is already written and already
trusted**: `domaene::Sicht::tabellenname` resolves `slots of` / `descendants of` /
`ancestors of` to a table, `Umgebung::kapazitaeten` holds its `count N`, and
`umgebung.rs:1347-1362` already turns exactly that pair into the type `index into T`
(`u32 in 0 ..< N`). *The user who writes `index into T` on a parameter gets the range; the
binder that provably has the same range gets nothing.*

**And the silence is not free.** On a `table Q count 8`:

```gabbro
traverse i over slots of w by unvisited touches writes w.slots {
    w.slots[i + 1000000].aktiv = true;
}
```

```bash
./target/release/gabbro pruefe probe/binder.gab   # 6 items, 0 errors, 0 hints
./target/release/gabbro emit  probe/binder.gab    # exit 0
```

```c
Q_slot slots[8];
for (uint32_t i = 0; i < (uint32_t)(sizeof(w->slots)/sizeof(w->slots[0])); i++) {
    w->slots[i + 1000000].aktiv = true;
```

**Both nets pass it, and the C is written.** An index a million past the end of an
eight-element array, through `pruefe` and through `emit`. `M103` — the folder's showcase
rule — steps aside inside every traversal body, and the tree's own note at
`m1.rs::name_aufloesen` predicted the shape: *"an unknown name has no type, and every range
rule silently steps aside where the type is missing — including the index bound."*

*The same untyped binder also lets `return i;` satisfy `-> u32 in 0 .. 10`.*

> **This is the one place where carrying plumbing and closing a hole are the same change.**
> Typing the binder removes 24 sites from the user's side of the ledger **and** makes the
> checker demand more, not less.

---

## 6. The rest of the `P` register, and the one site that is neither

**`None` (19) and `Some(x)` (3) — 22 sites, `P`.** Every one stands where the expected type
is written down one line away: a `return` in a function with a declared result, or an
assignment to a declared slot. Propagating the expected type into a tagged literal is
mechanical and one-directional.

**`lenof(m)` in a cost bound (3) — `P`.** `forever pruefer per_pass bounded 64 + 12 *
lenof(m) ops`. The three sites are one expression and its two sub-expressions.

**A mixed-width addition (1) — neither `P` nor `L`, and it is a fourth silent acquittal.**

```gabbro
let addr = a + o * f;      -- u64, ranges carried correctly
return addr + w;           -- u64 + u16  ->  Unbekannt, and NO diagnostic
```

An un-annotated `let` carries its initializer's range correctly (probed: `let s = x + y;`
over two `u32 in 0 .. 100` gives **100 % coverage, 0 errors**). The loss is at the mixed
width alone. *One site, and the rule that should have spoken said nothing.*

---

## 7. The differential — what the corpus would owe if the ceremony were struck out

The unperturbed run is silent, so each ceremony class was removed from all 70 files and the
corpus re-checked. **No `set -e`, no first-hit stop: every file runs, every code is counted.**

```bash
python3 differential.py {narrow|ranges|effects|costs}
```

| removed | sites | what the checker then says |
|---|---:|---|
| `narrow … else` | 17 | `M101` 6, `M108` 3, `M103` 1, `M104` 1, `F001` 1 — **12 total** |
| declared integer ranges | 81 | `M103` 15, `M104` 10, `M101` 5, `M119` 4, `E009` 3, `D021` 1, `E005` 1 — **39**, plus 4 `P001` |
| `effects { … }` | 315 | `E001` **265**, `M111` 22, `A002` 7, `M114` 6, `V003` 6 … — **327**, plus 19 `P001` |
| `costs <= N ops` | 238 | `A003` **7**, `E009` 3, `N035` 2 — **12 total** |

**Two readings, and the instrument's own limits are on the same line as its numbers.**

*First, the `ranges` column is a dependency census and NOT a plumbing census.* Strike the
declared range off a counter and the counter genuinely can overflow — `M104` is then
**right**, and the site is `L`. The 39 diagnostics measure how much of the corpus rests on
written ranges, not how much of it the compiler could have proved. **The anchor case says the
same thing:** `let mut b = a; b += 1;` on a full-range `u32` is refused by `M104`, and it is
refused correctly — `b` can be `u32::MAX`. Where the range IS declared and a check narrows
it, `V1` already carries it:

```gabbro
let mut b = x;  if b < 100 { b += 1; }    -- u32 in 0 .. 100:  0 errors, already
```

*So `x += 1` is not the largest plumbing category. It was the right place to look and the
wrong place to dig* — the brief said to verify rather than assume, and the verification came
back negative.

*Second, `costs` is not a demand.* Removing all **238** `costs` clauses from the corpus
produces **12** diagnostics, **7** of them `A003` on `asm` bodies, which are a different rule.
`beispiele/01-tabelle.gab` with all four `costs` clauses struck out checks `0 errors`.

> **W7 — two registers over one thing.** `messung/K3-AUSWAHL.md` §5 states *"`effects` and
> `costs` are added at every function, because the language refuses a function without
> them."* **Half of that is measured false.** The language refuses without `effects`
> (265 sites); it does not refuse without `costs` (12 sites, 7 of them `asm`-only). The
> reconciliation belongs at that sentence, and it is left un-made here on purpose — `K3-AUSWAHL.md`
> is frozen.

*Contamination is named, not hidden:* the `ranges` stripper ate the `=` of four `type X = T
in a .. b` declarations (4 `P001`), and the `effects` stripper hits four positions where the
grammar **requires** the word (19 `P001`, all `progress`/`falsifier`). Those files' other
diagnostics are suspect and are not load-bearing for either reading above.

---

## 8. The poison corpus — the baseline, before anything moves

```bash
for f in $(git ls-files 'beispiele/gift/*.gab'); do ./target/release/gabbro pruefe "$f"; done
```

**454 files. 414 refused by the checker (exit 1). 40 exit 0** — and all 40 are correct:

| | |
|---:|---|
| **38** | refused by the **emitter**, `C001`, exit 1 |
| **1** | `286-maintains-ohne-schreiben.gab` — its header says `erwartet: Hinweis M114`. A **hint** does not set exit 1 |
| **1** | `414-tabellenspeicher-heisst-so.gab` — its header says `erwartet: cc`. Caught by the C compiler by design |

**Every one of the 454 is refused by the tool its own header names.** *A poison scorer that
reads only `gabbro pruefe`'s exit code reports 40 escapes and is wrong 40 times out of 40* —
`gabbro pruefe` and `gabbro emit` are different answers, and 38 of these are the difference.

---

## 9. What the census settles

1. **The `kosten` register is closed.** 9 of 9 open bodies are `R`. Nothing to carry.
2. **The range demand is NOT the largest plumbing category**, and the anchor case `x += 1`
   is `L`, not `P`. Verified against the brief's own instruction to verify.
3. **39.3 % of the coverage gap is not a gap** — `Typ::Unbekannt` books "there is no type"
   and "I could not find the type" in one slot.
4. **The largest genuine `P` is the `traverse` binder, 24 sites**, and its procedure is
   already written elsewhere in the same crate.
5. **Four silent acquittals were found while counting**, all one cause: `Unbekannt` is
   compatible with everything. One of them writes an out-of-bounds C array access through
   both nets.
6. **`L` is empty.** Over 84 sites, not one is a fact the user knows and the compiler cannot.

---

## 10. What was measured and what was not

| ran | result |
|---|---|
| `gabbro pruefe` × 70 clean | 0 errors, 1278 expr / 84 untyped, 93.43 % |
| `gabbro kosten` × 70 clean | 179 computed / 9 open, 95.21 % |
| `gabbro pruefe` × 454 poison | 414 exit 1 |
| `gabbro emit` × 40 checker-clean poison | 38 `C001`, 2 correct by their own header |
| `cargo test --no-fail-fast` (server) | **411 passed, 0 failed**, 31 result lines |
| `instrumente/mutiere-pruefer.py --anker` (server) | **395 of 395 anchors bite**, ALL PASS |
| `instrumente/pruefe-emission.sh` (server) | ALL PASS — 29 pierced, 145 of 145 compile |
| the differential, 4 variants × 70 files | §7 |

**NOT run, and each would answer something this document does not:**

| not run | what it would have said |
|---|---|
| `mutiere-pruefer.py` **full** (~13 min, ~395 mutations) | whether the test suite kills a mutation of the code touched here. Only the **anchor** half ran — it is text counting and proves the catalogue is wired, not that the suite bites |
| `instrumente/pruefe-beweise.sh` / `isabelle build` | nothing in the census touches `beweise/`; both rsyncs were done so the run is available |
| `instrumente/abnahme.py --voll` | the full acceptance. Deferred until after the change, where its verdict means something |
| the second corpus («K2»/«K3» fragments) | plumbing coverage on code this folder did not write. **Deliberately out of scope** — the question is `K100`, not portability |
| `instrumente/zaehle-bereichspflichten.py` | the tree's own `narrow` count over `dokumente/FRAGMENTE.md`. The differential in §7 is over `beispiele/` and is **a different denominator** — the two are not comparable and were not compared (W25) |

> **A number in this document that names no command is a mistake.** So is a number whose
> denominator is not on the same line.

### A mark that moved, and it moved because the object grew

`CLAUDE.md` says the mutation catalogue stands at **388**. It stands at **395**
(`mutiere-pruefer.py --anker`, 395 of 395). The catalogue grew; the mark follows the object
and the reason stands here. *`README.md` and `CLAUDE.md` disagreeing about this number is the
`W7` this folder has already paid for once.*

---

# Addendum — the `ops` question, settled: they CANNOT, 50 of 55

*Asked by the coordinator after the census above was written, and it is the question that
sizes the whole job.* `gabbro k-bedingung` over the same 70 files says **43 carriers, K
holds 2, falls 41**, with **55 hand-written write sites over 29 carriers**. `k_haelt()`
(`kbedingung.rs:45-47`) is `hat_ops && handschrift.is_empty() && breaking.is_empty()`, and
all 41 fall at the first conjunct. **Why do 41 carriers declare no `ops`?** Two answers with
completely different price tags: they *could* and don't (uptake, hours), or they *cannot*
(`ops` is too weak, language work).

**Reconciliation first (W7).** All three of the coordinator's figures reproduce exactly on
`a1564f6`, which is *after* this document's own change:

```bash
./target/release/gabbro pflichten    $(git ls-files 'beispiele/*.gab' | grep -v '/gift/')
./target/release/gabbro k-bedingung  $(git ls-files 'beispiele/*.gab' | grep -v '/gift/')
```

```
84 obligations: 1 refinement, 6 preservation, 17 postcondition, 11 foreign,
                18 precondition, 18 device, 3 loop invariant, 10 unowned invariant
43 carriers: K holds 2, falls 41.   55 hand-written sites, 29 carriers.
```

> **The two 84s are not the same 84 and are never to be added.** *This* 84 is `gabbro
> pflichten`'s obligation count. §3's 84 is M1's untyped expressions out of 1278. Different
> instruments, different denominators, and the coincidence is a coincidence.

## A.1 What `ops` can express — read off the generated C, not off the grammar

```bash
./target/release/gabbro emit beispiele/47-ops-wortmenge.gab
```

```c
static void Verzeichnis_insert(Verzeichnis *t, uint32_t n) { t->slots[n].benutzt = 1; }
static void Verzeichnis_remove(Verzeichnis *t, uint32_t s) { t->slots[s].benutzt = 0;
                                                             t->slots[s].marke   = 0; }
```

**Three words, and that is the whole vocabulary** (`opsruf.rs:272-345`): `insert` writes the
occupancy flag and nothing else (plus the parent edge where the table has `tree`); `remove`
writes **every** field to zero; `relabel` writes the parent edge alone. And with `ops`
declared, **any** remaining hand write is `D001`. *So a carrier qualifies only if every one
of its sites maps to one of the three.*

## A.2 The walk — 55 sites, each judged, and every "yes" verified by rewriting it

**My enumeration of the sites is cross-checked against the checker's own count: 55 = 55.**

| | carriers | sites | verdict |
|---|---:|---:|---|
| **CAN be `ops` today** | **3** | **5** | rewritten, `pruefe` 0 errors, `emit` exit 0, `k-bedingung` says `haelt` |
| cannot — **`M140`**, the table is a global | 9 | 12 | the operation takes `ptr<normal, rw> T`, and Gabbro has no address-of |
| cannot — **`D010`**, no `bool` field at all | 5 | 6 | `occupied` demands a `bool`; these tables hold values, not occupancy |
| cannot — **`D001`**, the write is a payload | 12 | 32 | no word writes a payload field |
| | **29** | **55** | |

**The three that CAN, each rewritten and run rather than judged by reading:**

| carrier | cost of the conversion |
|---|---|
| `66-transport-rueckgabe.gab` `Puffer` (3 sites) | one `requires !h.slots[i].belegt`, plus `reads h.slots` |
| `15-own-traegt-beide-rechte.gab` `Region` (1) | one `requires`, and **`costs <= 4` → `<= 5`** — `K001` fired |
| `16-by-ops-am-feld.gab` `Objekte` (1) | one `requires`, `costs <= 2` → `<= 4` |

```
$ ./target/release/gabbro k-bedingung probe/p66.gab
Puffer  ja  0  0  haelt
```

**And the "cannot" verdicts were probed too, not imagined** — the trap named in the request.
The best possible rewrite of `40-werte-und-griffe.gab`, with `insert` doing all it can:

```gabbro
Puffer::insert(p, i);
p.slots[i].lage   = s;      -- error: [D001] `vergeben` writes `Puffer` by hand
```

There is no second call that could replace that line. Likewise `occupied` on a value table:

```gabbro
table Takte count 8 { slot { stand : u32 in 0 .. 3, } ops insert, remove; occupied stand; }
-- error: [D010] `occupied stand` is not a `bool` field of `Takte`'s slot
```

## A.3 The answer, and the one carrier that a single repair would convert

**They CANNOT — 50 of 55 sites (91 %), 26 of 29 carriers.** The uptake half is real and
small: **5 sites, 3 carriers.** `ops` is not under-adopted, it is **under-powered**: it
models exactly one data structure — a slot allocator with a `bool` occupancy flag, reached
through a pointer, whose payload is never written — and 26 of 29 carriers in this corpus are
not that.

> **`50-verfeinerung.gab`'s `Buch` is the sharpest single data point.** Its two write sites
> are `belegt = false; wert = 0;` over a two-field slot — that is `remove`, *exactly*, and it
> has the `bool`. Its only wall is that `Buch` is a **global**, so `Buch::remove(Buch, p)`
> gives `M140: a table does not answer for a pointer`. **One repair — a way to name a global
> table as a carrier — converts this carrier outright**, and it is the only one of the 29
> where a single wall stands alone.

## A.4 And the conversion MOVES an obligation rather than removing one

Every `ops` call charges its caller the premise the theorem discharged: `D012` — *"the
premise comes from `beweise/Table_Ops_Erhaltung.thy` — the generator discharges the
preservation proof ONCE per operation, and this is the half the caller owes in exchange."*
That half lands as a `V` at the **call site**, measured:

```
V  Precondition at the call site (1)
obligation  zwei :: nehmen requires #1  V  …:11  open  !r.slots[i].belegt
```

*It does not show in a file with no callers* — both rewritten examples still report `0
obligations`, because `V`'s anchor is the call and neither has one. **So "K holds" is not
free, and a K-count read without the `V` column beside it reads better than the program is.**

## A.5 The obligation register, sorted as far as it is settled

**29 of 84 are `R` by construction, and the tool says so itself for eleven of them:**

* **`device` 18** — `GCMD.SRTP: 0 -> 1`, `GSTS.RTPS == 1`. These are what the chip does when
  a register is written. The evidence is a datasheet, not the program; no procedure over the
  source discharges them. **`R`.**
* **`foreign` 11** — `ensures` on bodies Gabbro never sees. `gabbro pflichten` prints the
  verdict in its own closing text: *"they are ASSUMPTIONS about foreign code and do not
  dissolve even under 'all of Gabbro verified'."* **`R`.**

**The remaining 55 are NOT sorted here, and that is stated rather than glossed.** The `W`
(unowned invariant, 10) looked like it would be gated on the same `ops` wall as §A.2, and it
is **not established**: `Art::Walkinvariante` covers three constructs (`pflichten.rs:1175`),
not only table invariants, and one sentence of reasoning per obligation is what the tool's
own header demands. *A sort I cannot defend per obligation is worth less than saying it is
not done.*

## A.6 What this addendum did NOT run

| not run | what it would have said |
|---|---|
| `gabbro schablonen` | the 21 templates / 8 `designed`. Deliberately not inherited: `Stand::Entworfen` was flagged as carrying two opposite answers at S11 (`emit.rs:2365` generates `walk`, `:8666` refuses `mappings of`), and a field that means two things is not a measurement I will quote |
| a rewrite of the 26 "cannot" carriers | each would need a language change first; the three walls are named with codes instead |
| `abnahme.py --voll` | the full acceptance over both changes |
| the `V` count after converting all three | `V` needs call sites, and adding them would be a corpus I wrote while looking at it (trap 80) |
