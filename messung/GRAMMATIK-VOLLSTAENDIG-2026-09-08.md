# Completing the grammar for "a person proves only their own logic" — 2026-09-08

**Base:** `master` at `ec71432`, binary `target/debug/gabbro` of 15:33. Every measurement
below was **re-run today**; none is carried over from
[`OFFEN-PRUEFER-UND-GRAMMATIK-2026-09-07.md`](OFFEN-PRUEFER-UND-GRAMMATIK-2026-09-07.md),
though four rows confirm it.

**Corpus** wherever the word appears: `git ls-files 'beispiele/*.gab' | grep -v '/gift/'` — **70 files**.

---

## 0. What "complete" is going to mean, so that it can be checked

`Claude outputs/PLAN.md` states the goal as a sentence about the *person*: everything that is
not their own logic is carried, named as an assumption, or refused with a tag. That sentence
has a **grammar-side precondition nobody has written down**, and this file writes it:

> **A language surface is complete for "only own logic" when, for every form the grammar
> admits:**
> 1. **it means something** — the checker either objects to the form or the form has an
>    effect on what the checker concludes and on what the emitter writes;
> 2. **the proof channel answers for it** — the obligation it creates is carried, assumed by
>    name, or refused with a tag;
> 3. **it cannot silently disappear** — no edit that leaves the checker green may remove an
>    obligation without saying so.

Point 2 is the one `PLAN.md` has been working on for twenty-five runs, and it stands at
**11 refused forms, all tagged**. Points 1 and 3 have never been measured as a class.

> **The grammar is complete at the level of WORDS and open at the level of MEANING.**
> `zaehle-wortschatz.py` counts 221 terminals, 17 reserved and 204 contextual;
> `pruefe-grammatiktafel.py` reports `UNGEDECKT = 0`; every EBNF terminal is implemented and
> every parser-decided word is in the EBNF. **And a form can pass all of that and mean
> nothing.** Four do, measured below.

---

## 1. Forms that MEAN NOTHING — point 1, four measured today

### 1.1 The quantifier domain is decoration — and this is the worst of the four

```bash
sed 's/in slots of Topologie/in threads/' beispiele/18-vorfahren.gab > /tmp/dom-c.gab
./target/debug/gabbro pruefe beispiele/18-vorfahren.gab   # 5 items, 0 errors, 0 hints
./target/debug/gabbro pruefe /tmp/dom-c.gab              # 5 items, 0 errors, 0 hints
./target/debug/gabbro emit  … | md5sum                   # 4220717dff74105e8d12af740e7c7d3c -- BOTH
```

The invariant reads `forall g in slots of Topologie : Topologie.slots[g].bereich <= 255`.
Rewritten to `forall g in threads : …` it **quantifies over threads and indexes slots**, and
the checker says nothing, and the C is byte-identical.

**Why it belongs at the head of this list.** `PLAN.md` §5.2 books nine refused forms under
`quantified-*`, and a refusal is an honest answer. This is not a refusal: it is the *other*
nine domains, the ones that are NOT refused, having no effect either. A person writing an
invariant over the wrong domain is told nothing by the checker and nothing by the proof
channel — the channel translates the body, and the domain that was supposed to bound the
binder never reaches it.

### 1.2 A fractional bound on an integer type

```bash
printf 'module p::r {\ntype T = u32 in 0.5 .. 1.5;\n}\n' > /tmp/float.gab
./target/debug/gabbro pruefe /tmp/float.gab   # 2 items, 0 errors, 0 hints
```

`Shape.intIn lo hi` is the model's carrier for exactly this declaration (`PLAN.md` §3.1). A
range whose ends are not integers produces a shape whose meaning nobody has stated.

### 1.3 `divergent … -> never` that returns

```bash
printf 'module p::d {\ndivergent fn q() -> never\n effects { pure }\n{\n return;\n}\n}\n' > /tmp/never.gab
./target/debug/gabbro pruefe /tmp/never.gab   # 2 items, 0 errors, 1 hints
```

The hint is not about the `return`. `PLAN.md` writes `False` into the `_post` of a `-> never`
routine — so a body that returns makes the unit's duty *unprovable*, and the person is handed
a goal that is false because of a form the checker admitted.

### 1.4 An obligation vanishes on a rename — point 3, and it is silent

```bash
./target/debug/gabbro pflichten beispiele/01-tabelle.gab            # == 15 obligations
sed 's/maintains baum_wohlgeformt/maintains baum_bleibt_baum/' …    # rename the maintains
./target/debug/gabbro pflichten /tmp/mt.gab                         # == 14 obligations
./target/debug/gabbro pruefe  /tmp/mt.gab                           # 18 items, 0 errors, 0 hints
```

`pflichten.rs` matches a `maintains` against an invariant by **name text**. A typo in a
`maintains` removes an obligation and reports nothing; the same statement is then booked as
owed *and* as unowned. This is point 3 of §0, and the only measured instance of it so far.

---

## 2. The named grammar lines that are still missing

Not defects — decisions already taken whose surface was never written. Each is booked with
the source that names it.

| | what is missing | cost, as its own source states it | source |
|---|---|---|---|
| 2.1 | **`by consuming` names no point in time** | *"would need **a grammar line**"* | `gabbro schablonen --gate`, premise `consuming.leermenge` |
| 2.2 | a **single-path descent** over `mappings of` (the cost promise `levels × node length` has no name) | *"kostet ein Terminal"* | `TODO.md` Stufe 3 |
| 2.3 | **`threads` as a quantifier domain** | *"a language change, not a model change"* | `PLAN.md` §9.1 |
| 2.4 | **the traversal binder has no TYPE** in `slots of`, `descendants of`, `ancestors of`, `elems of` — so `p[i]` in the loop is not provably in range | *"eine Änderung und nicht vier"* | `TODO.md` Stufe 3 |
| 2.5 | **`group ops` / `by ops`** | heading reads *"the design, BEFORE the first grammar line"* | `TODO.md` Stufe 5 |

**2.4 is the one that costs the person proof work today** and the only one of the five that
`PLAN.md`'s corpus can already feel: a binder without a range is a witness the channel cannot
produce, and the person supplies it by hand.

---

## 3. What is measured and NOT in this file's scope

* **`gabbro pflichten --isabelle` over the corpus: `total 84  goals 1  refused 83`** (re-run
  today). The Isabelle channel is not the Lean channel of `PLAN.md`, and its 83 refusals are
  a different census with different classes. Named here so the two `84`/`173` figures are not
  read as one number.
* **`gabbro schablonen --gate`: 6 premises of PROVED templates have no pass** — a proof
  nothing establishes. Ratchet tooth 3. Two of the six are 2.1 above; the rest are Stufe 5.
* **The 11 refused forms of the Lean channel** — they are point 2 of §0 and they are answered.
  A refusal with a tag is a complete answer, not a gap.

---

## 4. The order, and why it is this one

1. **§1.1** — nine domains that decorate. It is the only one of the four whose blast radius is
   the whole invariant language, and the only one where the checker's silence and the proof
   channel's silence are the *same* silence.
2. **§1.4** — an obligation that disappears on a typo. Cheap to close, and it is the sole
   measured instance of point 3; a class with one instance and no guard is a class that grows.
3. **§1.2, §1.3** — two admitted forms with no meaning. Small, and each is one objection.
4. **§2.4** — the binder without a type: the only missing grammar line that the corpus already
   pays for.
5. **§2.1, §2.2, §2.3, §2.5** — grammar lines for decisions already taken, in the order their
   stages give them.

**What this file does not claim.** That the list is closed. Every entry here was found by
deriving the grammar from `parse.rs` and probing forms, not from the corpus — and the census
of 2026-09-07 says why that matters: *"Trap 80 does not only make a corpus flattering, it
makes it BLIND in a specific direction — toward every shape nobody thought to write."* A form
nobody has probed is not a form that means something.
