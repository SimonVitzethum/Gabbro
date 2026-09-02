# GabbroV V0 and V1 — are the 66 logic obligations sayable in the Lean fragment?

*Measured 2026-09-02 from tree `371dec6`. `dokumente/GABBROV.md` §10 puts V1 before
everything else, because it is the one stage that can fail before a line of code exists.
This file carries the answer and the way to it. Every count below names the command that
produced it.*

## The answer, up front

*PENDING — this heading is written before the count exists and stays empty until §3 is
walked. A file that carries its conclusion above its measurement invites the conclusion to
be written first; that happened once in this very file and was struck within the minute.*

---

## 1. What was fed in, and by which command

The population is the `L` column of `dokumente/PFLICHTEN.md` — the same rows the tree's own
counter counts, read with the tree's own row parser (`_zellen`, unescaped pipes only, third
column after markup is stripped).

```
./instrumente/zaehle-pflichten.py --spalten
```

| | |
|---|---:|
| obligations in total | 239 |
| plumbing (K) | 173 |
| **logic (L)** | **66** |
| of the 66, anchored at a `FRAGMENTE.md` line | 66 |
| of the 66, from the lowering rows | 0 |

**The lowering rows carry no `L`.** All ten are `K`, so the denominator of this run is
exactly the anchored rows, and `66` needs no adjustment.

---

## 2. Finding: the guard reach of a new `dokumente/*.md` is ONE loud number

*This is step A of the mandate, measured rather than assumed.*

`CLAUDE.md` records that seven guards read German document text and that **four go silently
blind** when it moves (`pruefe-todo.py`, `-zahlen.py`, `-grammatiktafel.py`,
`-widerruf.py`). Held against a **new** file in `dokumente/`, that list collapses:

| guard | reads `dokumente/GABBROV.md`? | why |
|---|---|---|
| `pruefe-todo.py` | no | reads `TODO.md`, `README.md`, `dokumente/PLAN.md` by name |
| `pruefe-grammatiktafel.py` | no | reads `dokumente/SYNTAX.md` only (`:148`) |
| `pruefe-zahlen.py` | **yes** — `rglob("*.md")` (`:1455`) | and it went **RED**, see below |
| `pruefe-widerruf.py` | **yes** — `glob("dokumente/*.md")` (`:243`) | already bilingual |

**`pruefe-zahlen.py` is loud, not blind, and it caught the right thing:**

```
BEFUND  TODO.md: „Dateien, die der Widerrufwaechter liest" steht als 179, der Lauf sagt 180
```

Adding one file to `dokumente/` moves `pruefe-widerruf.py`'s file count, and `TODO.md`
carries that count as a guarded number. *The guard for the document I was about to add was
a number about a different guard's reach* — exit 0 → 1 purely from the file's presence,
measured by adding and removing it and diffing the two runs.

**And `pruefe-widerruf.py` needs no work: it is already bilingual, and that is measured.**

```
== Sprechprobe (R14) ==
  eingesetzter Satz faellt:      ja, 24 von 24 Proben (je Eintrag deutsch UND englisch)
```

Twelve entries, both languages each, and every probe falls. Driven separately against the
German `GABBROV.md` text: **0 of 12 patterns fire on it.** So there is nothing this
translation can take away from that guard — the "pattern grasps into thin air" hazard has
no instance here, and that is a measurement and not a hope.

> **The order in the mandate was still the right one.** The reason it cost nothing this
> time is that the tree already paid it: `pruefe-widerruf.py`'s head records that `probe`
> and the second language became mandatory on 2026-09-01, *because* its green is
> indistinguishable from a miss. **A guard that cannot go red when its pattern dies has to
> carry the proof instead of inferring it** — and this run is what that purchase looks like
> from the outside.
