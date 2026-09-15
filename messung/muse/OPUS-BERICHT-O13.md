# O13 — the 72 GB, measured apart and repaired

*Opus lane `o13`, 2026-09-15. Everything below was measured on `ki-pc-fisch-101`
(110 GB, 16 cores, Lean 4.33.1, `~/.elan`), each run under
`/usr/bin/time -f "WANDUHR %e s SPEICHER %M kB"` and under a hard `ulimit -v` so a
runaway probe could not disturb the other lanes. **No number here is an estimate.**
A bare `lean` on an empty file costs 2,3 s and 477 MB on this machine; that is the
BASELINE every "net" column below is measured against.*

---

## 1. The two pathologies, reproduced and quantified

### 1a. `String.toList` — CONFIRMED, and worse than linear

The handed-over claim was: forcing the first character of one 1419-byte string literal
costs 33,7 GB and 217 s. Re-measured on a quiet machine with a synthetic ASCII text
(`theorem : (s.toList).isEmpty = false := rfl`, i.e. **whnf only — one character**):

| literal size | wall clock | peak resident | net over baseline |
|---|---|---|---|
| 50 B | 2,4 s | 0,51 GB | 0,04 GB |
| 100 B | 3,1 s | 0,62 GB | 0,15 GB |
| 200 B | 4,5 s | 0,92 GB | 0,45 GB |
| 400 B | 10,8 s | 2,05 GB | 1,58 GB |
| 800 B | 31,0 s | 6,19 GB | 5,72 GB |
| **1419 B** | **95,2 s** | **17,80 GB** | **17,33 GB** |

Growth is about **n^1,9** in both time and memory. The direction of the handed-over
finding is right and the mechanism is right; the constant is smaller on an idle machine
(17,8 GB, not 33,7 GB — the original was measured with other lanes' load beside it).
**The claim "one character of a long literal costs what the whole text costs" is
confirmed**: whnf and full force are within a factor of 1,5 of each other.

Forcing the WHOLE literal (`theorem : s.length = n := rfl`):

| literal size | wall clock | peak resident |
|---|---|---|
| 400 B | 13,7 s | 2,70 GB |
| 800 B | 48,2 s | 8,87 GB |

**Why.** In Lean 4.33 `String` is a UTF-8 byte array:
`String.toList s = (String.Internal.toArray s).toList` and
`String.Internal.toArray b = b.toByteArray.utf8Decode?.get _`. The `.get` forces the
`Option` to `some`, so the kernel must decode **every** byte before it can hand out the
first character — and `String.length` is a second pass over the same bytes. `lex s =
scan s.toList (s.length + 1)` pays it twice.

### 1b. The same text as a `List Char` of short `"…".toList` pieces

`theorem : quelle.length = n := rfl` — **fully forced**, the harder question:

| text | piece size | pieces | wall clock | peak resident |
|---|---|---|---|---|
| 400 B | 25 B | 16 | 3,9 s | 0,70 GB |
| 400 B | 50 B | 8 | 4,5 s | 0,82 GB |
| 800 B | 25 B | 32 | 5,5 s | 0,95 GB |
| 800 B | 50 B | 16 | 6,5 s | 1,16 GB |
| **1419 B** | **25 B** | **57** | **8,5 s** | **1,46 GB** |
| 1419 B | 50 B | 29 | 9,7 s | 1,74 GB |

Cost is **linear in the number of pieces** and about **k^1,55 in the piece length**, so
short pieces win. At 1419 bytes: **12× less memory and 11× less time than the single
literal, while doing strictly more work** (full force against whnf).

### 1c. The bridge is free

```lean
def src : String := String.ofList quelle
theorem d1 : src.toList = quelle := String.toList_ofList
theorem d2 : src.length = quelle.length := String.length_ofList
```

| | wall clock | peak resident |
|---|---|---|
| the two bridge theorems over a 1419-byte pin | **2,4 s** | **0,476 GB** |

That is the bare-`lean` baseline to three digits: **zero measurable cost.** Both are
core lemmas proved by `simp`, so the decoder is never run. This is what makes the repair
a repair and not a weakening — see §2.

### 1d. The fuel / `Nat.brecOn` pathology — **NOT reproduced**

O13 (and the design note in `CParser/CParse.lean` §4) says: *"a MUTUAL recursion through
a fuel argument compiles to a mutual `Nat.brecOn`, and reducing it is EXPONENTIAL in the
fuel"*. **That general claim is refuted.** Probes, each `rfl` on a closed term, fuel
really traversed:

| shape (peak resident) | fuel 10 | 20 | 30 | 40 | 60 | 80 | 100 | 200 | 320 |
|---|---|---|---|---|---|---|---|---|---|
| single recursion on `Nat`, fuel traversed | — | 0,477 | — | — | — | — | 0,477 | — | — |
| **two-way mutual**, fuel traversed | 0,477 | 0,477 | 0,477 | 0,477 | 0,479 | — | 0,479 | 0,480 | — |
| **two-way mutual**, fuel + list | — | 0,479 | — | 0,479 | — | 0,477 | — | — | 0,480 |
| **three-way mutual**, fuel + list | — | 0,473 | — | 0,478 | — | — | — | — | 0,478 |

All figures in GB. Every one of them is the bare baseline — **flat, not exponential**,
and wall clock stays at 2,3–3,8 s throughout, with no trend. The counter-evidence
inside this tree is stronger still: the
**Gabbro** statement and item parsers (`Parser/Anweisung.lean` lines 119 and 345,
`Parser/Element.lean` 65 and 140, `Parser/ElementTief.lean` eight blocks) are exactly
that shape — mutual blocks whose first argument is fuel — and `parseTopTief` runs them
at fuel `toks.length * 8 + 32` = **2032** for `tt104`. Kernel-reducing that is measured
below at well under a gigabyte.

**So the 112 GB the A2 lane saw had another cause**, and the sentence should not be
carried forward as a law about mutual recursion. What is left standing is the *design*
of `CParser/CParse.lean` §4 (expressions parsed without recursion) — that is fine, it
just is not justified by the reason written next to it. §5 says what to do about the
note.
