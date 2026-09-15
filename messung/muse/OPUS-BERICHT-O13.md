# O13 — the 72 GB, measured apart and repaired

*Opus lane `o13`, 2026-09-15. Everything below was measured on `ki-pc-fisch-101`
(110 GB, 16 cores, Lean 4.33.1, `~/.elan`), each run under
`/usr/bin/time -f "WANDUHR %e s SPEICHER %M kB"` and under a hard `ulimit -v` so a
runaway probe could not disturb the other lanes. **No number here is an estimate.**
A bare `lean` on an empty file costs 2,3 s and 477 MB on this machine; that is the
BASELINE every "net" column below is measured against.*

---

## 0. Files touched (for the merge)

| File | What changed |
|---|---|
| `grammatik/Grammatik/Parser/Lexer.lean` | **added** `lexL` and `lex_ofList` (+ one CUTS bullet, one `#print axioms`). Nothing existing changed |
| `grammatik/Grammatik/Schlusssatz.lean` | **added** `uebersetzeAllg_von_zeichen` (one theorem, right after `uebersetzeAllg`). Nothing existing changed |
| `grammatik/Grammatik/Parser/UebersetzeAllg2.lean` | `src104real` and `src108` are now `SRC-BEGIN`/`SRC-END` pin blocks + `String.ofList`; `lexL104real`/`lexL108` added; `lex104real`/`lex108` keep their statements |
| `grammatik/Grammatik/Kette104.lean` | `uebersetzt4`: eight tactic lines → one term. **Same statement.** |
| `grammatik/Grammatik/Kette108.lean` | `uebersetzt8`: the same, one line |
| `grammatik/Grammatik/Parser/Uebersetze.lean` | `u104lex`'s inline 669-byte literal → a piecewise pin (`srcZeilen104K`, `srcQuelle104K`) + `u104lexL`; `u104lex` keeps its meaning |
| `grammatik/Grammatik/Schlusssatz104.lean` | `src104 := String.ofList srcQuelle104K`; **added** `uebersetze104_von_zeichen`; `uebersetze104_ok`: six tactic lines → three |
| `grammatik/Grammatik/CParser/CParse.lean` | §4's cost note: the withdrawn `brecOn` law replaced by the withdrawal. **Comment only, no code.** |
| `instrumente/zaehle-kette.py` | `string_def` reads the piecewise pin too (`block_text`), four new speech-test directions |
| `dokumente/OFFEN.md` | O13 closed, with the closing measurement and the withdrawal |
| `dokumente/SATZKARTE.md` | §30 added; §29.6's second pathology withdrawn |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`, `README.md` | the new numbers |

**For the merge:** `Kette104.lean`, `Kette108.lean` and `Parser/Uebersetze.lean` are files
the Muse lanes also hold. In `Kette104`/`Kette108` the diff is **one theorem's proof, with
the statement untouched**. In `Uebersetze.lean` it is **one theorem and the definition
above it**, around line 1709; nothing else in that 2100-line file moved.

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

---

## 2. The repair

**The finding that moved the whole file.** With §1a in hand the obvious repair is "pin
the source as characters", and that is what was done — but it is **not** where the 72 GB
was. Measured by cutting `Kette104.lean` into prefixes and elaborating each:

| `Kette104.lean` up to and including | wall clock | peak resident |
|---|---|---|
| `low_some` (`decide` over the whole generic lowering) | 0,2 s | 0,73 GB |
| `parse4` (`parseTopTief tt104 = .ok items104` by `rfl`) | 1,2 s | 0,98 GB |
| `elab4`, `low4` (elaboration and lowering by `rfl`) | 1,4 s | 0,90 GB |
| **`uebersetzt4`** | **291 s** | **69,9 GB, then killed** |

Every stage of the pipeline — parse, preprocess, elaborate, lower, and the checker's
`decide` — is **cheap** under kernel reduction. **One theorem is the whole 72 GB**, and
it is the one that glues the stages together:

```lean
theorem uebersetzt4 : uebersetzeAllg src104real = .ok ⟨uExp104, P4, fs4⟩ := by
  unfold uebersetzeAllg        -- ← here
  rw [lex104real]; dsimp only; rw [parse4]; …
```

`unfold uebersetzeAllg` rewrites with the equation lemma, whose right-hand side is
`match lex s with …`, **at the concrete source**. Simplification looks at the
discriminant, whnf of `lex src104real` runs §1a's decoder over 2064 bytes, and the file
is gone. The lexer pin `lex104real` was *never* the expensive half — it is one `decide`
that the kernel could do in a few gigabytes even as a literal.

So the repair has two parts, and both are needed:

**(a) the source is pinned as characters** (`Parser/UebersetzeAllg2.lean`):

```lean
-- SRC-BEGIN src104real
def srcZeilen104 : List (List Char) :=
  ["-- 104 -- The reference fixture as a ".toList, … ]   -- 84 pieces, 2064 bytes
-- SRC-END src104real
def srcQuelle104 : List Char := srcZeilen104.flatten
def src104real  : String     := String.ofList srcQuelle104
```

with `lexL` and the bridge in `Parser/Lexer.lean`:

```lean
def lexL (cs : List Char) : Except LexFehler (List Token) := scan cs (cs.length + 1)

theorem lex_ofList (l : List Char) : lex (String.ofList l) = lexL l := by
  unfold lex lexL
  rw [String.toList_ofList, String.length_ofList]
```

**(b) the unfolding happens once, at a VARIABLE** (`Schlusssatz.lean`):

```lean
theorem uebersetzeAllg_von_zeichen {l : List Char} …
    (hl : lexL l = .ok toks) (hp : parseTopTief toks = .ok items)
    (he : elabU (pre108 items) = .ok u) (hw : lowerAllg u = .ok (P, fs)) :
    uebersetzeAllg (String.ofList l) = .ok ⟨u, P, fs⟩ := …
```

and the two chain files apply it:

```lean
theorem uebersetzt4 : uebersetzeAllg src104real = .ok ⟨uExp104, P4, fs4⟩ :=
  uebersetzeAllg_von_zeichen lexL104real parse4 elab4 low4
```

**The same two moves, twice more.** With `Kette104`/`Kette108` down to a gigabyte the
library's peak moved to the next two files carrying the same shape, and they were measured
and fixed the same way:

| Module | what carried it | before | after |
|---|---|---|---|
| `Parser/Uebersetze.lean` | `u104lex`, one 669-byte literal (`decide` 18 s, type check 27 s) | 47,6 s / 9,17 GB | **10,5 s / 1,99 GB** |
| `Schlusssatz104.lean` | `uebersetze104_ok`, `unfold uebersetze104` at `src104` | 32,5 s / 8,91 GB | **2,4 s / 0,93 GB** |

`Schlusssatz104.lean` got its own local stage lemma (`uebersetze104_von_zeichen`) because
`uebersetze104` is the by-hand pipeline keyed to 104's declaration and is defined in that
file. `src104` is now `String.ofList srcQuelle104K` — the pieces live in `Uebersetze.lean`
next to `u104lex`, which is where the text already was.

### Nothing is weakened — the four checks

1. **The theorem statements are the same text.** `uebersetzt4`, `uebersetzt8`,
   `lex104real`, `lex108`, `kette104`, `kette108`, `kette_104 : Kette src104real`,
   `kette_108 : Kette src108`, `s104_lex`, `uebersetze104_ok`, `schlusssatz_104` — every
   one of them is character-for-character what it was. Only proofs changed. `Kette` is
   still indexed by a `String`; `uebersetzeAllg` still takes a `String`. The single
   exception is `u104lex`, whose statement inlined the source literal and now names the
   pin (`lex (String.ofList srcQuelle104K) = .ok tt104`): the same 669 bytes, written
   once instead of twice — `Schlusssatz104.lean` used to carry a second copy of that
   literal, and a source text stored twice is a source text that can disagree with
   itself.
2. **`src104real` still IS the text.** `String.ofList l` is that text by definition
   (`String.toList_ofList` is the core lemma that says so), and the pieces are string
   literals a reviewer reads in the file. No `rfl`-pin is needed because no conversion
   is claimed — the `String` is *built from* the pieces, not *compared to* them.
3. **A guardian still decides whether the pin is the file.** `zaehle-kette.py`'s
   `string_def` now reads the `SRC-BEGIN` block as well, concatenating the `"…".toList`
   literals in order, and compares against `beispiele/*.gab` byte for byte — the same
   contract `pruefe-ctext.py` has on the emitted-C side. Verified on both pins:
   `src104real` 2064 = 2064 bytes identical, `src108` 2082 = 2082 identical. Four new
   speech-test directions (a block reads as its bytes; one byte changed is a different
   text; a missing block is no text; **the same text cut differently is the same text**)
   all pass, so the reader cannot go green over nothing and cannot call a re-cut a
   finding.
4. **Axioms.** `#print axioms` prints `[propext, Classical.choice, Quot.sound]` for
   `lex_ofList`, `lex104real`, `lex108`, `kette104`, `kette108`, `kette_104`,
   `kette_108`, `kette_108_zeuge`, `kette_108_nebenlaeufig` and every theorem in the
   files touched. No `sorry`, no `native_decide`, no new `axiom`. The witnesses
   (`kette_104_zeuge`, `kette_108_zeuge`) are untouched and still non-degenerate.

---

## 3. Re-measured

**Per module** (`lake env lean -Dprofiler=true`, one file at a time, warm imports):

| Module | before | after |
|---|---|---|
| `Grammatik.Kette104` | 4 min 40 s / **72 GB** (O13's figure; my own bounded re-run reached 69,9 GB at 291 s before the bar cut it) | **1,6 s / 0,92 GB** |
| `Grammatik.Kette108` | 6 min 50 s / **72 GB** (O13's figure) | **1,1 s / 0,87 GB** |
| `Grammatik.Kette104Satz` | not measured separately before | 0,7 s / 0,87 GB |
| `Grammatik.Parser.Uebersetze` | 47,6 s / 9,17 GB | **10,5 s / 1,99 GB** |
| `Grammatik.Schlusssatz104` | 32,5 s / 8,91 GB | **2,4 s / 0,93 GB** |
| `Grammatik.Parser.UebersetzeAllg2` | not measured separately before | 20,8 s / 2,93 GB |
| `Grammatik.Parser.Lexer` | — | 14,9 s / 2,51 GB (`lex_keywords` over 243 words) |
| `Grammatik.Schlusssatz` | — | 0,3 s / 0,72 GB |

**The whole library, from an EMPTY build directory, on an idle machine** (`rm -rf
.lake/build`, `lake build`, 248 jobs, exit 0):

| | wall clock | peak resident |
|---|---|---|
| before (O13's figure) | about 25 min | **72 GB**, `code 137` on a 16 GB machine |
| **after** | **319,7 s = 5 min 20 s** | **6,86 GB** |

Peak per module from a 5-second sampler that counts only this directory's processes:

| Module | peak |
|---|---|
| `Parser/ElementTiefProben.lean` | **6,84 GB** |
| `Parser/UebersetzeAllg2.lean` | 2,97 GB |
| `CText104Zeuge.lean` | 2,95 GB |
| `CText108.lean` | 2,91 GB |
| `Parser/Lexer.lean` | 2,35 GB |
| `Parser/Uebersetze.lean` | 2,03 GB |
| everything else (242 modules) | ≤ 1,12 GB |

`Kette104` and `Kette108` do not appear in the top twelve.

**The checks after the repair:**

| What | Result |
|---|---|
| `lake build` (248 jobs) | green, exit 0 |
| `lake env lean Nachpruefung.lean` | 0,2 s / 0,82 GB; `gabbro_ziel`, `gabbro_ziel_zeuge`, `probeA/probeD/w1`, `schlusssatz`, `kette_104_zeuge`, `kette_108_zeuge`, `K124.schlusssatz_124`, `K124.schlusssatz_124_zeuge` — all `[propext, Classical.choice, Quot.sound]` |
| `#print axioms` over the 22 theorems in the files touched | the standard three, every one |
| `zaehle-kette.py --lean` on 104 and 108 | **2 of 2 CLOSED**, sieves (a)–(e) all green, `[YYYYY]` for both |
| `zaehle-kette.py` speech test | 15 of 15 directions, including the four new ones |
| the pins against the files, byte for byte | `src104real` 2064 = 2064, `src108` 2082 = 2082 |
| `pruefe-waechter.py` on `zaehle-kette.py` | `ok` on all four static demands |

*`pruefe-englisch.py` is red on this tree, and it is red on master for the same reason — 30
German feeders in `crates/*.rs`, none of them in a file this lane touched.*

---

## 4. What is left, and what this lane deliberately did not do

**Nothing needs more than 16 GB any more.** The largest single module is
`Parser/ElementTiefProben.lean` at 6,84 GB, and it is the SAME `String.toList` cost in a
file that has nothing to do with the chain: 59 agreement probes of the shape
`lex "…" = .ok […]`, 6606 bytes of literal in all, the longest 489 bytes. It was not
converted because (a) it fits in 16 GB with room, (b) converting it changes 59 theorem
statements' surface (`lex "…"` → `lex (String.ofList …)`), and (c) two Muse lanes are in
that neighbourhood right now. The recipe is written down here so whoever wants the library
under 3 GB can follow it in an hour.

**`CParser/CLexer.lean`'s cost note still quotes 33,7 GB / 217 s.** It is not wrong about
the direction; it is the loaded-machine figure. Left alone to keep this diff small.

**`messung/muse/OPUS-BERICHT-CPARSER.md` still carries the withdrawn brecOn claim.** A lane
report is a dated record, like the commit history — it is not edited after the fact. The
withdrawal is recorded where the claim was being USED as a reason: `CParser/CParse.lean` §4,
`dokumente/OFFEN.md` O13, `dokumente/SATZKARTE.md` §29.6.

**A note on the measuring apparatus, because it cost an hour.** `ulimit -v` is the wrong bar
for a Lean build: Lean reserves far more address space than it touches, and two `lean`
processes under a 30 GB virtual cap DEADLOCKED (`futex_wait`, VmSize 16 GB, RSS 0,5 GB, zero
CPU) rather than aborting — *a bound that hangs the run looks exactly like a run that is
slow.* A watchdog on RESIDENT memory is the honest bar. And it must count only its own
directory's processes: the first watchdog read `ps -C lean` for the whole machine, saw
another lane's build at 72 GB and killed this one. Same family as `W16` and as the `pgrep -f`
trap in CLAUDE.md — **a measuring device that counts the neighbour.**

*(That accident did produce one useful thing: an INDEPENDENT reproduction of the old number.
Another lane's `lean` on `Grammatik/Kette104.lean`, from the unrepaired tree, was sitting at
**72 135 220 kB** when my watchdog read it.)*

---

## 5. The note in `CParser/CParse.lean`

The design note at §4 justified "no recursion in the C expression parser" with the
brecOn law that §1d refutes. The design is fine; the reason was not. The note now says so
in place, keeps the SCOPE reason (this subset's expressions nest at most one level), and
points at §1d for the table. `dokumente/SATZKARTE.md` §29.6 and `dokumente/OFFEN.md` O13
carry the same withdrawal.

**What was NOT established**: why that one probe reached 112 GB. It was not reproduced, and
this lane did not hunt for it — the parser it was about no longer exists in that shape. If
it reappears, the thing to measure first is whether Lean compiled the block to
`WellFounded.fix` rather than `Nat.brecOn`; `Acc.rec` is the reduction the kernel cannot do
lazily, and a mutual block that fails the structural-recursion check falls back to it
silently.
