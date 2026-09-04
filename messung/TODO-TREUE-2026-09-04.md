# `TODO.md` against the code — a measured staleness rate, 2026-09-04

**Base:** `master` at `ac39916`. Worktree `agent-a19c3a7bcf672d8ec`, server directory
`gabbro-code`. **Mandate:** `TODO.md` is a register, and a register is a claim; the code is
what runs. Do not read the document end to end and paraphrase it — sample it against the code
and report the hit rate. **`pruefe-zahlen.py` already holds 91 figures against their commands
(a separate, already-covered class); this checks the prose, file references and status
claims no guard holds.**

## 1. The sampling rule, stated before the answers

1. Every line in `TODO.md` matching `\b[A-Z][0-9]{2,4}\b` (a rule-ID-shaped token, e.g. `M140`,
   `N035`, `P006`) **or** `crates/[A-Za-z0-9_./-]+` **or**
   `instrumente/[A-Za-z0-9_.-]+\.(py|sh)`, deduplicated by line number and sorted:
   **441 candidate lines**, out of 5331 total.
2. Sample = every 9th line of that sorted list (systematic, not chosen by interest):
   **49 lines** — 13, 156, 259, 343, 440, 491, 580, 772, 829, 996, 1043, 1189, 1286, 1387,
   1470, 1550, 1644, 1780, 1873, 2032, 2102, 2260, 2343, 2531, 2625, 2669, 2770, 2854, 2942,
   3019, 3181, 3326, 3354, 3408, 3467, 3542, 3781, 3985, 4060, 4096, 4153, 4247, 4301, 4560,
   4831, 5077, 5193, 5270, 5304.
3. Per line: found the enclosing claim (TODO.md bullets run many lines; the sampled line is
   usually mid-sentence), then checked it against the code with a bounded effort — a couple
   of greps and, where a figure was involved, one live run of the guard named in the text.
   Classified **HELD** (matches), **STALE** (was true, code has since moved: renamed,
   relocated, superseded, numbers moved, status flipped), **NONEXISTENT** (names something
   that isn't in the tree at all), or **UNCLEAR** (a bounded effort could not settle it —
   mostly design narrative or an external-repo reference).

## 2. The result

| verdict | count | share |
|---|---:|---:|
| HELD | 29 | 59 % |
| STALE | 7 | 14 % |
| NONEXISTENT | 0 | 0 % |
| UNCLEAR | 13 | 27 % |
| **total** | **49** | |

**No sampled claim names a rule, file or function that does not exist.** Every `M`/`N`/`P`/`S`/
`H`/`D`/`E`/`K` code and every `crates/`/`instrumente/` path checked resolves to real code.
The failures are not fabrication — they are **drift**: a line number that moved when a file
grew, a count that grew with the corpus, a bug already fixed while the checkbox stayed open,
a label that migrated. That is a different and cheaper kind of untrustworthiness than
"names something imaginary," and it is the one a register accumulates by just sitting still
while the tree keeps moving.

## 3. The seven `STALE` findings, in enough detail to act on

**`TODO.md:438-459`** — *"`zaehle-absagen.py` schließt im Arbeitsbaum eines AGENTEN den
ganzen Korpus aus"*, an open (`- [ ]`) item citing `instrumente/zaehle-absagen.py:379–381`
for an absolute-path `.claude` filter, and proposing the fix in prose: *"Die Heilung ist ein
Satz und keine Zeile: der Filter müsste relativ zur Wurzel wirken statt absolut."* **Both are
wrong today.** The file is 588 lines now and the filter sits at `:420` (`aus_bau = ("target",
".claude", ".lake")`), and it already tests `d.relative_to(wurzel).parts[:-1]` — the exact
fix the entry proposes as still-needed. The code's own comment at `:403-418` narrates this
bug and its repair in the past tense. The checkbox should be closed; it is not.

**`TODO.md:1043-1047`** — *"`./instrumente/pruefe-gruende.py` führt heute 5 verdächtige,
114 tragende, 96 unklare"* (dated 2026-08-31/2026-09-01). Live run today:
```
7 verdaechtig · 122 tragend · 101 unklar
```
All three counts moved (5→7, 114→122, 96→101) as more identifiers were added. The mechanism
described (a closed suspect-word list over refusal texts) is unchanged; only the figures
are stale.

**`TODO.md:1189-1193`** — *"`--anker` meldete `382 von 383` am selben Tag"*, cited as the
then-current mutation-anchor state. Live run today:
```
timeout 60 python3 instrumente/mutiere-pruefer.py --anker
== 392 von 392 Ankern greifen ==
```
Not just a count that grew (383→392 as the catalogue grew) — the entry describes a state with
one anchor *not* holding, and today's run is a clean `392 von 392`. The gap the entry is about
has since closed.

**`TODO.md:1470-1474`** — *"`./instrumente/pruefe-reichweite.py` (0 ungelesen, zwei Bauteile
von genau einem Pass gelesen)"* and *"`./instrumente/pruefe-klauseln.py` (22 Klauseln
gebucht, sechs ungelesen)"*. Live runs today:
```
== 0 ungelesen, 0 von genau einem Pass gelesen ==      (pruefe-reichweite.py)
-- UNGELESEN: 4 --
== KLAUSELN: 13 gebucht, keine neue ==                 (pruefe-klauseln.py)
```
"Zwei Bauteile" is now zero, and the clause register shrank from 22/6 to 13/4 — a bigger
move than ordinary corpus growth explains, and worth a second look by whoever owns that
guard, not just a re-citation.

**`TODO.md:2770-2771`** — *"seit dem 2026-08-20 traegt der Faden eine Zahl
(`./instrumente/zaehle-theorien.py`: 2 von 13 Theorien ohne Register)"*. Live run today:
`2 von 15`. The numerator held; the denominator is stale by two theories.

**`TODO.md:2854-2858`** — *"Zahn 3: NEUN Praemissen ohne Hersteller"* (measured 2026-08-18,
recomputed 2026-08-20). Live run today (`gabbro schablonen --tor`):
```
gabbro schablonen --tor: 6 premises of PROVED templates have no pass
```
The gate still exists and still fails (`EXIT=1`, confirming the entry's general claim that
the tor is mechanically red) — but the count is 6, not 9; three have been closed since.

**`TODO.md:343-347`** (minor) — *"Danach 31 Items, 0 Fehler, 0 Hinweise, 199 Zeilen C"* for
`F05`. Live run today: `32 items, 0 errors, 0 hints`, C output `204` lines. The qualitative
claim (checks clean, lowers) holds; the exact counts drifted by one item and five lines,
most likely a later, unrelated addition to the checker or the fragment.

## 4. What `HELD` looked like, so the ratio is legible

Not every hit was a coincidence-proof re-citation. Two are worth naming because they were
verified against the **live, canonical** tool output rather than a second document:

* **`TODO.md:5077`**: *"`grep -c 'table.ops.erhaltung' crates/gabbro-check/src/zeugnis.rs` →
  `0`."* Run verbatim today: `0`. An exact, reproducible match, command included in the
  claim itself.
* **`TODO.md:2669`**: claims today's register has `S17 = ops.suche`, `S20 = gruppe.ops`,
  `S21 = gruppe.sperrabdruck`, all `entworfen`. `./target/debug/gabbro schablonen --tor`
  today prints exactly that mapping. (Two in-source *comments*, `schablonen.rs:779` and
  `:999`, still call `gruppe.sperrabdruck` "S17" — a drift inside the source's own prose, not
  in `TODO.md`; the tool's canonical, position-derived numbering is what `TODO.md` matches.)

## 5. What `UNCLEAR` means here, so it isn't read as a third failure class

13 of 49 (27 %) could not be settled inside a bounded couple-of-greps effort. They are
concentrated in three shapes, none of which is "the claim looked wrong":

* **Open design questions and deferred decisions**, stated as such in the text (*"Wo endet
  die Forderung `Has(X)`?"*, the `NICHT JETZT` table, the *carried-forward* design table at
  `:4293-4301`) — there is no code state to check them against; that is the point of the
  entry.
* **Narrative about a specific past run** (a printed 25 % coverage figure, a `512¹⁵` typo
  correction) where the artefact that would confirm it is a log line from one run on one day,
  not a re-runnable guard.
* **A claim about a different repository** (`TODO.md:3019`, `crates/caprock-cap/src/space.rs`
  — Caprock's own tree, read-only, `../caprock-messbasis`), out of the effort budget for this
  pass.

None of the 13 showed a contradiction on the light check performed; they are reported
separately from `HELD` only because "no contradiction found in one grep" is a weaker claim
than "reproduced against a live run," and the sampling rule asked for that distinction to
stay visible rather than be rounded up.

## 6. Reading the ratio

**0 of 49 name something that does not exist.** Every rule identifier and file path sampled
resolves. **7 of 49 (14 %) are stale** — mostly numbers that moved as the tree grew, plus one
item (`zaehle-absagen.py`, `:438-459`) where the underlying bug has been fixed and the
checkbox was never closed. That is a usable document with a measurable decay rate, not an
unusable one — but it is also not the ground truth `K100-VERDICT-2026-09-04.md`'s mandate
insists on treating it as: **a register that stops being re-verified starts drifting the
moment the tree moves under it, and this sample puts a number on how far it has drifted.**
