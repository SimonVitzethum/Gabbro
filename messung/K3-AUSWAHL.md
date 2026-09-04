# «K3» — the selection rule, stated BEFORE the cut

**2026-09-04.** This document exists so that the corpus in
[`k3-fragmente/`](k3-fragmente/) can be checked by somebody who does not trust us. It states
where the code comes from, which rule picked it, and what that rule selected and rejected —
**and it is committed in the same commit as the fragments, before a single one of them has
been run through `gabbro`.**

> **Nothing in this document or in `k3-fragmente/` has been measured at the time of its
> commit.** The freeze is the commit order, not a sentence. `git log --format='%h %ci %s'`
> over the two commits of this lane shows the cut preceding every measurement; the
> measurement stands in [`K3-BEFUND.md`](K3-BEFUND.md) and in the commit after this one.

---

## 1. Why a second corpus, and why «K2» is not one

K100's second gate stands against **trap 80** — *measuring against a corpus you built while
looking at it.* The ten fragments in [`fragmente/`](fragmente/) were chosen **by us, for their
difficulty**; a figure over them measures our selection.

«K2» was declared to be the corpus that fixes this, and the audit of 2026-09-04
([`AUDIT-K100-2026-09-04.md`](AUDIT-K100-2026-09-04.md) §4) took it apart from the commit
graph:

```
21:53  a805a4a  «K2»: zwei Fragmente geschnitten -- EIN Konstrukt blockiert beide ...
22:50  b5f5fdb  RCU ist gebaut: kw.rs, parse.rs, ast.rs, geteilt.rs, beispiele/31-rcu.gab
23:56  6a56874  «K2» abgeschlossen: fuenf Fragmente, vier tragen ohne Rest ...
```

**Fifty-seven minutes between the cut and the construct that both cut fragments had failed
on.** The checker moved after seeing the corpus, so the corpus became a fixture. Its
*counting* half — 234 files, 578 `rcu_read_*`, 2669 `goto`, 2034 `BUG_ON`/`WARN_ON` over
`kernel/`+`mm/` — is genuine and re-derives byte for byte; its *fragment* half is five
author-written reproductions.

`dokumente/PLAN.md`:1531 still claimed *"three whole modules, all three check clean and lower"*
while the checker itself said **1 clean unit out of 4 blocks** in that range. That line is
corrected in the same lane as this replacement.

---

## 2. The source

| | |
|---|---|
| tree | `/home/simon/Dokumente/SEL4Lake/_linux-mess/linux` |
| version | **Linux 7.2.0-rc7** |
| commit | `db2ddb87143519e20a95aa36c60b36107b736a58` — *"Linux 7.2-rc7"*, 2026-08-09 |
| author line | **foreign.** Nobody in this project wrote a line of it. |

```bash
cd /home/simon/Dokumente/SEL4Lake/_linux-mess/linux && git log -1 --format='%H %ci %s'
# db2ddb87143519e20a95aa36c60b36107b736a58 2026-08-09 14:54:50 -0700 Linux 7.2-rc7
```

This is the **same tree** «K2» counted over. That is deliberate: its counting half is the one
part of «K2» that survived the audit, so the ground is already surveyed and the figures beside
this corpus are comparable. What changes is the region and the method.

---

## 3. The region — `lib/`, at `-maxdepth 1`

**`lib/*.c` — the kernel's own general-purpose library, 212 files.**

Three reasons, all stated before anything was read:

1. **It is disjoint from `kernel/` and `mm/`**, which are the only two directories this
   project has ever counted over or cut from. Nothing in `lib/` has been transcribed here
   before — and neither has anything from Caprock, which is a different tree entirely.
2. **It is a named subsystem**, not a hand-drawn set of files.
3. Its functions name comparatively few foreign structures, so a transcription is an
   **excerpt** rather than mostly scaffolding of our own invention. That matters because the
   whole point is faithfulness: `messung/fragmente/`'s rule — *only declarations the excerpt
   calls and does not name may be added* — is only affordable where that set is small.

> **The bias this buys, stated up front so that it can be discounted:** `lib/` is
> algorithmic and data-structure code — bounded loops, arrays, bit work, intrusive lists.
> Bounded loops and arrays are the class Gabbro was designed for; intrusive lists are a class
> it has no answer to at all. **If the result comes out well, this choice is part of why; if
> it comes out badly, so is this choice.** It is not neutral and is not claimed to be.

---

## 4. The rule

**Stated in full before it was run, and run exactly once.**

1. A **function definition** is a line that is exactly `{` at column 0, whose preceding line
   ends in `)`, closed by the first following line that is exactly `}`. Its **body length**
   is the number of lines strictly between the two.
2. The **candidate set** is every such definition in `lib/*.c` (`-maxdepth 1`), ordered by
   *(file name, line number)*.
3. One **size window**, and it is the only non-positional criterion: `8 <= body <= 60`
   lines. *The lower bound drops wrappers that have nothing in them to measure; the upper
   bound is the largest excerpt that can still be transcribed line by line at this scale.*
   Both bounds are properties of the **excerpt**, not of what it does — the rule never looks
   at what a function contains.
4. **Take every Nth survivor**, `N = floor(candidates / 8)`, starting at index 0, until eight
   are taken.

Nothing about the fragments — not their subject, not their difficulty, not whether Gabbro can
say them — enters anywhere in this rule.

### The program, verbatim

```python
#!/usr/bin/env python3
import re, sys, glob, os
REGION = sys.argv[1]
LO, HI = 8, 60
WANT   = 8

def funcs(path):
    lines = open(path, encoding="utf-8", errors="replace").read().split("\n")
    out = []
    for i, l in enumerate(lines):
        if l != "{" or i == 0:
            continue
        if not lines[i-1].rstrip().endswith(")"):
            continue
        j = None
        for k in range(i+1, len(lines)):
            if lines[k] == "}":
                j = k
                break
        if j is None:
            continue
        s = i-1
        while s > 0 and lines[s-1].rstrip() != "" and not re.match(r"^\S", lines[s]):
            s -= 1
        sig = " ".join(x.strip() for x in lines[s:i])
        m = re.search(r"([A-Za-z_][A-Za-z0-9_]*)\s*\(", sig)
        if not m:
            continue
        out.append((path, i+1, j+1, j-i-1, m.group(1), sig))
    return out

files = sorted(glob.glob(os.path.join(REGION, "*.c")))
cands = []
for f in files:
    cands.extend(funcs(f))
cands.sort(key=lambda t: (t[0], t[1]))
inwin = [c for c in cands if LO <= c[3] <= HI]
N = len(inwin) // WANT
picked = [inwin[k] for k in range(0, len(inwin), N)][:WANT]
```

### What it selected and what it rejected

```
$ python3 auswahl.py /home/simon/Dokumente/SEL4Lake/_linux-mess/linux/lib
# region     /home/simon/Dokumente/SEL4Lake/_linux-mess/linux/lib
# files      212
# functions  3324
# window     8..60 body lines -> 1709 candidates (rejected: 1451 too small, 164 too big)
# stride     N = 1709 // 8 = 213; take index 0, N, 2N, ... (8 picked)

     0  alloc_tag.c:62-76        13 lines  allocinfo_start
   213  debugobjects.c:199-222   22 lines  pool_pop_batch
   426  iov_iter.c:47-71         23 lines  copy_from_user_iter
   639  lru_cache.c:300-309       8 lines  lc_del
   852  percpu-refcount.c:65-105 39 lines  percpu_ref_init
  1065  stackdepot.c:363-393     29 lines  depot_pop_free_pool
  1278  test_firmware.c:1556-1566 9 lines  test_firmware_exit
  1491  test_vmalloc.c:537-594   56 lines  test_func
```

| | |
|---|---|
| **denominator** | **8** — fixed by the rule before the candidates were enumerated |
| rejected by the window | 1451 below 8 body lines, 164 above 60 |
| rejected by the stride | 1701 of the 1709 in the window |
| rejected by us | **none.** No fragment was swapped, re-rolled or dropped after it was seen |

> **Two of the eight are test-module code** (`test_firmware_exit`, `test_func`), and one of
> those is the largest. That is what a positional rule over `lib/` yields; it is not a defect
> of the draw and nothing was done about it. *A corpus one is allowed to re-roll is a corpus
> one chose.*

---

## 5. What a fragment file is

Each of the eight is transcribed into one `.gab` file under
[`k3-fragmente/`](k3-fragmente/), under the rule this folder already uses for
`messung/fragmente/`:

* the **C excerpt stands verbatim** in the head of the file — whoever reads the Gabbro can
  hold it against the original line by line;
* **added are only the declarations the excerpt names and does not define** — the foreign
  structures, the callees, the constants. They are marked as added;
* **`effects` and `costs` are added at every function**, because the language refuses a
  function without them. *The C has no such clause, so this is not transcription — it is what
  Gabbro demands of anything that is to be a function at all, and it is marked at every site;*
* **nothing is bent to be writable.** Where a C statement has no Gabbro form, the statement
  stands as a comment marked `WALL`, naming what is missing, and **nothing is put in its
  place.** *An excerpt that was bent to be writable measures the bending.*

---

## 6. The order, and it is the whole mechanism

1. **This document and the eight fragments are committed first.** No measurement has been run.
2. **Then** `gabbro pruefe` / `emit` / `cc` over the eight, in a **second** commit.
3. **After the measurement, nothing under `crates/` moves.** If a fragment shows a gap, the
   gap is the result. *A checker that moves after seeing the corpus turns the corpus into a
   fixture* — which is exactly what happened to «K2» on 2026-08-18.
