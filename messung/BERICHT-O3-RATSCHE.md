# O3 — must the obligation NAME bind the obligation's CONTENT?

Running report. Lane: the subject of §15's ratchet (`SPRACHE.md` §15, `OFFEN.md` `O3`).
Worktree `.claude/worktrees/agent-adca48c751da1d8d3`, from `master` at `1cb66b0`.
Built on `ki-pc-fisch-101:gabbro-nb` (`cargo build --offline`, 5.23 s); the sweeps run the
finished binary locally, `free -g` reading 31 GB total and 20 GB available.

- [x] 1. reachability — how many obligations carry an ordinal above 1, with the denominator
- [x] 2. has it already happened in this tree's history
- [ ] 3. what the register itself relies on
- [ ] 4. the options with their costs, the recommendation, and the cheap one built

---

## 1. Reachability — **28 of 113 for a swap, 79 of 113 for an insertion, 113 of 113 for an edit**

Measured 2026-09-03 at `1cb66b0` over **every `.gab` in the tree bar `beispiele/gift/`**:
183 units, 134 of them emitting a register, **38 carrying at least one obligation line**,
**113 obligation lines** total. (`messung/gabbrov/MANIFEST-COMPLETENESS.md` says 110 at
`94c9ac5`; the three extra are `F01`, which got a register on 2026-09-03 with `501b758`.
Two numbers, one reconciled cause — not two measurements.)

The name is built in `crates/gabbro-check/src/pflichten.rs`, and only three of the eight
kinds put an **ordinal** in it:

| kind | name shape | ordinal over |
|---|---|---|
| `N` / `F` | `<fn> :: ensures #n` | the function's `ensures` conjuncts (`pflichten.rs`:654) |
| `V` | `<fn> :: <callee> requires #n` | the **callee's** `requires` conjuncts (`pflichten.rs`:358) |
| `S` | `<fn> :: loop invariant #n` | the loops of the body, in source order (`pflichten.rs`:535) |
| `E`, `R`, `D`, `W` | `maintains I` · `refines g` · `reg X requires` · `invariant X` | — a NAME, no ordinal |

So there are three severities and they must not be reported as one number:

| | lines | what moves the mark |
|---|---:|---|
| **a swap of two siblings** | **28 of 113** | needs a sibling group of size ≥ 2 — there are **11 such groups over 6 files** |
| **an insertion or deletion among the siblings** | **79 of 113** | every ordinal-bearing line, *including the lone `#1`s*: write a new conjunct in front of `ensures #1` and `#1` now denotes the new one |
| **an edit of the text under an unchanged name** | **113 of 113** | also the four NAMED kinds — edit the body of the `spec fn` a `maintains I` points at, and `I` names something else |

The eleven permutable groups, in full:

```
3x  beispiele/01-tabelle.gab        aushaengen     :: ensures #
2x  beispiele/01-tabelle.gab        blatt_loeschen :: aushaengen requires #
3x  beispiele/01-tabelle.gab        einsammeln     :: blatt_loeschen requires #
3x  beispiele/09-ohne-zeiger.gab    einsammeln     :: blatt_loeschen requires #
2x  beispiele/53-zwei-orte.gab      treffen_oeffnen    :: ensures #
2x  beispiele/53-zwei-orte.gab      treffen_schliessen :: ensures #
2x  beispiele/56-auftragsring.gab   einreihen      :: ensures #
4x  messung/caprock/kapraum.gab     einsammeln     :: blatt_loeschen requires #
2x  messung/fragmente/F01.gab       delete_leaf    :: ensures #
2x  messung/fragmente/F01.gab       delete_leaf    :: unlink requires #
3x  messung/fragmente/F01.gab       unlink         :: ensures #
```

Class census of the 113: `N` 35, `V` 27, `D` 15, `E` 12, `F` 12, `W` 6, `S` 5, `R` 1.

**And the name IS a key today, just not a content-binding one:** no two lines inside one unit
carry the same name (0 of 113). The `V` duplicate `pflichten.rs`:55 warns about is still
latent, as that comment says.

**The number is not zero, in any of the three readings.** The cheapest reading (a swap) is
small — 28 of 113 — but the reading that matters for a ratchet is the middle one: an
obligation added to a contract renumbers every later one, and 79 of 113 lines carry a number
that an addition can move.

## 2. Has it already happened? — **No, and it could not have: the corpus has never edited a contract at all**

This is the question that outranks the rest, so it was measured exhaustively rather than
along `git log -- <path>` (which simplifies history and can drop a change that arrived
through a merge).

**Method.** `git rev-list --all` → **1079 commits**, each diffed against **every** parent,
every `.gab` on both sides parsed into per-function ordered conjunct lists, and consecutive
lists compared. Classification: `PERMUTATION` (same multiset, different order), `SHIFT` (an
ordinal that exists on both sides carries different text, both texts present on both sides),
`EDIT` (anything else).

```
modified-file pairs examined:  459
clause lists identical:        398
clause lists changed:            0

==== 0 distinct change(s) ====
```

**A detector that has never fired has measured nothing**, so it was driven in all three
directions against the very file `O3` uses — swapping `aushaengen`'s `ensures` conjuncts 1
and 3, inserting one at the front, and editing one in place:

```
base: ['c.slots[s].elter == None', 'c.slots[s].vorheriges == None', 'c.slots[s].naechstes == None']
  swap 1<->3        -> PERMUTATION
  insert at front   -> SHIFT
  edit conjunct #1  -> EDIT
SPRECHPROBE: ok
```

**Second, independent direction, with no parser in it.** A permutation must remove a line.
Over `git log --all -p --diff-filter=M -- '*.gab'` — every modification of every `.gab` file
that ever existed — there are **2 521 added lines and 282 removed ones**, and of the 282
**not one** contains `requires`, `ensures`, `maintains`, `invariant` or `refines`, and not
one is a bare conjunct continuation line either (they are `}`, `{`, `costs`, `traverse`,
`extern fn`, `lock`, `can_fail`, `return`). The removed lines are structural, never
contractual.

The two flagship carriers say the same thing one file at a time: `beispiele/01-tabelle.gab`
went through six revisions and `messung/fragmente/F01.gab` through five, and each carried
**exactly the same 11 and 16 conjunct slots, byte for byte, at every one of them.**

> **The finding, stated as it is:** in this tree's whole history no `requires`/`ensures`
> conjunct has ever been reordered, renumbered, or edited. A contract arrives with its file
> and never moves again. **So no `closed` mark stands on the wrong obligation today** — and
> no mark could have, because the write-back that would set one (`GABBROV.md` V4) is not
> built: `pflichten.rs::ZUSTAND` is the constant `"open"`, and all 113 lines say `open`.

*That is a statement about the past and about today, and about neither tomorrow nor the
corpus that V4 will be pointed at.* The corpus has been append-only because it is a
demonstration corpus; the moment an obligation is worked on rather than written down —
which is exactly what a `closed` mark implies is happening — the append-only habit ends.
