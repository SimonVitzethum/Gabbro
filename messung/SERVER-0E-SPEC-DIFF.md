# The `Spec.lean` diff of the dynamic arena — what moves, and why nothing is weakened

*Server lane (`ubuntu@simon.jocraft.cc`), 2026-09-28, session 3. TODO §0e item 1, deliverable
H3. The review is written by the lane that made the diff; every claim below names the command
or the file that answers it.*

**The diff is COMMENT ONLY.** No definition of `grammatik/Grammatik/Zielsatz/Spec.lean`
changes, no premise group gains or loses a member, `Laufzeit` has the three fields it had
(`lader`, `start`, `einmal`), and no proof in the tree is touched. Measured:

```
$ git diff --stat master -- grammatik/Grammatik/Zielsatz/Spec.lean
$ cd grammatik && ~/.elan/bin/lake build          # 355 jobs, no error
$ cd grammatik && ~/.elan/bin/lake env lean Nachpruefung.lean | grep gabbro_ziel
'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 1. What was asked, and what the previous session expected

`AUFTRAG-1.md` H3 asks for "the two `Spec.lean` (d) fault-latency assumption texts as a
reviewed diff". `PLAN-DYNAMISCH.md` §9 fixes their wording and their names,
`Laufzeit.reserve` and `Laufzeit.commit`, and says they go "in the ONE list (`Spec.lean`
header style)".

Session 2's hand-over (`~/claude-lane/STAND.md`, point 0 of *Next step*) read those names as
**new FIELDS of the `structure Laufzeit`**, and measured the consequence: five construction
sites (`Zielsatz/Ruhe.lean:538`, `:597`, `Zielsatz/FaedenZeuge.lean:381`, `:495`,
`Schlusssatz124.lean:1291`) plus every generated certificate would have to supply them, and
a half-added premise leaves `grammatik/` red.

**That reading is wrong, and this session did not follow it.** The reason is below; it is the
only judgement call in this diff, so it is the first thing a reviewer should attack.

## 2. Why the texts are NOT new fields

A field of `Laufzeit` is a **premise of `GabbroZiel`**. Premises only ever move one way: every
premise added makes the theorem say *less* — it excludes runs from the claim. So the question
"does a new field weaken the statement?" has one answer before one looks at the content: yes,
unless the field is already implied by the premises that stand.

Take the two texts one at a time.

**`Laufzeit.reserve`** — *"the loader reserves the virtual range for every dynamic arena's `M`
before any start runs; a failed reservation refuses the load, it never starts a program with a
smaller range."*

In this statement an arena **is** a table (`ArenaZucker.lean`; for the dynamic form,
`ArenaDyn.lean` section `Form`: the table spans the ceiling `M`). The loader premise that
stands, `Laufzeit.lader : sp = speicherR E.sp0`, says the loader establishes the program's
declared initial memory — and that memory *contains the table of `M` slots*. A load that
cannot provide the range establishes no `E.sp0`, so `lader` is **false** of it and the theorem
already says nothing about that run. The reservation is not a missing premise; it is the
reading of a premise that stands.

Adding it as a field would therefore (i) claim nothing new, (ii) cost five construction sites
and every certificate, and (iii) weaken the theorem by exactly the runs where the *new* field
fails while `lader` holds — an empty set if the field is stated correctly, and a silent hole
if it is not. That is ceremony bought at the price of a guarantee, which
`PLAN-EINFACHHEIT.md` and AGENTS.md §3 both forbid.

**`Laufzeit.commit`** — *"every `grow` the checker admits either commits its slots before the
next statement runs or takes the `else` branch; a commit that reports success names
readable/writable storage; commit latency is bounded by the runtime's declared per-slot
cost."*

Here the first clause is now **proved, not assumed**. `ArenaDyn.dynGrow_commit` (added this
session) says the form has exactly two outcomes: the narrow of `committed + n` into `0 .. M`
fits and one store happens — with the frame, so the used counter and every slot stay put — or
it does not fit and the `else` runs, and `Block.narrow`'s `else` does not fall through. Past
the ceiling there is no branch at all (`dynGrowListe_scheitert`, from fix lane F2). Making the
clause a premise would *assume* what the model proves, and a reader who later weakened
`dynGrow_commit` would not notice, because the premise would carry the claim.

What is left of the text after the proof takes its half is a statement about the **C runtime**:
a commit that fails below the ceiling must reach the program's `else` or fail-stop, and must
never report success over storage that faults on first touch. That is the same class as every
other "the C realises what G means" fact — covered by the NOT CLAIMED line *"the C and the
hardware"* and settled by translation validation, not by a premise. The latency clause is the
same: `ArenaDyn.growKosten` reads the per-slot cost as **data** from premise (c)'s latency
entry and proves nothing about it (`growKosten_pos` is the only claim, and it is arithmetic).

## 3. What the diff actually is

Two new bullets in THE ONE LIST of the header (the list whose entries read
`* (d) \`Laufzeit.lader\` -- …`), inserted between `lader` and `start`/`einmal`:

* **`(d) Laufzeit.reserve`** — PLAN-DYNAMISCH §9's wording verbatim, then: no new premise and
  no new field, with the argument of §2 above; then what the reservation *is* on each of the
  three runtimes that exist today — hosted `mmap(PROT_NONE)` + lazy `mprotect`
  (`laufzeit/arena_dyn.c`), the carved region of (M10) on metal, one `vzalloc` region per
  arena with a budget over it in a Linux kernel module (`laufzeit/kmodul/arena.c`); and the
  explicit NOT CLAIMED: *that the reservation succeeds* — refuse-on-load is a refusal, not a
  leg.
* **`(d) Laufzeit.commit`** — PLAN-DYNAMISCH §9's wording verbatim, then which half is proved
  (`dynGrow_commit`, `dynGrowListe_scheitert`) and which half is assumed about the C, and the
  sentence that the latency number is read and never justified.

And one clarification in NOT CLAIMED, on the line that puts dynamic unbounded data structures
out of scope (OFFEN O29): an `arena … max M` is **not** that case — its ceiling bounds it, its
form is sugar over the existing `Block` — **but** the exporter does not produce that shape, so
no dynamic-arena program is CERTIFIED (see §5).

## 4. Why nothing is weakened — the checklist

| Question | Answer, measured |
|---|---|
| Does any premise move? | No. `Laufzeit` has `lader`, `start`, `einmal`; `GabbroZiel`'s four premise groups are byte-identical. |
| Does any leg of `Ziel`/`ZielF`/`ZielX` move? | No. No definition in the file changed. |
| Does any proof change? | No. `lake build` is 355 jobs with no error; `#print axioms gabbro_ziel` is the three standard axioms. |
| Is a refusal turned into a warning? | No refusal is touched. `N426` (every `grow` against the UPPER bound) and `N466` (`R-commit`) stand unchanged; `LG005` still refuses `grow` in the exporter. |
| Is an `ensures` derived? | No. |
| Does the NOT CLAIMED list shrink? | No. It gains a *clarification* and loses no line. The clarification makes the list stricter in one direction: it now says in writing that no dynamic-arena program is certified. |
| Could the new text be read as a claim? | Both bullets say what is NOT claimed in their own body, and both are marked as comment-only. |

## 5. The gap this diff makes visible (and does not close)

Writing the clarification forced a measurement that had not been made in this lane:

```
$ grep -n "StmtArt::Grow" crates/gabbro-check/src/lean_g.rs
4184:        // **Lane 257:** `grow A by n else { … };` has no G form in this
4189:        StmtArt::Grow(g) => Err(refuse("LG005", …))
```

The exporter **refuses `grow` (`LG005`)** and, for an arena declaration, builds the static
`ArenaForm` over `hi` — not over the ceiling `M`. So:

* the Lean forms of `ArenaDyn.lean` section `Form` are covered by `gabbro_ziel`, because they
  are ordinary `Block` terms and the goal theorem quantifies over all of them;
* **no dynamic-arena program is CERTIFIED**, because the exporter cannot write one down;
* for such a program a green `lake build` says nothing — exactly what the header's
  *WHAT A GREEN BUILD COVERS* paragraph says about every UNCERTIFIED program.

This is the same status `ArenaZucker.lean` had between its merge and the closing of OFFEN O14.
It is now written into three places so it cannot be read past: the NOT CLAIMED clarification
in `Spec.lean`, the CUTS of `ArenaDyn.lean`, and this section. **It is not closed here**, and
closing it is exporter work (`lean_g.rs`: a `DynForm` model beside the `ArenaForm` one), not
model work.

## 6. What a reviewer should check

1. `git diff master -- grammatik/Grammatik/Zielsatz/Spec.lean` touches only comment lines.
2. The two bullets' first sentences are PLAN-DYNAMISCH §9's wording, unchanged.
3. §2's argument: is `Laufzeit.lader` really false of a load that cannot reserve `M`? It rests
   on the arena being a table of `M` slots in `E.sp0` — check `DynForm` in
   `grammatik/Grammatik/ArenaDyn.lean` (`hk : D.gtyp komm = Ty.int 0 (D.count tab)`, the table
   spans the ceiling) and `ArenaForm` in `ArenaZucker.lean`.
4. `dynGrow_commit` really has the frame conjuncts (used counter, slots) — if it does not, the
   `Laufzeit.commit` bullet claims a proof that does not exist.
5. The witnesses are not degenerate: `DynZeuge.gespannt` is an arena with **room to the
   ceiling whose allocation is refused** (`zeuge_alloc_ueber`, `zeuge_raum_unter_der_decke`),
   which is the one state the static form cannot name.
