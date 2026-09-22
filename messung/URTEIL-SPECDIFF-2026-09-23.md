# Verdict — the Spec diff of fix lanes F9, F10, F11

*Independent review, 2026-09-23, of `git diff 4e6c2435..97f56b11` over the goal-statement area.
AGENTS §2 asks that every extension of the goal be reviewed as a diff of `Spec.lean`; that
review had not happened for F9/F10/F11, whose work was already on master. Adversarial standard:
nothing is accepted on the strength of a claim in a comment or a report.*

**Machine:** the laptop, locally, by Simon's decision (fisch unreachable).
`free -g`: 31 GB total, 19 GB available. 20 cores.

---

## 0. Verdicts at a glance

| Change | Verdict |
|---|---|
| **F9** (`ea2d41f0`) — O-1 clone handoff, one NOT-CLAIMED line, standalone `klon_ziel` | **SOUND** |
| **F10** (`16a0185b`, `513924b0`) — `einzeln := EinzelnPool`, `Getrennt` pairs occurrences, `Laufzeit.einmal` relaxed | **SOUND** |
| **F11** (`f5d83439`) — new leg `keinKernHalt : KernHaltG` | **SOUND as a theorem, OVERCLAIMED in its header** (F1, fixed) |

No unsound step was found. One overclaim was found, and it is the central sentence of F11's
own "why nothing is weakened" paragraph. It is corrected in a follow-up commit (§6).

---

## 1. Build and axiom evidence (measured, not quoted)

| Measurement | Result |
|---|---|
| `cd grammatik && lake build` | **green, `EXIT=0`**, 285 jobs |
| `#print axioms gabbro_ziel` | **`[propext, Classical.choice, Quot.sound]`** — exactly the three |
| `cargo test --no-fail-fast` | **`EXIT=0`, 72 collections, 1326 passed, 0 failed** |
| `pruefe-akzeptiert-diff.py --selbsttest` | ok, both directions; pool case: example 157 accepted at `einzeln` |
| `pruefe-akzeptiert-diff.py` | green; all nine components agree on **19/19** comparable programs |
| `sorry` / `admit` / `native_decide` in `grammatik/` | **none** (only the words inside prose comments) |
| `axiom` declarations in `grammatik/` | **exactly one: `dma_inhalt` (`Geraet.lean:204`)** — pre-existing (lane 29, P24), unrelated to the goal theorem, and absent from `gabbro_ziel`'s axiom set |

Every new theorem of the three lanes prints standard axioms: `kernHaltG_gilt`,
`einzelnPoolB_iff`, `poolSicherWB_iff`, `mehrfachB_iff`, `pruefer_vor_neu`, `laufzeit_vor_neu`,
`akzeptiert_nodup_gleich`, `pool_ziel_zeuge`, `pool_abgelehnt`, `masken_zeuge`,
`masken_disziplin_59`, `masken_disziplin_460`, `klon_ziel`.

All four new files are imported by `grammatik/Grammatik.lean` (`CloneHandoff`,
`Zielsatz.Masken`, `Zielsatz.MaskenZeuge`, `Zielsatz.PoolZeuge`), so the build really covers
them; a new file that no one imports is a file no one checks.

---

## 2. F10 — the changed premises. Relaxation or restriction?

Three things moved. Taken one at a time, and then together.

### 2.1 `AkzeptiertSpec.einzeln : ws.Nodup` → `EinzelnPool P fs ws` — a **RELAXATION**

`EinzelnPool ws := ∀ w, Mehrfach ws w → PoolSicherW P fs w`, and `Mehrfach ws w` is
`List.Sublist [w, w] ws`. On a repetition-free `ws` nothing is `Mehrfach`
(`nicht_mehrfach_of_nodup`), so the new field holds vacuously: `einzelnPool_of_nodup`. Strictly
weaker, and **strictly** so — `einzelnPool_paar` gives `EinzelnPool P fs [w, w] ↔ PoolSicherW P fs w`,
which is inhabited (`zPool_poolSicher`), while `[w, w].Nodup` is not.

### 2.2 `Getrennt` pairs an occurrence with itself — a **RESTRICTION**

`w₁ ≠ w₂` became `(w₁ ≠ w₂ ∨ Mehrfach ws w₁)`, so more pairs must satisfy the separation
condition. **This is a genuine tightening, and it bites**: `pool_fuss_paart_vorkommen` proves
`fussWB mP mSI mFs [mHauptA, mHauptA] = false` where the pre-F10 `fussWBVor` was `true`. That is
exactly right — it is what stops a pool routine from reading in a footprint what its own second
instance writes — and it is the part of the diff a careless lane would have left out.

**Is any previously accepted unit lost by it?** No, and this is proved, not argued:
`akzeptiert_vor_neu : AkzeptiertVor … = true → Akzeptiert … = true`. The tightening is inert on
everything the old checker accepted, because the old checker's own `einzelnB` demanded
`ws.Nodup` (`akzeptiertVor_nodup`), and on a `Nodup` list `getrenntW = getrenntWVor` word for
word (`getrenntW_nodup`), hence `Akzeptiert = AkzeptiertVor` (`akzeptiert_nodup_gleich`).

**So: no silent loss.** A restriction that only ever applies where the old predicate was already
`False` is not a restriction on any admitted program. The net effect on `AkzeptiertSpec` is a
relaxation in the proper sense — `AkzeptiertSpecVor → AkzeptiertSpec` is proved unconditionally
(`akzeptiertSpecVor_neu`), so every old checker is still a `Pruefer` (`pruefer_vor_neu`). The
header's phrase "both premise changes are RELAXATIONS" is therefore **accurate**, and I record
that I went looking for an overclaim here and did not find one: the `Nodup` field of the OLD
spec is what makes the implication go through, and the header says so in its point (i).

### 2.3 `Laufzeit.einmal` — a **RELAXATION**

`(init t).1 = none` became `… = none ∨ ∃ w, (init t).1 = some w ∧ Mehrfach E.ws w`. Weaker;
`laufzeit_vor_neu` proves old → new. More runs are covered, none removed. The declared arguments
are still pinned by `Laufzeit.start`, so a pool's two threads still each run a declared
occurrence.

### 2.4 Is the new acceptance vacuous, or trivially satisfiable?

No, in both directions, and each direction has a witness:

* **Not vacuous.** `pool_ziel_zeuge` — a pool of two lock-guarded workers, accepted by
  `akzeptiert_pruefer`, **both instances stepped**, `Ziel` derived from `gabbro_ziel` at `M3` of
  a real three-step run. `zPool_schreibt` shows the fixture actually writes a table, and
  `zPool_vor_abgelehnt` shows the pre-F10 checker refused it — so the statement really did grow.
* **Not trivial.** `pool_abgelehnt` — `hauptB`, which writes `privB` unguarded and non-atomic,
  declared twice, is refused, and refused **by `einzelnPoolB` specifically**: the other eight
  components are proved `true` on the same input. `pool_abgelehnt_einmal_ok` shows the same
  routine declared *once* beside another is still accepted, so the refusal is about the second
  instance and not about the routine. `poolSicher_refD_unmoeglich` shows `PoolSicher` is
  uninhabited on the reference fixture.

### 2.5 Is every previously proved conclusion still proved?

Yes. The only proof changes below `Akzeptiert_ok` are `getrenntK_of` and `schreibGetrenntK_of`,
and both were checked line by line:

* `getrenntK_of` now derives `(init t).1 ≠ (init u).1 ∨ Mehrfach ws (init t).1` from the relaxed
  `StartZulaessig.einmal` — the same disjunction the new `Getrennt` consumes. Nothing is
  discarded.
* `schreibGetrenntK_of` gained the hypotheses `hB : ∀ L, ¬ Bewacht c L` and
  `hAt : ¬ AtomarAusgenommen c`, and in the new same-routine case it uses `EinzelnPool` to derive
  a contradiction: the pool graph writes only guarded or atomic carriers, and `c` is neither.
  **The added hypotheses are not a weakening of the lemma's use site:** at the one call site in
  `Akzeptiert_ok` they are the binders of the `renn` component itself
  (`fun c hB hAt => schreibGetrenntK_of hZ hA.einzeln hB hAt (hA.renn c hB hAt)`), so nothing was
  smuggled in.

The race leg for a pool is carried where it must be: `SchreibGetrennt` still pairs only
*different* routines, so it says nothing about two instances of one routine — and that hole is
exactly what `PoolSicher` closes. The two halves fit; neither is load-bearing twice.

**F10 verdict: SOUND.** `Ziel` is unchanged in text and in content; `GabbroZiel` covers strictly
more programs, with a witness for the "strictly".

---

## 3. F11 — the new leg. Strictly stronger, or merely longer?

### 3.1 The proof is real

`kernHaltG_gilt` is not a decorative theorem. Its argument, followed step by step in
`Zielsatz/Masken.lean`, is: the lock the handler stands at is masked (`handler_sperre_maskiert`,
from `MerkInvG` propagated along the run by `merkInvG_lauf`); by *run to completion* no thread of
the handler's core stepped since the handler's first step, so `laufG_fremd` makes `f`'s trace
constant; hence `f` already held the lock at the handler's entry; which *entry only when
unmasked* forbids for a masked lock. The `¬∃ i, fs i = g` branch is handled separately against
`M0`. No step is hand-waved.

### 3.2 The vacuity hunt — and what it found

`KernPlan` is **satisfiable together with a handler that genuinely stands at a lock**, which is
the only version of the question worth asking. `masken_zeuge` (on `Korpus59.lean`) exhibits it:
two threads on one core, thread 1 takes `RING` (unmasked), the handler thread 0 then steps and
stands at `locks TAKT` (masked) while thread 1 is inside its section, `AnSperre M3 0 KLock.takt`
is proved by construction, `KernPlan` is discharged against the real traces, and the leg is
**applied** to conclude `TAKT ∉ offen ((M3.faeden 1).spur)`. Three real steps, a real lock
acquisition, a real `AnSperre`. Non-degenerate.

**What program would violate the leg?** `beispiele/gift/460`: a handler whose lock does not mask.
The model's answer is that such a program fails the leg's *masking hypothesis*, so the leg simply
does not apply to it — and `masken_disziplin_460` proves the discipline Bool refuses that shape,
while `masken_disziplin_59` accepts example 59. So the refusal lives in the Rust `H102` and in
`maskenDisziplinB`, not in `Ziel`. That is stated in the header and is honest.

### 3.3 **FINDING F1 — "STRICTLY stronger" is false. Severity: MEDIUM. (Fixed.)**

The header of `Spec.lean` said:

> `Ziel` gains a conjunct and loses none, so `GabbroZiel` is **STRICTLY stronger**

and `FIX-F11.md` repeated it. This does not survive its own next sentence. `kernHaltG_gilt` has
**no hypotheses**:

```lean
theorem kernHaltG_gilt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : KernHaltG P O passes M0 M
```

and `ziel_aus` discharges the field with it and nothing else:

```lean
keinKernHalt := kernHaltG_gilt P O passes _ M
```

A conjunct that is an unconditional theorem adds no logical content. Therefore
`Ziel_new ↔ Ziel_old` and `GabbroZiel_new ↔ GabbroZiel_old`: the statement is **logically
equivalent** to what it was before F11, not strictly stronger. It is stronger only in the
bookkeeping sense that one more fact must now be produced at the site.

This matters because "strictly stronger" is the kind of sentence a later reader spends. The leg
is worth having — it is the *reading* of a core schedule that machine G does not itself know, and
it is the model counterpart of a Rust rule that does refuse programs — but its entire program-side
content sits in its own hypotheses (`KernPlan` and the `H102` discipline), which is also why
OFFEN O19 stays open. `Spec.lean` already describes the `zeit` leg in exactly these honest terms
("holds for EVERY program of G with no premise … so it says nothing about …"); `keinKernHalt`
belongs in the same class and now says so.

**Fixed** in the follow-up commit: both the `Spec.lean` header and `FIX-F11.md` now state the
equivalence and name the two places that force it.

### 3.4 What was checked and was fine

* No premise of `GabbroZiel` moved for F11 — confirmed against the diff, which touches only the
  `Ziel` structure and the header.
* `KernPlan` is a hypothesis of the leg's own quantifier, not of the theorem, so no run was
  removed from `GabbroZiel`'s scope. A run no core schedule admits still gets the other legs.
* `hM0 : ∀ t L, ¬ AnSperre M0 t L` is met by start machines (`anSperre_start_falsch`), so the
  hypothesis is not a hidden filter.
* The NOT-CLAIMED line "the emitted C realises no masking at all (no `cli`/`sti`; `beispiele/59`
  says so in its header)" is **true**: `beispiele/59-eintritt-nimmt-maskierte-sperre.gab` lines
  15–16 say the emitter writes no `cli`/`sti` and that `masks irqs` is a promise about the
  lowering. A statement that names its own unrealised premise is the honest kind.

**F11 verdict: SOUND as a theorem; its header was OVERCLAIMED and is corrected.**

---

## 4. F9 — the clone handoff

F9's whole effect on the goal statement is **one NOT-CLAIMED paragraph**; `git show ea2d41f0 --
Spec.lean` is 5 insertions and 1 deletion, and `GabbroZiel` and `gabbro_ziel` are untouched. The
earlier O-1 Spec diff (`Deklaration.klon`, `Laufzeit.klon`, the `CloneAssume` premise) was
**dropped as vacuous** on review G11 F1 — the right call, and the rare one.

`klon_ziel` is a corollary of `gabbro_ziel` through `klonErreichbar_G` (every clone run is a G run
with the children placed at their entries). It therefore adds no premise and no strength: the
child is not a thread spawned at run time in the model, it is a **declared start that sits idle
until a live parent spawns it**. The NOT-CLAIMED line says exactly this — a spawned child reaches
`Ziel` only when the unit lists the child entry as a declared start and is accepted — and names
the two refusals that keep such units out (`LG004` in the exporter, `C185` in the emitter, both
present in the tree) and OFFEN O21. The claim is not bigger than the proof.

**F9 verdict: SOUND.**

---

## 5. The Rust/Lean correspondence claims

| Claim | Checked | Result |
|---|---|---|
| `N304` ↔ `EinzelnPool` | `fusswache2.rs:1300–1308` against `PoolSicher` | **Agrees**, with one named difference: Rust admits `guarded(c) \|\| atomic \|\| core.contains(c)`; the Lean `PoolSicher` has **no per-core disjunct**. So the Rust rule is strictly more permissive for `accumulates … per cpu`. |
| …and is that gap real? | `lean_g.rs:876` | **Neutralised and named.** The exporter refuses `ItemArt::Accumulates` by name (LG001), so such a unit never reaches (a). Named in the Spec header's F10 block and in OFFEN O17. |
| Retirement of `N315` — does the Lean Bool really accept an idle duplicate start? | `PoolSicher` on an idle routine | **Yes.** An idle routine writes nothing, so the write clause is vacuous; `haelt = []` and `gruende = 0` are already demanded of any declared start by `wurzeln`. `Getrennt`'s new self-pair is vacuous too, since an idle routine has empty footprints. The verdicts match, which is the stated point of the retirement. Gift 976 went with it and the idle twin is pinned inline. |
| Lifted `LG001` for repeated starts | `lean_g.rs:3338` | Present and reasoned against `N304`/`gabbro_ziel`. |
| `H102` ↔ `maskenDisziplinB` | `kontexte.rs:266–318` against `Zielsatz/Masken.lean` | **Plausible and consistently described, but NOT mechanically cross-checked** — see finding F2. |

### **FINDING F2 — the `H102` ↔ `maskenDisziplinB` correspondence has no guardian. Severity: LOW. Report only.**

`N304` ↔ `EinzelnPool` is backed by `pruefe-akzeptiert-diff.py`, which compares the Rust verdict
against the Lean Bool component by component on the corpus (19/19, `einzeln` included). `H102` ↔
`maskenDisziplinB` has no such instrument: it is asserted in prose in both files. Nothing is
wrong today — I read both and they decide the same condition over the handler's call-graph hull —
but it is an unpinned correspondence in the same position where the project chose to build a
guardian for the other one. **What it needs:** either a corpus probe that runs `maskenDisziplinB`
beside `H102` on examples 59 and gift/460, or a line in OFFEN O19 recording that the
correspondence is by inspection. Not fixed here: it is a new instrument, not a small correction.

### Observation (no severity) — `pruefe-akzeptiert-diff.py` reports both example 59 and 109 as
`partial (entry/boot roots)`. That is pre-existing and expected — the exporter drops `via idt` —
but it means the one corpus file the F11 witnesses are built on is *not* among the 19 programs
where the nine components are pinned. Worth knowing when reading "19/19".

---

## 6. Header lists: named assumptions and NOT CLAIMED

**Complete and true after F9/F10/F11**, checked entry by entry:

* The named-definitions list gained `Mehrfach`, `PoolSicher`/`PoolSicherW`/`EinzelnPool`,
  `KernPlan` and `KernHaltG`. Nothing new in the diff is missing from it.
* NOT CLAIMED, F10: the old "one thread per busy start (SMP-symmetric code …)" was correctly
  **narrowed**, not deleted, to "a busy routine declared ONCE on several threads", with the pool
  case and its `EinzelnPool` condition spelled out. This is the entry a weakening would have
  quietly dropped; it was not dropped.
* NOT CLAIMED, F11: handlers, cores, `via idt`, and the unrealised `cli`/`sti` — all present, and
  the `beispiele/59` claim is true (§3.4).
* NOT CLAIMED, F9: the run-time-spawned thread, with `LG004`, `C185` and O21.
* Every OFFEN citation in the new header text resolves: **O17, O18 (marked closed by F10), O19
  (narrowed by F11), O21** all exist in `dokumente/OFFEN.md`.

---

## 7. Findings, ranked

| # | Finding | Severity | Needs |
|---|---|---|---|
| **F1** | `Spec.lean` and `FIX-F11.md` called `GabbroZiel` **STRICTLY stronger** after F11. `kernHaltG_gilt` is unconditional and `ziel_aus` discharges the leg with it alone, so the new `Ziel` is **logically equivalent** to the old. | MEDIUM | **FIXED** in the follow-up commit — both places now state the equivalence, name `kernHaltG_gilt` and `ziel_aus`, and class the leg with `zeit`. |
| **F2** | The `H102` ↔ `maskenDisziplinB` correspondence is asserted in prose in both files, with no instrument, where the sibling `N304` ↔ `EinzelnPool` has one. | LOW | A corpus probe running both on 59 and gift/460, or a line in OFFEN O19 recording "by inspection". Report only — a new instrument, not a correction. |
| — | Rust `N304` admits per-core writes that the Lean `PoolSicher` does not. | none (named) | Already named in the Spec header and OFFEN O17, and neutralised by the exporter's LG001 refusal of `accumulates`. No action. |
| — | `beispiele/59` is `partial` for `pruefe-akzeptiert-diff.py`, so the F11 witness corpus file is outside the 19 pinned programs. | none (informational) | No action. |

**No UNSOUND finding. No silent loss of an accepted unit. No degenerate witness. No non-standard
axiom.**

---

## 8. The follow-up commit

Documentation only; no proof, no definition and no Rust code changed. `Spec.lean`'s header
paragraph for F11 and the corresponding paragraph of `FIX-F11.md` now say that the new `Ziel` is
logically equivalent to the old, name the two places that force it, and put `keinKernHalt` in the
same class as `zeit`. Rebuilt after the edit: `lake build` green.
