# The goal theorem as ONE reviewable Lean statement -- plan

*Written 2026-09-14 at the folder owner's request. Why: Lean makes a PROOF unanswerable,
not a STATEMENT. Both 2026-09-14 verdicts, and probes A and D before them, found theorems
that were true and said the wrong thing. The remedy is not more theorems. It is one short
statement of the goal that a human can read in an hour, with everything the kernel cannot
judge gathered into it and nothing else.*

## 0. The goal, in the owner's words

> A Gabbro user who wants to formally verify a Gabbro program proves only their OWN logic
> plus named hardware assumptions; everything else -- memory safety, data-race freedom,
> contracts holding where claimed in concurrent runs, and time -- is carried by the language.

## 1. Two files, one of them the review target

| File | Content | Size budget | Who reads it |
|---|---|---|---|
| `grammatik/Grammatik/Zielsatz/Spec.lean` | ONLY definitions and the statement `gabbro_ziel` (as `def GabbroZiel : Prop`); imports only the model's DEFINITION files, never a proof file | ≤ 300 lines of its own | the human reviewer |
| `grammatik/Grammatik/Zielsatz/Beweis.lean` | `theorem gabbro_ziel : GabbroZiel`, assembled from the existing flagship theorems | any | the kernel |
| `grammatik/Grammatik/Zielsatz/Proben.lean` | the anti-vacuity obligations (§4) | any | the kernel |

`Spec.lean` compiles without `Beweis.lean`. A reviewer therefore reads the statement and the
definitions it names, and nothing that merely proves. §5 lists those definitions.

## 2. The statement (shape; names final when written)

```lean
def GabbroZiel : Prop :=
  ∀ (D : Deklaration) (P : Programm D) (S : SperrInv D) (Q : AxEns D) (fs : List D.Fn),
    -- (a) what the CHECKER decides: one Bool, exactly what the Rust checker computes
    Akzeptiert P S fs = true →
    -- (b) what the USER proves: per function, for every budget (no prover-chosen knob)
    NutzerPflicht P S Q →
    -- (c) what the HARDWARE is assumed to do: named, nothing else
    ∀ (O : Orakel D), HardwareAnnahmen O Q →
    -- (d) for EVERY start and EVERY run -- nothing chosen by the prover
    ∀ (passes : Nat) (sp : Speicher D) (init : Faden → Σ f, Env D (D.params f)),
      StartZulaessig P S sp init →
      ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M →
        Ziel P S O passes M
```

**`Ziel P S O passes M` bundles the four legs of the goal, and nothing else:**

| Leg | Conjunct | Today's theorem |
|---|---|---|
| memory safety | every access is typed and in range by construction; every guarded access holds its guard (`HeldIn`) | `Expr`/`Stmt` typing, `zugriff_haelt`, `rufG_haelt_statisch` |
| data-race freedom | every pair of accesses to a guarded carrier by different threads is ordered | `rennfrei_g_voll`, `keine_datenrasse_g` (stated on runs, the conjunct quantifies over the run M lies on) |
| contracts where claimed | `VertragAmOrtG`, `SperrInvG`, `InvAmOrtG`, `StartEndeG`, `KeinLogikHaltG` | `ziel_ort_mehrfaden_ende` (+ the `passes` fix, §3) |
| progress | no deadlock; every stop is named (awaits visibility, a hardware outcome) | `keine_verklemmungG`, `ziel_ort_sperre_fortschritt` |
| time | every frame's own steps ≤ its declared `costs` | `frame_schritte_beschraenkt`, `kosten_passt_deklaration` |

**Quantifier discipline, the lesson of probes A and D:**
- Everything the prover could pick to empty an obligation is universally quantified: `passes`,
  the oracle `O` (restricted ONLY by `HardwareAnnahmen`), the start memory `sp`, the start
  assignment `init`, the run.
- The premises are exactly three groups: (a) decided by the checker, (b) the user's own logic,
  (c) named hardware assumptions. A premise that fits none of the three is a finding, not a
  premise.
- `NutzerPflicht` quantifies over every `passes` itself (probe D), and no premise names a
  specific program.

## 3. What the statement needs that is not on master yet

1. **`passes` quantified** (probe D). An Opus agent is doing this now.
2. **`Akzeptiert` as ONE Bool**, the conjunction of the decidable premises:
   - `programmImFragmentG`;
   - the current footprint `FussS … (lokK P K)` with the call-graph closure `AbgK`;
   - lock floors `StufenM`;
   - `SperrInvOk`;
   - `StartExklusiv` in its finite form.

   Where a premise is a Prop today, it gets a Bool and a `_ok` equivalence. The call graphs
   `K` are computed inside `Akzeptiert` from `P` (`reachB`), not supplied.
3. **One flagship that carries all legs at once.** Today they are separate theorems with
   slightly different premise sets (e.g. `keine_verklemmungG` needs start functions without
   signature locks, and race freedom is stated on runs). `Beweis.lean` reconciles them. Where
   a premise set does not fit, that is a finding, reported in the file's CUTS.
4. **Floats**: `Ziel` is stated over the model as it stands when the float switch lands. Until
   then the float step is an opaque-Float computation and is named as such in the review list.

## 4. Anti-vacuity, built in (Proben.lean)

- `gabbro_ziel_zeuge`: every premise holds JOINTLY on a non-degenerate CONCURRENT program. The
  program has two active threads, a shared carrier under a lock with a non-trivial invariant,
  private tables and a memory-changing run, and it is written as a `.gab` and exported by
  `gabbro lean-g`, not hand-built.
- Refutations, each a theorem:
  - **probe A** (`ensures false` everywhere) violates `NutzerPflicht`;
  - **probe D** (`forever … leave` with `ensures false`) violates `NutzerPflicht` for some
    `passes`;
  - a program that breaks a table invariant violates `NutzerPflicht`;
  - an unguarded shared write violates `Akzeptiert`.
- Positives: probes B/C (contracts over shared state at a lock boundary, readers in a `locks`
  block) satisfy all premises.
- **Corpus measurement:** the number of `beispiele/*.gab` programs whose export satisfies
  `Akzeptiert` by `decide`. Booked next to the chain count.

## 5. The review package (what a human must read, and only that)

`Spec.lean` itself, plus the definitions it names, listed with file and line in the file's
header. Expected list:
- machine G (`RufMaschineG.lean`: states, `RufSchrittG`, `RufStartG`, `RufErreichbarG`);
- the sequential semantics the obligation is stated over (`execEndH`);
- `KoerperGutS`, `InvGutS`, `GutO`, `RegLokal`, `AxVertragO`, `SperrInvOk`;
- `VertragAmOrtG`, `SperrInvG`, `InvAmOrtG`, `StartEndeG`, `KeinLogikHaltG`, `GeordnetG`,
  `kostenTief`;
- `Akzeptiert` and its components.

For every entry the header gives one sentence in plain words: what it says, and what it would
mean if it were wrong. The package also carries the four review questions:
1. Does `Ziel` say the four legs of the goal, and nothing weaker?
2. Is every premise in exactly one of the three groups?
3. Can any premise be satisfied by choosing something the user controls, so that an
   obligation becomes empty? (Probes A/D are the known instances.)
4. Does machine G run what the language means?

The last question is where translation validation (PLAN-UEBERSETZUNGSVALIDIERUNG.md) takes over
for the C.

## 6. What the statement deliberately does not claim

These are named in the header, not hidden:
- termination and a waiting bound under fairness;
- the C and the hardware (that is the closing theorem's job, per program);
- weak memory beyond the named DRF-SC premise;
- floats until the switch;
- starvation freedom.

Adding any of them later extends `Ziel`, and each extension is reviewed as a diff of
`Spec.lean`.

## 7. Order and owners

1. **Now:** the `passes` fix (Opus, running).
2. **`Spec.lean`**, definitions and statement only: **Opus**, directly after (1), because the
   statement is the part where "green" does not mean "right". Review by me against §2 and §5
   before any proof work starts.
3. **`Akzeptiert` as a Bool** with `_ok` equivalences: a Muse lane (bounded, decidable
   plumbing), in parallel with (4).
4. **`Beweis.lean`** assembling the flagships: Opus.
5. **`Proben.lean`** and the corpus measurement: a Muse lane, then an Opus check of the probes'
   statements.
6. **Two independent verdicts, third round**, run AGAINST `Spec.lean`: is this the goal?
7. **External human review** of the §5 package. It is the first point where outside review has
   a lever on a few hundred lines instead of the whole tree.

**Effort:** (2) half a day, (3) one day, (4) one to two days, (5) half a day, (6) half a day.
About 3–4 days of work, with (1) and the float switch as the only dependencies.

## 8. Extensions of the goal (noninterference, liveness, higher-order contracts): the rules

*Added 2026-09-14 after an external review of the three proposed extensions.*

**The criterion is counted per OBLIGATION, not per feature.** "Stays in the carried fragment"
means every premise belongs to the checker, the user's logic, or a named hardware/runtime
assumption. The measure of whether an extension keeps that promise is `gabbro obligations`:
how many of the obligations the extension generates the checker discharges, and how many it
hands to the user. The number is booked BEFORE and AFTER each extension, on its examples and on
the corpus. An extension that stays in the fragment nominally but moves most of its obligations
into user logic has left it in practice. For noninterference this is the deciding number: it is
the product promise only if the checker supplies its premises.

**One assumption list.** Every runtime or hardware assumption goes into the SAME named list:
- the lock primitives (acquire/release, happens-before);
- thread creation;
- the idle root;
- a FIFO or ticket lock for the waiting bound;
- the scheduler class for noninterference;
- DRF-SC;
- the IEEE float unit;
- the device answers;
- the C compiler.

Today they sit in A1–A5 (`schlusssatz_104`), PLAN-UEBERSETZUNGSVALIDIERUNG §3(b), GLEITKOMMA.md
and the goal theorem's `HardwareAnnahmen`. `Spec.lean`'s header is the one place that lists
them all.

**Noninterference: two statements, and the customer sentence written down first.**
- The first theorem is schedule-parametric: the same scheduler choices and the same inputs of
  domain B give the same B-observation. It is the right first theorem, and it is weaker than
  the product promise, because the scheduler is a channel.
- The customer-facing sentence needs a scheduler class whose decisions do not depend on other
  domains' state, for example a fixed-timetable partition scheduler (seL4's configuration).
- The sentence is written in NICHTINTERFERENZ.md in the exact form in which it is TRUE, next to
  the form that is false: "tenant A learns nothing about tenant B on a dynamically
  load-balanced machine" does not hold under a load-based scheduler. It is written before
  anyone else writes it.
- Declassification (controlled release) decides whether the flow rule is usable at all. It
  weakens the statement to delimited release, and that is where this extension costs work.

**Liveness: measure the number from the first example.**
- "Waiting ≤ the sum of the `held` times of the threads ahead", with a FIFO/ticket lock as a
  named runtime assumption.
- Composed over nested locks, the bounds recurse. Ranks make the recursion terminate, but they
  do not keep it small: it grows multiplicatively over rank levels.
- The bound is computed and booked on every example from the start. The theorem alone does not
  count as done: a green theorem over a number nobody can put in a data sheet is not a result.
  `beispiele/01`'s `costs <= 839680 ops` is the known precedent one level down.

**Higher-order contracts: variance, and effects on the type.**
- Refinement of a function against a pointer type's contract is contravariant in `requires`
  and covariant in `ensures`. The wrong direction is unsound, so a poison probe must catch it.
- A driver or scheduler callback speaks about world state, so the pointer type carries
  `effects` and `costs`. The function's effects must be a subset of the type's and its costs at
  most the type's. The checker decides both; the pre/post implication is user logic.
- Through pointers the call graph is no longer static. Every pass that closes over it (frames,
  effects, cost sums, lock order) joins over all admissible candidates (`KandOk`). The
  summaries get coarser, and the ceremony and cost numbers are expected to jump. They are
  booked when the extension lands.
