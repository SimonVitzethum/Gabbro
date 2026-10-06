# MUSE-REPORT-1385: GabbroV bridge — the shared-atomic rely

Lane 1385, clone `/home/simon/Dokumente/gabbro-muse/a1385`, branch `muse/1385`
(verified: `.git/HEAD` = `ref: refs/heads/muse/1385`). Status: **UNMEASURED**
(Lean verification blocked, see §5). No push (lane rule). No other agent/model
calls.

## 1. Task

Family V5 `the shared-atomic rely` (TODO 0f): premise (b) of the goal is
`NutzerPflichtA` (every body against EVERY value a shared atomic read may
return), while GabbroV duties assume values of a plain read. V5 closed the
bridge only for the parser's fragment (2 of 146 units: 104, 108). Define the
duty statement of a body whose shared-atomic reads are ARBITRARY values, and
prove that it implies `NutzerPflichtA` for the parser's fragment, or prove the
precise obstruction. Required witness shape: a body with one shared-atomic
read whose result steers a branch.

## 2. What was done

NEW FILE `grammatik/Grammatik/X86/GvAtomRely.lean` (148 lines) in namespace
`Gabbro.Grammatik.X86.GvAtomRely`, plus one import line
`import Grammatik.X86.GvAtomRely` appended to `grammatik/Grammatik.lean`.
No other existing file touched. No new interpreter: `execEndHA`/`HavocA` are
reused from `AtomarSem`, never redefined. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`. English only.

New definitions (the required duty statements):

- `GvRelyDuty (P S Q T passes f)` — per-body arbitrary-values duty: the rely
  triple `KoerperGutSA ∧ InvGutSA ∧ InvGutGrundA` over every atomic
  environment in `HavocA T` (the GabbroV reading of the rely obligation).
- `GvDutyA (E)` (structure, mirrors `NutzerPflichtA`) — `logik`: every body
  meets `GvRelyDuty` over the unit's shared atomics `GeteiltA E.P E.ws`;
  `start`: `StartPflicht E`. Lock/axiom locality stays checker-side.

New theorems (all premises used by their proofs):

- `gvDutyA_gibt_nutzerA (h : GvDutyA E) (hlokS : SperrInvLokal E.S)
  (hlokQ : AxEnsLokal E.Q) : NutzerPflichtA E` — assembly of per-body
  GabbroV duties plus locality into goal premise (b). Proof: one anonymous
  constructor, definitional unfolding only.
- `gv_plain_gibt_relyDuty_parserfragment (hat : ∀ g, D.atomar g = false)
  (h : NutzerPflicht E) : GvDutyA E` — on the parser fragment (no atomic
  global; V5 `declOf_kein_atomar`, the parser elaborates `Glob := Empty`)
  GabbroV's PLAIN duty implies the arbitrary-values duty. Generic over every
  declaration (strictly more general than 104-only `oblig_nutzerA`, which it
  follows: `⟨(nutzerPflichtA_ohne_atomar hat h).logik.1, h.start⟩`).
- `gv_rely_braucht_atomfreiheit : ¬ ∀ ws f, KoerperGutS hP 0 … f →
  KoerperGutSA hP 0 … (GeteiltA hP ws) f` — the precise obstruction: without
  atomic-freedom the transfer FAILS. Proof: instantiate with `hws`,
  `NFn.zaehlB`, `hP_seq 0`; `hP_rely_nicht` closes it.

Witnesses (joint premises + non-degeneracy, per rule 13):

- `gv_plain_gibt_relyDuty_parserfragment_zeuge` — on 104's exported unit:
  `(fun g => nomatch g)` (no globals, same term as `oblig_nutzerA`),
  `oblig_nutzer` (plain duty proved), and `oblig_ruf_bewegt` (reached run
  moving memory: `einzahlen` moves slot `0 -> 100`).
- `gv_rely_braucht_atomfreiheit_zeuge` — `hP_seq 0` (sequential duty holds),
  `hP_rely_nicht` (rely duty fails), `hP_konfig_geteilt` (`konfig` shared),
  `TraegerSchreibt hauptA tabA = true` (`by decide`, same proposition as
  `atomar_nichtleer.1`), `aFuenf_havoc` (the value-5 environment is in the
  rely class). The branch-steering body is `hRumpf`: `zaehlB` stores shared
  `konfig` into `tabB[0]`, then `hTest` (`ite konfig == tabB[0]`) writes 1
  vs 2 — exactly the required witness shape (one shared-atomic read steering
  a branch); `hP_wert_A` shows the havoc drives it to 2 against ensured 1.

CUTS section and five `#print axioms` lines close the file.

## 3. Reuse (nothing duplicated)

`nutzerPflichtA_ohne_atomar` (`BeweisAtomar`), `logikPflichtA_of_frei`
(`AtomarPflicht`), `KoerperGutSA/SA` (`AtomarRec`), `HavocA` (`AtomarSem`),
fixtures `hP/hws/hRumpf/aFuenf` + `hP_seq/hP_rely_nicht/hP_konfig_geteilt/
aFuenf_havoc` (`AtomarAkzeptiertZeuge`, `NIZeuge`, `SchwachZeuge`),
`oblig_nutzer/oblig_ruf_bewegt/oO/rho7/gD/gE` (`Pflicht104`/
`GenOblig104`). Open-line mirrors accepted `AtomicPayload.lean` at the same
tree depth. Every copied proof term (`fun g => nomatch g`, `by decide` for
`TraegerSchreibt`, the `rufAt` statement) is taken verbatim from already
accepted files for the same proposition.

## 4. What remains open (not claimed)

Duty construction for atomic-bearing units from `Pflichten src` (stays with
`bruecke/`, atomic-free only); per-access x86-TSO refinement into W/GX;
payload hand-off. See file CUTS.

## 5. Blocker (why UNMEASURED)

`./lean-probe grammatik/Grammatik/X86/GvAtomRely.lean` was run FOUR times via
the queued wrapper (10 min, 60 min, 30 min, 20 min timeouts; ~120 min total):
**zero output every time** — each run killed while waiting inside the shared
`lean-slot`; no error line, no `== N error(s)` line, no olean produced
(`grammatik/.lake/build/**/*GvAtomRely*` absent afterwards). Warm cache
present (`grammatik/.lake/build/` exists). This is slot congestion (or a
stuck holder) across the ~15 live lanes, not a build result. NOTHING in the
new module is therefore claimed green: no `./lean-probe` first line and no
`./lean-bau` result line exist for it. Every proof step above is documented
against its accepted source so the exact-candidate reviewer can check it
once the slot clears. The module plus the one `Grammatik.lean` import line
were committed UNVERIFIED so that the reviewer reads exactly what was
written (dispatcher requires a clean tree); no green is claimed for them.

## 6. Commit state

- `MUSE-REPORT-1385.md`: this file (committed).
- `grammatik/Grammatik/X86/GvAtomRely.lean` (148 lines, §2) plus the one
  `import Grammatik.X86.GvAtomRely` line in `grammatik/Grammatik.lean`:
  committed as the exact review candidate, UNMEASURED (see §5). No other
  existing file touched. No `sorry`/`admit`/`axiom`/`native_decide` anywhere
  in the candidate.

## 7. Assessment of the task

The task is sound. The positive direction for the parser fragment is small
by nature (the rely is empty there — V5 S4 already knew this); the file's
value is making it GENERIC plus pinning the exact obstruction (`hP`:
sequential holds, rely fails, branch steered by the second read), which is
the precise statement future atomic-bearing duty construction must overcome.
No premise was manufactured: the fragment bridge uses atomic-freedom
essentially, and the obstruction shows it cannot be dropped. Safety was not
traded for coverage: anything beyond the fragment is stated as OPEN, not
proved.
