# MUSE-REPORT-100 (lane 100, D2: thread-separation facts by computation)

## What was done

New file `grammatik/Grammatik/Trennung.lean` (registered as
`import Grammatik.Trennung` at the end of `grammatik/Grammatik.lean`),
closing lane D2 of `dokumente/SATZKARTE.md` §8: `PCMarkSep` /
`PCUnsharedSep` (the goal family's `hMSep` / `hCSep`) and the `hNurG`
shape of `eigenzustand_nur_eigene_schritteD_rep` are decided by
computation over atom lists.

New definitions (all `Bool`, all computable over atom lists):

- `markSepB (code) (prog) (fs)` — no code named by one listed thread's
  text is named by another's (diagonal passes).
- `unsharedSepB (prog) (fs)` — a carrier reached from two listed
  threads' texts is declared shared (`D.geteilt` / `D.ggeteilt`).
- `nurGB (t) (g) (prog) (fs)` — no listed thread other than `g` names
  `Sum.inl t` in any atom.
- `koerperMarken (tabs) (globs) (b)` — the marks named in a function
  body (flattened atoms' marks, the traversal `progAus` uses).

New theorems:

- `markSep_aus_B`, `unsharedSep_aus_B`, `nurG_aus_B` — soundness over a
  general `prog : PCProg D`: `Bool = true` plus coverage
  `hcov : forall h, h notin fs -> prog h = []` implies `PCMarkSep` /
  `PCUnsharedSep` / the `hNurG` shape.
- `markSep_aus_B_progAus`, `unsharedSep_aus_B_progAus`,
  `nurG_aus_B_progAus` — the exact task shape, conclusions over
  `Extraktion.progAus P fcode tabs globs` (one-line instantiations).
- `marke_aus_progAus_in_koerper` — a thread's extracted marks sit in its
  function's body marks.
- `pcMarkSep_aus_verschiedenen_funktionen` — structural special case
  (see deviation below).
- `pcMarkSep_scheitert_geteilte_marke` — one mark named by two threads'
  texts already breaks `PCMarkSep`, over an arbitrary text.
- `refB_prog_abdeckung` — coverage for the witness program, proved from
  its definition.
- `markSep_aus_B_zeuge`, `nurG_aus_B_zeuge` — rule-13 companions (see below).

## Last `./lean-bau` result line

`Build completed successfully (54 jobs).` with
`== 0 error line(s) in the COMPLETE output`.
Every main theorem depends only on `[propext, Classical.choice,
Quot.sound]` (printed at the end of the file, visible in the build log);
no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is
used by its proof.

## Rule-13 witnesses

`markSep_aus_B_zeuge` and `nurG_aus_B_zeuge` instantiate ALL premises
JOINTLY on `refD` / `refB_prog` with `fs = [0, 1]`, both Bools evaluated
by `decide`. Non-degeneracy rides along in the same existential:
`einzahlen` writes `konto` (`refEin_schreibt`) and the reached PC run
moves memory (`refB_pc_erreicht`, `refB_pc_schreibt`). An extra
`example` checks `unsharedSepB refB_prog [0, 1] = true` by `decide`
(shared `konto`, silent thread 0).

## Deviation from the task (stated plainly, per rules 4 and 12)

1. The structural theorem as sketched — "distinct threads run distinct
   functions and every mark named in a body has a nonzero code implies
   `PCMarkSep`" — is FALSE: two distinct function bodies may name the
   SAME mark (hence the same code), exactly as two same-function threads
   do. `pcMarkSep_scheitert_geteilte_marke` mechanizes this gap, and it
   is the same failure `pcMarkSep_scheitert_gleich_fn`
   (MarkenInstanzA.lean) already proves for shared texts. The proved
   `pcMarkSep_aus_verschiedenen_funktionen` therefore carries the
   load-bearing premise `hDisj` (distinct function bodies name marks
   with distinct codes) and drops the nonzero-code premise, which is
   load-free for `PCMarkSep` (zero collides like any other code; nothing
   in `Einfaedig` exempts it). Same-function threads stay excluded (B8).
2. The soundness theorems take an explicit thread list `fs` (DATA, not a
   proposition) plus the coverage side-condition `hcov`. This premise is
   unavoidable, not a weakening: `Faden` is `Nat`, hence infinite, so no
   decidable check can range over all threads. On the witness `hcov` is
   proved from the program definition, not assumed. The general-`prog`
   statements are strictly stronger than the `progAus` sketch; the
   `..._progAus` corollaries give the exact sketched shape.
3. Membership tests over `D.Tab ⊕ D.Glob` run through `List.any` with
   `DecidableEq`: list-membership `Decidable` needs `BEq` in this
   toolchain and no `BEq` instances exist for declaration components.
   `Nat`/`Faden` membership uses `decide` directly.

## Rust checker survey (required by the task)

- Carrier/unshared separation: YES — `pruefe_ungeteilt` in
  `crates/gabbro-check/src/bau.rs:303` evaluates the W5 premise
  (`pruefeUngeteilt`: every unshared carrier is reached by at most one
  thread) over fuel-bounded reachability; called beside the `H013`
  verdict in `crates/gabbro-check/src/geteilt.rs:785`, currently pinned
  silent (decides nothing observable).
- Cross-thread mark separation: NO — nothing in `crates/` checks that
  two threads' texts name disjoint mark codes. `marken_pruefen`
  (`m1.rs:2886`) is about conversions/labels, not threads; linear-mark
  separation lives only on the Lean side (`Marken.lean`,
  `MarkenInstanzA.lean`).
- Own-state text fact (`nurGB` shape): NO Rust equivalent found.

## What remains open

- Tying `fs`/`hcov` to a checker thread table (which threads the
  checker spawns) — stated, not shown (see CUTS).
- Establishing `hDisj` per program from the mark→code map (finite
  per-function-pair check) — the decision procedure is `markSepB`; the
  structural theorem is the human-readable special case.
- Same-function threads (B8): needs per-thread mark instances plus
  per-thread carrier instances (MarkenInstanzA.lean groundwork).
- Cosmetic: one linter warning (`unusedSimpArgs` on `h1` in
  `refB_prog_abdeckung`) — verified load-bearing (dropping `h1` leaves
  the match unsolved; dropping `hh` does too), kept with a comment.
