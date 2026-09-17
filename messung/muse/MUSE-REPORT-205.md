# MUSE-REPORT-205 — C read correspondence for nested arrays `[[T; n]; m]`

## What was done

New file only: `grammatik/Grammatik/CFormNested.lean` (no existing file touched,
per the wave-6 reviewer rule; see §"What remains open" for the consequences).

- `nestedRead p ci cj M N es τ` — the emitted shape `ld (idx (idx p ci M (N*es)) cj N es) τ`.
- `flatRead p ck M N es τ` — the flat shape `ld (idx p ck (M*N) es) τ`.
- `cform_nested_read` — **the lemma**: under the pinned numbers (dimensions
  `M N`, strides `N * es` / `es`, element type `τ`), per-dimension bounds
  (`0 ≤ i < M`, `0 ≤ j < N`), object start (`0 ≤ q.off`), and effect-free
  index evaluations (`hp hi hj hk`, each returning the same state), the
  emitted nested read evaluates exactly as the flat slot read at
  `flachIndex N i j` — the model's cell of `M[i][j]` (`eval_nestIdx`).
  Proof: `ev_idx_nested` (`Verschachtelt.lean`) for the address, then one
  definitional `show` step through `ld` and `rw`. Every premise is used
  (all feed `ev_idx_nested`); no premise quantifies over program syntax.
- `cform_nested_read_zeuge` — **the witness**: all premises instantiated
  jointly at `M = 3, N = 4, es = 4`, `M[1][2]` vs flat element 6
  (`uint32_t M[3][4]`), proved by `rfl`/`decide`, conjoined with the
  non-degeneracy fact `nvZelle 6 (…) = some 7` from `nv_lauf`
  (`Verschachtelt.lean`: 12-cell table `nvD`, `nvBlock` writes cell 6 —
  a table some function writes, with a memory-changing step).

## Verification

- `./lean-probe grammatik/Grammatik/CFormNested.lean`: 0 errors.
  `#print axioms` for both theorems: exactly `[propext, Classical.choice,
  Quot.sound]` (standard three).
- `./lean-bau`: green, "Build completed successfully (268 jobs)."
  (Note: the new file is not yet part of that build — no import added, see below.)
- Planted-defect check (statement broken once, then reverted): with `hk`
  swapped to `flachIndex (M : Int) i j` (row stride `M * es` instead of
  `N * es`), `lean-probe` fails red with 2 errors:
  - line 43: `hk` has type `… flachIndex (↑M) i j …` but `ev_idx_nested`
    expects `… flachIndex (↑N) i j …` (application type mismatch);
  - line 79: the witness `rfl` fails since `6 ≠ flachIndex 3 1 2 = 5`.
  After revert: green again. Soundness shown by red-on-defect, not claimed.

## What remains open / where the task as written could not be followed

1. **No `import Grammatik.CFormNested` added to `grammatik/Grammatik.lean`.**
   The task asks for it, but the wave-6 reviewer rule ("do not change any
   existing file") forbids touching `Grammatik.lean`. So the file checks
   green standalone via `lean-probe` but is not in the `lean-bau` closure.
   The merger should add the one import line; nothing else is needed.
2. **`pruefe-cformen.py` shows no nested-array-read row as lemma — because
   the table has no such row.** The only array-read row is `expr:array-read`
   (`FORMS` line 227, empty lemma list; `KNOWN_UNCOVERED` line 282:
   "`constTab_read` covers static const tables only"), and the aggregate
   rows are a different absence (O16). Flipping a row to lemma would require
   editing `instrumente/pruefe-cformen.py` (adding e.g.
   `"expr:nested-array-read": (["cform_nested_read"], …)` plus classifier
   handling to separate `A[i][j]` from flat `A[i]`), which is also an
   existing file. I did not do that under the reviewer rule. The lemma name
   `cform_nested_read` is chosen so the row can name it directly.
3. **Memory content is still uncovered by construction.** The lemma proves
   address equality through the load; what the loaded value *means* for a
   mutable static (`corrW` for a `T a[M][N]` object) does not exist yet —
   only `constTab_read` (read-only) does. The file's `CUTS` block states
   this: the nested read inherits the pre-existing uncovered
   `expr:array-read` for its content until a flat static-array read lemma
   exists. The deliverable-1 claim "the C read denotes the model slot
   read" therefore holds at the address/offset level, not yet as a
   `corrW`-level value correspondence — stated plainly, not oversold.

## Anything believed wrong in the task

- The task says the lemma "must flip the nested-array-read row to lemma",
  but no such row exists in `pruefe-cformen.py`; the premise that the row
  is there is wrong (or belongs to a parallel lane's edit).
- The task's "Do NOT edit … `MARKE_EMIT*`" + "add the import" + the
  reviewer rule "do not change any existing file" cannot all hold; I
  obeyed the reviewer rule and documented the one-line merge step.
