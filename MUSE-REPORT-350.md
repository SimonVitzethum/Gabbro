# MUSE-REPORT-350: Organisation plan C6 — AtomicPayload

Lane 350, branch `muse/350`. Owns ONLY `grammatik/Grammatik/X86/AtomicPayload.lean`,
one additive import at END of `grammatik/Grammatik.lean`, and this report.
Reviewer: lane 388.

## What was done

New file `grammatik/Grammatik/X86/AtomicPayload.lean`
(namespace `Gabbro.Grammatik.X86.AtomicPayload`, ~360 lines): the checker half of
QUELLBRUECKE section 3.3 (shared atomics) plus the duty-side audit of the atomic
fragment. Everything is generic over every declaration/program; no source admission
was tightened, no canonical vocabulary edited, no second IR/executor built.

Reused (never redefined): `AkzeptiertSpecX`/`FussSX`/`GeteiltV`/`GeteiltA`/`LogikPflichtA`
(`Zielsatz/Spec.lean`), `HavocA`/`havocA_mono`/`havocA_id`/`idA` (`Speichermodell/AtomarSem.lean`),
`KoerperGutSA`/`InvGutSA`/`InvGutGrundA` + mono lemmas (`Speichermodell/AtomarRec.lean`),
`vertragsFreiB`/`vertragsFreiB_ok`/`geteiltVB` (`Zielsatz/AtomarAkzeptiert.lean`),
`atomarB_iff` (`Speichermodell/AtomarZeuge.lean`), canonical `istIn`/`istIn_iff`,
`waechterVon`/`waechterVon_mem`, `fussOrteG`, `invOrteP`, `PaarungAusgenommen`,
`AtomarAusgenommen`. The bridge `nutzerA_aus_quelle` side was audited, not edited.

### New definitions

- `atomarFussB (P) (fs) (f) (c) : Bool` — decided footprint-membership check for an
  admitted shared atomic at one footprint: `istIn (fussOrteG P f) c && atomarB c &&
  (waechterVon c).isEmpty && vertragsFreiB P fs c`. (`geteiltVB` decides admission
  WITHOUT the footprint conjunct; the footprint side is the new checker-half piece.)
- `pD : Deklaration` — `nD` with one publication (`konfig` atomic publishes `zaehler`
  made non-atomic). No in-tree fixture has a payload (`nutzlast` is empty everywhere);
  this is the smallest declaration that has one. Only `atomar`/`nutzlast` move, plus a
  re-supplied `ggeteilt_bewacht` (its TYPE mentions `atomar`, so `nD`'s proof term does
  not fit; new proof from the everywhere-false `ggeteilt`).

### New theorems (each premise used by its proof)

1. `atomarFussB_ok` — check true implies footprint membership, `AtomarAusgenommen`,
   guard absence, `VertragsFrei`. Witness `atomarFussB_ok_zeuge`.
2. `geteiltV_von_atomarFuss` — check + full enumeration + `¬ GetrenntR P ws c` gives
   `GeteiltV P ws c`. Non-locality stays an explicit Prop premise (no syntax Bool
   decides the call closure). Witness `geteiltV_von_atomarFuss_zeuge`.
3. `vertrag_erwaehnung_verweigert` — PROVED Prop refusal: a carrier in any `requires`/
   `ensures`/owed invariant is neither contract-free nor admitted. Witness
   `vertrag_erwaehnung_verweigert_zeuge` (on `AtomarXZeuge.vP`, `kern` ensures
   `konfig == 3`).
4. `vertrag_bool_verweigert` — same refusal as Bool: both `vertragsFreiB` and
   `atomarFussB` are `false` under a full enumeration. Witness
   `vertrag_bool_verweigert_zeuge`.
5. `audit_pflicht_deckt_aufgenommen` — duty-side audit: `LogikPflichtA` over `GeteiltA`
   transfers to `GeteiltV` via the mono lemmas (narrowing, never re-proving, never a
   guessed contract). Witness `audit_pflicht_deckt_aufgenommen_zeuge` (via `n1_logikA`).
6. `audit_beobachtung_menge` — rely policy: an atomic environment preserves the whole
   trace and every non-rely carrier (observations as SET, never narrowed). Witness
   `audit_beobachtung_menge_zeuge` (identity environment in the fixture rely class,
   preservation firing at every read list/world).
7. `nichtatomar_verweigert` — a non-atomic carrier is refused everywhere (not excepted,
   check false, never admitted). Covers every publish payload (payloads are non-atomic
   per the P3 verdict reading in `ausgenommenB`). Witness `nichtatomar_verweigert_zeuge`.
8. `nutzlast_braucht_restbeweis` — a publish payload is not an admitted atomic even
   beside an atomic publication; the hand-off needs its residue proof. Witness
   `nutzlast_braucht_restbeweis_zeuge` over `pD`.
9. `atomar_nichtleer` — shared non-degeneracy: `hauptA` writes `tabA`, and a W run from
   the zero memory reaches `konfig = 3` (start memory has 0): a memory-changing run
   through the guard discipline (no lock anywhere; the atomic carries the sharing).

Every `_zeuge` instantiates ALL premises jointly on concrete values. Run-statement
witnesses (memory-changing reached run) are at `nP`; the pure checker-side refusals
(`vertrag_*` on `vP`, `nutzlast_*` on `pD`) carry the written-table leg, documented in
the file: they share `nD`'s tables/functions, and the run leg over those is witnessed
at `nP`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/AtomicPayload.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 error lines, `Build completed successfully (386 jobs)`,
  `Built Grammatik.X86.AtomicPayload`, `Built Grammatik`.
- `#print axioms` for all 8 main theorems: subsets of
  `[propext, Classical.choice, Quot.sound]` (most `[propext]` or `[propext, Quot.sound]`;
  full list in build log). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- `gabbro_ziel` axiom probe (`./lean-probe .../BeweisAtomar.lean`): still exactly
  `[propext, Classical.choice, Quot.sound]` (also `gabbro_ziel_gx`, `gabbro_ziel_sc_aus`,
  `gabbro_ziel_verbund*`).

## What remains OPEN (also as CUTS in the file)

1. Per-access x86-TSO refinement into W/GX (lane 274 business); no multi-byte
   atomicity / LOCK/RMW correspondence claimed.
2. Source bridge constructing duties for atomic-bearing units from `Pflichten src`
   (`nutzerA_aus_quelle` covers atomic-free units only); this file audits the duty to
   discharge, it does not construct it.
3. Plain-payload hand-off residue proof.
4. Shared IR (lane 287) consumed as pending interface, never invented.

## Notes for the reviewer (things in the task I read strictly)

- "Decided footprint-membership checks" (plural): delivered as ONE check with four
  decided conjuncts plus the per-conjunct projections of `atomarFussB_ok`. The
  footprint conjunct itself is the canonical `istIn (fussOrteG P f)`, deliberately not
  re-wrapped: a second name for the same Bool would be a duplicate register.
- `n1_konfig_geteilt.1.2.2` is used as the `¬ GetrenntR` witness component; the
  non-locality fact itself is NOT re-proved (it is a Prop over the call closure).
- Name trap found while working: `vP` over `vD` sits directly in `Gabbro.Grammatik`
  (`ZielOrtVollZeuge.lean`), so the bare name does NOT mean the atomic fixture's `vP`;
  the file qualifies `AtomarXZeuge.vP` / `AtomarXZeuge.vertrag_atomar_echt` explicitly.
- `omit [DecidableEq D.Fn] in` must precede the docstring (Lean parses `docstring +
  omit` as an error); the file follows the `AtomarAkzeptiert.lean` order.
- `pD`'s `ggeteilt_bewacht` cannot reuse `nD`'s proof term (dependent field type
  mentions `atomar`); proved from the everywhere-false `ggeteilt` instead.
- No TSO/flag/division/float/cost content was manufactured: the file makes no claim
  about target bytes at all, per the safety corrections (refusal Bool = admission,
  never a hardware fault).
