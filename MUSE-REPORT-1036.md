# MUSE-REPORT-1036: Exact review of author 886 (Optimiser rule: LEA selection rule)

Lane 1036, clone `/home/simon/Dokumente/gabbro-muse/a1036`, branch `muse/1036` (verified).
Owns ONLY this file. Report-only exact review; no source touched, no live controls used.

## CANDIDATE

CANDIDATE: 886 8c0bb68b06f5b745801e1cf65efedfdbd0c32095

## VERDICT

VERDICT: ACCEPT (bounded — see claim boundary below)

## What was reviewed

The pinned snapshot (`.tmp/review/SNAPSHOT.json`, base `b040b155`, identical to
this clone's HEAD): new file `grammatik/Grammatik/X86/OptLeaSel.lean` (608 lines),
one appended import line in `grammatik/Grammatik.lean` (`import Grammatik.X86.OptLeaSel`),
plus the author report. PATCH contains exactly these three files (verified
`diff --git` headers). No new diagnostic/gift/example/CLI numbers, no MARKE changes,
no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

The candidate proves the DESIGN section 7 "Flags-aware peepholes" LEA-selection
rule lemma over reused canonical vocabulary only (`Typen`, `Syntax`, `Semantik`,
`ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.AddressEncoding`, `X86.LeaPureForm`):
validator side conditions (`LeaCert`, `leaZulassen`) with all four refusals,
scale admission pins (1/2/4/8 admitted, 3/5 refused, SIB round trip
`leaSkala_kodiert` over accepted `codeSkala_skalaCode`), the recomputed-check
certificate constructor (`leaCertFuer` over accepted `skalaOk`/`leaDispOk`) with
refusal bridges, the local rewrite record (`LeaRewrite`, `leaRewriteForm`) with
the precise must-NOT-fire case (`leaRewriteForm_drei_verweigert`: scale 3 admits
no `adrOk` form), the value-identity lemma (`leaWert_identitaet`), the word bridge
(`leaWort_bruecke` via `wortOfNat_add`/`wortOfNat_mul`), executed-step purity
(`leaSchritt_wert`/`_flags`/`_speicher` over accepted `leaFormSchritt`), the
source window heads (`leaFensterLit`, `leaFensterAdd`), the TARGET connection
`OptLeaSel_verbindung` (13 conjuncts) and its joint companion
`OptLeaSel_verbindung_zeuge` (`8192 + 1*8 + 5` on table-writing `refD` beside the
memory-changing reached run `MB`).

## Independent checks performed (against live base definitions)

- Architecture vs local Intel SDM text (`.tmp/HARDWARE-REFERENCES`,
  LEA entry p. 3-547): `REX.W + 8D` for `r64` (matches accepted no-REX.W refusal,
  reused); Operation is `DEST := EffectiveAddress(SRC)` with no memory read
  (matches `adrEff` purity, `leaSchritt_speicher`, both `orte = []`);
  "Flags Affected: None" (matches proved `leaSchritt_flags`; the author's
  flag-liveness cert field is honestly documented as vacuous-but-checked).
  Scale set {1,2,4,8} is the SIB scale field; 3/5 have no encoding — refused
  at two levels (decide-probes and the `adrOk` record level).
- Canonical reuse, not a parallel model: `leaFormSchritt` keeps flags/memory by
  construction (record update touches only register/rip — read in
  `AddressEncoding.lean`); `skaliertForm` builds `⟨some b, some idx, k, d, a,
  false⟩`, exactly the tuple `leaWert_identitaet` feeds to `dispWortArt`, so the
  simp-closed identity is not a shape mismatch.
- Witness substance: `leaWitZustand` in base has `rbx = 8192`, `rcx = 1` (read);
  `refEin_schreibt`, `refB_erreicht`, `refB_schreibt` (slot 0 -> 100), `refD`,
  `refP`, `refO`, `refSp0`, `initB`, `MB`, `keinRuf`, `vertragVon`,
  `Endblock.leave`/`bind`, `RufStartF`/`RufErreichbarF` all exist with the used
  shapes; `8192 + 8 + 5 = 8205` independently matches accepted `leaWit_rechnet`.
  Non-degenerate (table-writing declaration, memory-changing reached run).
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep hits were
  only the substring "admit" inside "admitted"); every TARGET premise is used
  (`hW` via the read-back `omega`, `hw1`/`hw2` inside the window terms,
  all side-condition/register/displacement/length premises named in proofs);
  nothing derives `ensures`; no refusal becomes a warning; no faulting form
  (no divisor/load/float in either window); both windows integer-only so the
  IEEE-vacuity argument is legitimate, not decorative.
- Build evidence: full `./lean-probe` trajectory with intermediate failures
  honestly shown, final `./lean-bau` exit 0 (511 jobs), TARGET and witness at
  exactly `[propext, Classical.choice, Quot.sound]`.

## Claim boundary (bounded acceptance)

Accepted as: a source-window to abstract-`leaFormSchritt` selection rule with
validator-decided side conditions. Explicitly NOT accepted as, per the file's
own precise CUTS: silicon correspondence; new codec rows; TSO/GX transfer
(none exists — no memory event); the lowering-pass certificate (when a pass may
pick the form); ADD/SHL per-form byte comparison; the formal work bound.
Two observations, neither verdict-changing: (1) the report's "fetched LEA"
wording for the witness rests on accepted fetched lemmas (`leaWit_rechnet`),
while the file's own step conjuncts use the abstract step — substantiated but
indirect; (2) Intel raises #UD on a LOCK-prefixed LEA and the certificate has
no LOCK premise — sound within the claim because `leaFormSchritt` has no prefix
concept and byte emission sits behind the already-OPEN lowering gate.

## What remains open

Nothing assigned to this lane beyond this report. No repairs requested.
I did not rebuild the candidate in my tree (report-only scope; candidate files
are not owned here and base equals my HEAD); verification is by inspection
against live base definitions plus the candidate's complete build trajectory.
No `./lean-bau` run in this clone; no Lean files added or modified here.

## Task feedback

Nothing in the task is wrong. The pinned snapshot, owner task, build evidence
and reference manual were all present and sufficient.
