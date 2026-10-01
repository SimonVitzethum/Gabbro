# MUSE-REPORT-298: Independent review of candidate 282 (X86/Ganzzahl.lean)

Scope: candidate 282 only, at pinned snapshot (SNAPSHOT.json: HEAD
126cd7b4b1a48a80b78e815cc0a74138eaeafe87, base dd02d912, clean).
Reviewed the exact snapshot copies under .tmp/review/author-282/
(MUSE-REPORT-282.md, PATCH.diff, Ganzzahl.lean, OWNER-TASK.md,
BUILD-EVIDENCE.json). No other clone read, no code edited.
This clone (muse/298) is clean; canonical X86 files are unchanged
between the author's base and this HEAD (empty diff --stat), so the
probe below runs against the same Typen/Wort/Speicher the author used.

## Method

- Read the full 499-line snapshot file, every definition and proof.
- Ran `./lean-probe .tmp/review/author-282/grammatik/Grammatik/X86/Ganzzahl.lean`:
  `== 0 error(s) in the COMPLETE output`, all `#print axioms` standard
  (`[propext, Quot.sound]`, one `[propext]`-only).
- Checked PATCH.diff covers exactly the 3 SNAPSHOT.json files; the
  Grammatik.lean hunk is one additive import line, nothing else.
- Grepped the snapshot for forbidden tactics (only `#print axioms` hits),
  for source-syntax quantification (`Vertrag|Stmt|Endblock|ErgExpr`: none)
  and ZEUGE targets (owner task has none).
- Recomputed every boundary-probe value independently in python3
  (max*max high 0xFF..FE / low 1, shifts, sar, mulHighU b8 0xFE).
- Checked Flags field order in Typen.lean (cf pf af zf sf of): the
  `Flags.mk` uses in and64/or64/mul_gueltig_existenz match it.

## Verified true (no finding)

- All proved theorems are true; final build evidence is consistent:
  `./lean-bau` exit 0, 0 error lines, 369 jobs. Intermediate red probes
  in BUILD-EVIDENCE.json are dev history, final state green (reproduced).
- Report inventory matches the file: andB_b64, orB_b64, notB_b64,
  and64_cf/of/af, or64_cf/of/af, and64_gueltig, or64_gueltig, mulLow_b64,
  mulHighU_null_links, mulLow_null_links, mulTrag_heisst,
  divU_verweigert_bei_null, divU_antwortet_bei_nichtnull,
  divS_verweigert_bei_null, divS_verweigert_min_durch_neg1,
  schiebeZaehler bounds/period, shlB/shrB_b64_null,
  shlB_b64_breite_ist_null, mul_gueltig_existenz,
  mul_unbestimmt_unbeschraenkt, schiebe_gueltig_existenz, passtU/S_heisst,
  all decide probes, ganzzahl_speicher_sonde.
- Every proof-relevant premise is used; no Prop-typed premise, no
  discarded hypothesis, no assumed conclusion, no contract quantified away.
- Memory probe is genuine: shlB .b64 1 3 (= 8) through permission-checked
  write64, read back via read64_nach_write64, byte observably changed
  (0x00 -> 0x08 at base). Reuses trunc/sext/writeBytesN_hit, no new
  word/register/state types.
- No _zeuge obligation: no theorem quantifies over program syntax and the
  owner task names no ZEUGE target. The report's claim on this is correct.
- CUTS honestly disclaim encodings, source correspondence, cost, TSO/GX,
  hardware verification. No binary-validation overclaim.
- Non-findings checked and dismissed: shrB omits `trunc` but is harmless
  (value < 2^b.bits keeps high bits zero); narrow `% 32` mask is
  hardware-accurate for all narrow forms (5-bit mask), so the report's
  "judgement call" framing is over-cautious, not a defect.

## Findings (all reproduced; fix required)

R1 (material): `SchiebeGueltig` (snapshot lines 166-171) is correct only
for b64 but takes no width, so it misclassifies narrow shifts twice:
(a) both OF side-conditions measure `schiebeZaehler .b64 c` while the
value ops mask per-width. Failing value: raw count c = 33 gives b64-mask
33 (OF treated as undefined) versus narrow-mask 1 (hardware defines OF).
A snapshot with `ueberlauf = none` and arbitrary OF satisfies the
relation for a case where hardware pins OF.
(b) `f.sf = sfTest s.ergebnis` reads bit 63. Failing value:
`sarB .b8 0x80 7 = 0xFF` (proved in probe_sar) has 8-bit sign bit 1 but
bit 63 = 0, so the relation demands `f.sf = false` where 8-bit SF = true.
(zfTest/parityEven are width-correct; only SF and the OF conditions are
wrong.) Fix: add `(b : Breite)` to `SchiebeNachweis`/`SchiebeGueltig`,
use `schiebeZaehler b c` in both OF clauses and the width-correct sign
test (`negB b`) for SF; or restrict the relation to `.b64` by name and
type. `schiebe_gueltig_existenz` (lines 337-345) must follow the same
parameter.

R2 (required cleanup): `TeilFehler` with `durchNull`/`quotientUeberlauf`
(lines 75-78) is dead: zero references outside its own definition
(grep confirmed). `divU`/`divS` report refusal via `Option none`, so the
cause is never surfaced. Fix: return the cause from the division defs or
delete the inductive; do not leave both side by side.

R3 (required scoping): `mulTrag`/`MulGueltig` (lines 147-153) present the
unsigned-high-nonzero rule as THE MUL carry, but the file also delivers
signed `mulHighS`. Failing reuse: `mulHighU .b8 0xFF 0xFF = 0xFE`
(≠ 0, so `mulTrag = true`), while the signed reading (-1 * -1 = +1)
fits in 8 bits, so hardware IMUL reports CF = OF = 0. Fix: scope
`MulGueltig` to unsigned MUL by name and doc, or add a signed variant
built on `mulHighS` (carry iff high half is not the sign extension).

## Open / not bugs

The CUTS-block items (encodings lane 279, source bridge 277, cost,
TSO 274/284, silicon verification) stay open as labelled. R1-R3 are not
labelled cuts: R1 states an exactness ("OF pinned exactly when the count
is one") the code does not deliver for narrow widths.

## Task remarks

Nothing in the owner task or this review task appears wrong. No
delegation, no Rust work, no source/Spec changes, no network. Only this
report file is committed.

CANDIDATE: 282 126cd7b4b1a48a80b78e815cc0a74138eaeafe87
VERDICT: REPAIR
