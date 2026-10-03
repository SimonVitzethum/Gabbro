# MUSE-REPORT-886: Optimiser rule — LEA selection rule

Lane 886, clone `/home/simon/Dokumente/gabbro-muse/a886`, branch `muse/886`.
Owned files only: `grammatik/Grammatik/X86/OptLeaSel.lean` (new),
`grammatik/Grammatik.lean` (one appended import line), this report.

## What was done

Proved the LEA selection rule lemma (DESIGN §7 row "Flags-aware
peepholes", §3A tile: `LEA` for `a + b*k + c` with `k` in {1,2,4,8} —
pure, no flags, no memory event) as a generic rule lemma over
arbitrary values with validator-decided side conditions, reusing only
accepted vocabulary (`Typen`, `Syntax`, `Semantik`, `ReferenzB`,
`X86.Typen`, `X86.Wort`, `X86.AddressEncoding`, `X86.LeaPureForm`).
No source/checker/Spec/goal/emitter edits, no new numbers, no
friend-reserved files touched.

New definitions: `LeaCert` (skala/disp/lebendigOk/keinToken),
`leaZulassen`, `leaCertFuer`, `LeaRewrite` (dst/basis/index/skala/
disp/art/cert — the local rewrite record), `leaRewriteForm`,
`leaMulLo`, `leaMulHi`, `leaFensterLit`, `leaFensterAdd`.

New theorems (all `#print axioms` clean, see below):
refusals/admission: `leaVerweigert_skala`, `leaVerweigert_disp`,
`leaVerweigert_lebendig`, `leaVerweigert_token`,
`probe_leaZulassen_ok`, `leaCertFuer_verweigert_skala`,
`leaCertFuer_verweigert_disp`, `probe_leaCertFuer_ok`;
scale: `probe_skala_admitted`, `probe_skala_drei`,
`probe_skala_fuenf`, `leaSkala_kodiert`;
refusal case: `leaRewriteForm_drei_verweigert` (scale 3 admits no
`adrOk` form — the rule must NOT fire, no SIB byte could encode it);
value identity: `imin_selbst`, `imax_selbst`, `leaMulLo_selbst`,
`leaMulHi_selbst`, `leaWert_identitaet` (scaled form computes
base + index*scale + displacement as words — why non-address values
may use LEA);
word bridge: `wortOfNat_add`, `wortOfNat_mul`, `leaWort_bruecke`;
step purity: `leaSchritt_wert`, `leaSchritt_flags`,
`leaSchritt_speicher`;
TARGET `OptLeaSel_verbindung` (13 conjuncts: value, `execEnd`
outcome, both `orte = []`, admission, SIB round trip, word image,
target identity, LEA computes the source value, step value/flags/
memory, width-exact read-back) with companion
`OptLeaSel_verbindung_zeuge` (jointly inhabited: `8192 + 1*8 + 5`
on table-writing `refD` beside memory-changing reached run `MB`,
fetched LEA computing `8205`; non-degenerate).

Value/fault/observation coverage: `execEnd` equality carries fault
(`logik`/`hardware`), contracts (same env values), call logs (no
call either side), concurrency (both `orte = []`, proved), budget
(same block shape, pure unbudgeted computation); both windows are
integer-only so no float rounding scope is entered (IEEE untouched).
Nothing derives `ensures`, no refusal becomes a warning, no faulting
form is speculated (no divisor/load/float in either window).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`.
`OptLeaSel_verbindung` and `_zeuge` depend on axioms
`[propext, Classical.choice, Quot.sound]` — exactly the standard
`gabbro_ziel` set; every other new theorem uses a subset. No
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere in the
file. `gabbro_ziel` itself was not re-proved here; it is untouched
(no `grammatik/` file except the import line changed, build green).

## What remains open

Per CUTS in the file: silicon correspondence; new codec rows;
TSO/GX bridge (no LEA memory event exists to transfer); the
lowering-pass certificate (when a pass may pick the form —
layer B/C); instruction-level ADD/SHL comparison (pilot `Befehl`
has no `shl`/`imul`/`lea`); the formal level-(c) work bound;
anything beyond the window (ABI/loader/entry/budget).

## Task feedback

Nothing in the task is wrong. Two remarks: (1) "prove ...
including IEEE" for an integer-only selection is honestly
discharged by integer-only windows plus outcome equality (a
separate float lemma would be decorative); (2) the DESIGN row's
flag-liveness premise is vacuous for LEA itself (it never
clobbers flags — proved) but kept as checked validator data, with
the refusal proved; the genuine refusal work is scale/shape.
The wide `OptLeaSel_verbindung` statement was iterated through
`./lean-probe` (paren balance, implicit `D Γ Λ` propagation,
`Vertrag` capitalisation — the file uses `Vertrag D` throughout).
