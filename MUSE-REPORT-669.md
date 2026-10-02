# MUSE-REPORT-669: Exact review of author 668 (IEEE scalar operation and conversion byte rows)

Lane 669, clone `/home/simon/Dokumente/gabbro-muse/a669`, branch `muse/669`.
Owns only this report. No source touched (a temporary reproduction copy was
fully reverted; `git status` clean before this commit).

CANDIDATE: 668 b54e99304574395b644041845aa94ededc1b876d
VERDICT: ACCEPT

## 1. What was reviewed

Pinned snapshot (`.tmp/review/SNAPSHOT.json`, base
`1d08711596ee4e493b13f146a4f861e28a69761d`, clean): one new file
`grammatik/Grammatik/X86/ScalarFloatHardwareForms.lean` (2203 lines, 73 defs,
148 theorems), one additive umbrella import, author report
`MUSE-REPORT-668.md`, plus `OWNER-TASK.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`
(50 command records). I read the module end to end (lines 1-2203).

## 2. Mechanical gates: all pass

- Bans: zero `sorry`, zero tactic-`admit`, zero `axiom`, zero `native_decide`,
  zero `unsafe`. The 11 `admit` string hits are English prose ("admitted
  domain/profile"). Nine plain `decide`s close closed goals (allowed).
- Rule 4: zero `intro _`, zero `have _ :=`, no `forall rho/v` contract
  quantification, no `Prop`-typed premises, no `variable`/`section` tricks.
  Spot-checked premise use: `cvttAdapter_gueltig` (w, t, ht, hlo, hhi all
  used), `fpHwByteschritt_arithRR_rechnet` (hf, hform, hfp, hgate, hout all
  used), `fpHwFetchDekodiert_erfolg` (all used). `fpHwByteschritt` takes ONLY
  the state; no caller-supplied decoded form becomes evidence.
- Rule 13: no theorem quantifies over `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/
  `Expr`/`Args`, so no `_zeuge` is owed. Joint non-degenerate evidence exists
  anyway: W1 `fpHwW1_div_speichert` and W2 `fpHwW2_cvtsi_speichert` are reached
  two-step fetched runs with a proved real memory change plus readback
  (`fpHwW1_aendert`/`fpHwW1_liest`, W2 twins).
- `CUTS:` block present and honest; 50 `#print axioms` lines present.
- Patch integrity: `PATCH.diff` = one additive import hunk in
  `grammatik/Grammatik.lean` plus one new-file hunk; nothing else touched.
  No friend-reserved optimiser path, no source/checker/Spec/goal/emitter file.

## 3. Provenance: verified against the local Intel snapshot

Checked `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
(325462-093US): SUBSD `F2 0F 5C /r`; CVTTSD2SI `F2 0F 2C /r` (r32) and
`F2 REX.W 0F 2C /r` (r64); CVTSI2SD `F2 0F 2A /r` and `F2 REX.W 0F 2A /r`;
UCOMISD `66 0F 2E /r`; MOVSD `F2 0F 10 /r` (reg/mem) and `F2 0F 11 /r`;
REX "must be immediately before the opcode" (prefix-first order);
masked out-of-range conversion returns `80000000H` / `80000000_00000000H`;
unordered-comparison flag shape `OF,SF,AF=000, ZF,PF,CF=111`. All match the
file's stated contract. The author's REX-order finding against accepted
`VectorCodec.encodeVector` (`[vectorRex op, natByte 102, ...]`, REX before the
66 prefix) is accurate in this clone and correctly bounded: recorded for the
coordinator only, filed as no soundness bug (lane 597 CUTS = self-consistency),
file not owned, not touched.

## 4. Architecture: decoder accept-set audited arm by arm

- Every ACCEPTED form is silicon-meaningful with the modelled semantics:
  F2 arithmetic (W=0), 66 UCOMISD (W=0), REX.W=1 conversions, F2 MOVSD
  load/store/copy; ModRM mod=11/10 with SIB-36-only and base resolution
  (rsp/r12 via SIB, rbp/r13 disp32 without SIB) consistent between encoder
  and decoder; REX.R/REX.B extend reg/r/m with the CVTTSD2SI GPR/XMM
  crossover correct.
- Every silicon-DIVERGENT neighbor refuses, several with closed pins:
  W=0 conversions (32-bit silicon semantics vs whole-register model),
  REX.W=1 arithmetic (silicon ignores W; subset pins W=0), packed shapes
  under 66 (`arith66`), MOVHPD shapes (`66 0F 16/17` fall through to none),
  register-form store, F2+2E, COMISD `0F 2F` (traps on QNaN, unmodelled),
  F3 prefix, REX-before-prefix, X=1, non-36 SIB, mod=00/01, all truncations.
- CVTTSD2SI adapter is a genuine safe refinement, not a trust assumption:
  `cvttHwGueltig` admits only finite in-int64-range inputs;
  `cvttAdapter_gueltig` proves the accepted wrapper EQUALS truncation there;
  `fpHwByteschritt_cvttVerweigert` refuses off-domain even though fetch
  succeeds (W3-bad witness). This correctly handles the silicon/model split
  (indefinite integer vs 0/saturated).
- Upper-lane effects: arithmetic register-form preserve proved
  (`fpHwByteschritt_arithRR_hoch` over all four ops); high-register execution
  witnessed (W7 `xmm15 <- xmm8`, low moves, `0xDEADBEEFDEADBEEF` upper kept).
  NaN handled at class level with explicit unordered/equal rows and reserved
  flags; payload equality never concluded -- exactly the scope the owner task
  demanded ("resolve or refuse"), and CUTS states the boundary.
- Refusal witnesses planted and proved: W3-bad (domain), W5 (unreadable data
  under good fetch), W6 (FTZ-mutated word), W8 (executable-boundary
  truncation). Pilot-disjointness pins (`fpHwPilot_weist_*_zurueck`, closed
  `decide`s against accepted `decode`) give the 660/658 consumers the
  extension-only evidence. `ExtendedExecution` untouched as required.

## 5. Reproduction (queued wrappers, then full revert)

All six module imports plus `Codec` (pilot `decode`) are byte-identical
between the candidate base `1d08711` and this clone HEAD, so a temporary copy
is faithful. With the staged file copied in plus the one import line:
`./lean-probe .../ScalarFloatHardwareForms.lean` -> `== 0 error(s) ... exit 0`
(first line), axiom prints all within standard sets; `./lean-bau` ->
`Build completed successfully (474 jobs)` (460 at author base + 14 modules
from later lanes in this HEAD). Both artifacts then removed and
`grammatik/Grammatik.lean` restored; `git status` clean before this report.

## 6. Bounded notes (no repair required)

- Silicon-valid no-REX-at-all encodings refuse (decoder always expects the
  REX byte). Conservative refusal, consistent with "unsupported encodings
  refuse", but CUTS names other subset refusals explicitly and not this one;
  integration may want one `decide` pin plus a CUTS line.
- The NaN unordered row is proved at step level (`fpHwSchritt_...`), not as
  a fetched-bytes run; MOVSD-load upper-zeroing has no fetched witness
  (W7 covers the register copy). Both inherit from accepted `fpSchritt`
  lemmas; no wrong execution, only witness coverage a later lane may extend.
- Remaining essential rows (SQRTSD, CVTSD2SI, f32 widths, packed beyond
  PXOR/PADDQ, 660/658 integration) are listed as open by the author; no
  claim exceeds the proof.

## 7. Claim boundary

ACCEPT covers: the exact pinned candidate only. It establishes
REX-aware canonical byte rows with an independent decoder, round trips,
explicit refusals, the CVTT domain adapter, the gated byte step, byte-level
IEEE observations at class fidelity, and joint witnesses W1-W8 -- all inside
standard `gabbro_ziel` axioms. It does NOT establish silicon correspondence,
raw-bit NaN fidelity, sticky-MXCSR behavior, TSO/concurrency, or any
source/checker/emitter/goal connection, none of which is claimed.
