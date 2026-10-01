# Audit: FLOAT-SIMD — accepted `Gleitprofil` / `Vektor` implementations and concrete consumer gaps

*Owner: lane 412. Owns only this file plus `MUSE-REPORT-412.md`.
Status: adversarial implementation audit, not a proof and not a design change.
No Lean module, checker, Spec, goal, Rust, emitter, Typen/execution/codec or
friend path is touched here. Full source-to-final-byte validation remains OPEN.*

Scope: the two accepted modules `grammatik/Grammatik/X86/Gleitprofil.lean`
(lane 286, review 302) and `grammatik/Grammatik/X86/Vektor.lean` (lane 290,
review 306), read against the actual source float surface
(`Typen.lean`, `Semantik.lean`, `Gleitkomma.lean`), the canonical pilot
(`X86/Typen.lean`: 14 integer/control `Befehl` constructors, no float form),
`X86/Speicher.lean`, and the consumer tasks that need them (A6 ScalarFloat
lane 340 working, reserve lanes 424 FeatureProfile / 425 FloatExceptions /
426 VectorFootprints, C4 EntryState lane 348). Prior architecture reviews
(`FLOAT-ZEIT.md` lane 278, `REVIEW-OPT-BINAER.md` §§2.9/3, `REVIEW-TSO.md`,
`REVIEW-QUELLE-INVARIANTEN.md` §9) are cited, not repeated: every section
below names file/theorem/line evidence in the *current implementation* and
the *concrete consumer gap* it leaves.

Method: read both files in full (653 / 651 lines), reproduced positive and
negative probes with `./lean-probe` (0 errors, see §7), checked each CUTS
claim against what the file actually proves. Verdict pattern used throughout:
"correct within its stated claim" vs "genuinely missing bridge work" vs
"false semantics" — no finding of the third kind was made; inventing one out
of an explicitly OPEN bridge would be audit noise and is not done here.

## 1. binary64 source surface — the width gap is measured, not closed (no bug)

Source facts (unchanged, off limits): `GFloat` is `GBits f64`
(`Typen.lean:82`); `Ty.fl` carries no width and the model computes every
float in binary64 (`Typen.lean:79-82`, `Semantik.lean:399`); `gleitRechne`,
`bruch`, `gleitAusInt`, `gleitPasst`, `gleitRoh` are all f64
(`Typen.lean:88-114`, `Semantik.lean:351-352,625-654`).

`Gleitprofil` §6 states the consequence as theorems, not prose:
`f32_rundet_16777217` vs `f64_trennt_16777217` (lines 399-406),
`gegenbeispiel_werte` / `gegenbeispiel_muster` (409-430), and
`quelle_gegen_f32` (436-443: the source model computes `2^24+1` where
genuine binary32 computes `2^24`). The CUTS block (lines 568-576) names the
extension this profile prepares and does not perform (width in `Ty.fl`,
width dispatch in `gleitRechne`/`bruch`/`gleitAusInt`, per-width values,
binary32 correspondence rows). Reproduced: `ofInt f32 16777217 =
ofInt f32 16777216` and the f64 inequality both `decide` clean
(`.tmp/probe412-float-simd.lean`, 0 errors).

Audit verdict: **correct within its stated claim.** The `fadd32/fsub32/
fmul32/fdiv32` wrappers (lines 260-277) are standalone model applications
with well-formedness theorems per op per width (300-347); nothing in the
file links them to source `Ty.fl` execution, so no consumer can mistake
them for a closed lowering. The one hard rule for consumer A6 (lane 340):
every `float` (f32) node must be **refused at the bridge** until path (a)
or (b) of `FLOAT-ZEIT.md` §4.3 is proved — the task text already says this
(WORK-ALLOCATION A6: "every `float` (f32) node refused at the bridge"),
and this audit confirms the refusal has a measured reason
(`quelle_gegen_f32`), not a missing measurement.

No repair in this module. Missing bridge work is owned elsewhere: P1 below.

## 2. Floating control word and per-context state — admission check correct, dynamics OPEN (no bug)

Implemented and proved: `mxcsrBit` (22), `mxcsrRundungRNE` (25-26, RC bits
13-14 clear), `mxcsrMaskenAlle` (30-32, bits 7-12 set), `mxcsrGueltig`
(36-37: RNE + FTZ bit 15 off + DAZ bit 6 off + all masks set, sticky bits
0-5 explicitly NOT read). Five decided verdicts: `mxcsr_standard`
(`0x1F80 = true`), `mxcsr_ftz_verweigert`, `mxcsr_daz_verweigert`,
`mxcsr_runde_unten_verweigert`, `mxcsr_maske_verweigert` (40-52).
Per-context state: `FPKontext` owns one word (61-63), `kontextReset`
(`0x1F80`, 66), `sichere`/`stelleHer` as pure data movement with the two
round-trip theorems (75-80), `kontextReset_gueltig` (83),
`kontext_nicht_global` (87-89: valid and refused words coexist as two
contexts — the per-context reading `FLOAT-ZEIT.md` §4.2 items 1/7 demands).
Reproduced: `mxcsrGueltig 0x1F80 = true`, `0x9F80 = false` by `decide`.

Sticky flags are an explicit gap, proved as a gap: `mxcsr_sticky_egal_*
(99-104) show the verdict ignores bits 0-5 in both directions, and CUTS
(584-587) says accumulation/clearing/reads are unmodelled. That is the
honest shape — the verdict is an *admission* check, and the correspondence
must carry sticky flags as reserved-unobserved-or-matched
(`FLOAT-ZEIT.md` §4.2 traps paragraph), which is consumer work, not this file.

Audit verdict: **correct within its stated claim; dynamics legitimately
incomplete.** What is genuinely absent (consumer gaps, not defects):

- No `LDMXCSR`/`STMXCSR` enumeration, no entry-establishes / writer-preserves
  chain (`FLOAT-ZEIT.md` §4.2 items 1/7, phase-B `establish_mxcsr_entry` +
  `preserve_ldmxcsr`). There is nothing to enumerate *against* yet: the
  pilot `Befehl` has no float or control-state constructor
  (`Typen.lean:53-67`, confirmed by grep: zero float/XMM/SSE/FMA matches
  outside `Vektor.lean`'s "not extended" comments).
- No XMM register file anywhere (both files say so explicitly). Handler
  save/restore (XMM + MXCSR) and upper-YMM discipline are therefore not
  statable yet — owned by C4 EntryState (lane 348) + A6, not repairable here.
- Bit positions (RC 13-14, FTZ 15, DAZ 6, masks 7-12, sticky 0-5) are stated
  from the Intel layout and proved *consistent* (reset accepted, each bad bit
  refused), never verified against silicon — CUTS (581-583) says exactly
  this. A hardware-profile datum, not a theorem defect.

No repair in this module. Missing bridge work: P0/P2 below.

## 3. Signaling NaNs — trapping/quieting unmodelled, classification correct (no bug)

Model facts (`Gleitkomma.lean`): `klasse` (77-83) answers `.nan` for *any*
nonzero fraction at max exponent — there is no quiet-bit distinction.
`add/mul/div` propagate the NaN *input bits* (`| .nan, _ => a`, lines
226-229, 244-247, 272-275); only *computed* NaNs are canonical `nanQ`
(payload 1, line 217). CUTS in the model file (line 1147-1148) and in
`Gleitprofil` (588-591) both state: no quiet-bit discipline.

Consequence reproduced in `.tmp/probe412-snan.lean` (0 errors): an
SNaN-shaped payload `⟨false, bexpMax, 4⟩` (quiet bit clear, payload bit set)
classifies as plain `.nan`, and `add f64 snan +0` returns the input bits
unchanged — i.e. **no trap, no quieting, no invalid-flag raise exists in
the model.** `nan_nutzlast_offen32` (455-462) proves classification pins no
payload; `nan_klasse_berechnet32` (465-467) proves `0/0` classifies NaN.

Audit verdict: **correct within its stated claim; the SNaN semantics is a
named OPEN bridge, not a false theorem.** No theorem concludes a payload,
a trap, or a flag — so none is false. The consumer obligation is precise
and jointly owned: A6's NaN relation must stay class-level AND prove
`nan_payload_unbeobachtbar` (non-observability over source-observable
behaviour: NaN never inhabits `Gleit lo hi`, `flt/fle` answer `false` on
any NaN) AND carry the sticky-flag reservation as a joint premise — because
silicon quieting raises invalid *and* changes bits, neither half alone
suffices (`FLOAT-ZEIT.md` §4.3). Admitting any bit-observing form (float in
memory read as integer, `STMXCSR` reader in image) re-opens that lemma.
Reserve lane 425 (FloatExceptions) is the natural owner of the SNaN/flag
half; A6 owns the class-level relation. P1 below.

A reviewer trap to avoid: calling `add`'s `| .nan, _ => a` arm "wrong
because hardware quietens SNaN" mistakes the model's stated propagation
policy for a hardware claim. The file never claims hardware correspondence
(`SSEAdd32Entspricht` is a `def`, lines 472-474, with NO theorem concluding
it — §7 CUTS equivalent at 577-583). The defect would only exist if a
consumer cited `add` as executed-SSE behaviour without the
non-observability lemma; no such citation exists today.

## 4. Exceptions, rounding modes, FMA/contraction — refused by absence, correctly (no bug)

- The model is RNE-only: every op is "exact result, then round-to-nearest-
  even" (`rundeBruch`/`rundeExakt`); no rounding-mode parameter exists.
  `Gleitprofil` admits only RNE words (§2). Other modes (round-down refused
  at `mxcsr_runde_unten_verweigert`), x87/FPCR, `ROUNDSS/ROUNDSD`,
  `CVTSS2SI` non-truncating conversions are out of scope in both files'
  CUTS. Consistent: there is no second rounding the code secretly uses.
- No FMA/fused op exists in `Gleitkomma.lean` (grep: zero `fma`/fused
  matches), no contraction parameter, no fused wrapper in `Gleitprofil`.
  `FLOAT-ZEIT.md` §4.2 item 3 requires refusing *encoded* fusion
  (`VFMADD*SS/SD`) unless a contracted source form with its own
  model/checker/certificate is admitted. Today there is no float encoding
  at all, so the refusal is vacuous-but-correct: nothing admits a fusion.
  Consumer A6 + decoder work must make the refusal syntactic the moment the
  first float `Befehl` constructor lands (its task already lists
  "x87/FMA/packed encodings refused syntactically").
- Exception masks: the profile demands all six set (traps off); an unmasked
  image is outside the model. But no theorem connects "masks set" to "no
  trap fires" — correctly so, since no instruction semantics exists to
  fire a trap. The C-side `Hardware.ieee` vocabulary is untouched, and the
  goal's float range failures are user-logic `Logik.bereich`, not a stop
  (`FLOAT-ZEIT.md` §3) — nothing here invents a new stop kind.

Audit verdict: **no false semantics; the exception/rounding/FMA story is a
set of consumer-side syntactic refusals waiting for the first float
`Befehl`.** The ordering constraint that matters now: A6 must premise
*every* scalar op correspondence on `mxcsrGueltig` (checked
establishes/preserves per §2), and the `CVTTSS2SI/CVTTSD2SI` saturation
wrapper for `gleitRoh` plus the `UCOMISD`-NaN-`false` rows must be proved
as correspondences, not inherited from the model. P0 below.

## 5. SIMD integer lanes — lane separation and tearing treatment correct (no bug)

`Vektor.lean` models packed 128-bit *integer* words only (8/16/32/64-bit
lanes over canonical `Wort`/`Breite`), with the header (12-16) and CUTS
(583-599) stating: no XMM file, `Befehl` untouched, no FP SIMD, admission
refused. Proved:

- Exact packing: `laneCount_bits` (every width packs exactly 128 bits),
  `vecVal_proj`/`laneGet_mk` (pack-then-read round-trip), per-lane
  add/sub/xor/and/or correctness against canonical `addB`/`subB`/`xorB`/
  trunc (`laneGet_add/sub/xor/and/or`, 247-294), no inter-lane carry/borrow
  (`vecAdd_allein`, `vecSub_allein`, 298-309) with decided boundary
  witnesses (`0xFF+1` wraps while the neighbour adds independently, 450-491).
- Memory carriage as two ordered canonical 64-bit chunks: `vecWrite`/
  `vecRead` (369-378), permission preservation (381-388), per-chunk refusal
  lemmas (391-402), read-after-write (406-422), byte frame (425-433), and —
  load-bearing for every future vectorisation consumer —
  **`vecWrite_teilt` (438-446): the intermediate state after the first chunk
  is observably mixed (low half new, high half old).** Reproduced via
  `#check @vecWrite_teilt` (probe prints its statement, 0 errors). Per-byte
  TSO is not multi-byte atomicity, and this file proves the negative
  instead of assuming the positive. `vecJoin_split` (323-334) and the
  nonzero two-chunk witness `vecWrite_read_zeuge` (513-571, observably
  changes memory) close the data half.

Two precision notes (consumer gaps, not defects):

- **Wrap behaviour is inherited, not strengthened.** `vecWrite` carries no
  `OhneUmbruch16` premise; it defers to `write64`'s `schreibbar8`, whose
  footprint arithmetic wraps mod 2^64 (`Speicher.lean:135-146`; `OhneUmbruch`
  is a proof precondition for frame/read-back lemmas, `Speicher.lean:158-
  160`, not a refusal in the definition). The vector read-back theorem
  `vecRead_nach_write` correctly demands `hno : OhneUmbruch16 a`, so any
  consumer chaining it must discharge no-wrap — the natural home is the B2
  overlap/alignment checker (merged) or lane 426's footprint work. Do not
  "repair" `vecWrite` by bolting on a wrap refusal: that would fork the
  scalar convention (which also defers) into two registers.
- **Tail/upper-lane discipline does not exist yet.** The 128-bit word is
  exact-width (no tail bits inside it), but there is no YMM upper-lane state,
  no VEX zeroing-vs-preserve distinction, no alignment requirement, and no
  fault-order / concurrent-visibility / tearing-correspondence / budget /
  `FolgeG` lemma — all listed in CUTS (593-598) as required before any
  admission. The 128-bit non-atomicity result is exactly the lemma the TSO
  bridge needs as input (per-access granularity), not a replacement for it.

Admission posture verified: `simdFreigabe : Bool := false` (578) with
`simd_gesperrt` (581); any admission must edit the definition, so it cannot
slip in silently. The five gates named there (source correspondence, fault
order IR-VALIDIERUNG §3 9a, visibility 9b, tearing 9c, FP control 9d,
concurrent observations, budget transfer) match the consumer lanes. **No FP
lane exists**, so float-SIMD admission is not even statable — correctly
refused by absence. Reproduced: `simdFreigabe = false := rfl`.

## 6. Prioritized necessary repair / missing bridge tasks

Nothing below asks `Gleitprofil`/`Vektor` to change. P0 is the one ordering
constraint; P1-P3 are consumer-side bridge work with owners.

- **P0 — A6 ScalarFloat (lane 340, working) must keep the three refusals
  syntactic from the first constructor:** (i) every `float`/f32 node refused
  at the bridge (§1, `quelle_gegen_f32` is the reason); (ii) FMA/x87/packed/
  AVX encodings refused syntactically, one source op = one machine op, no
  reassociation/`x-x→0`/`0*x→0`/reciprocal peepholes (§4, `REVIEW-OPT-BINAER`
  §2.9 already books these as validator refusals); (iii) every scalar op
  correspondence premises checked `mxcsrGueltig` establishes/preserves per
  execution context (§2). If 340 delivers float `Befehl` constructors with a
  bare stability assumption ("nobody changes MXCSR") instead of the checked
  chain, that is a finding against 340, not against this audit's modules.
- **P1 — NaN/SNaN joint lemma (A6 + reserve 425 FloatExceptions):**
  class-level FP relation + proved `nan_payload_unbeobachtbar` (both
  `Gleit lo hi` gating rows and the `flt/fle`-`false`-on-NaN rows) + sticky-
  flag reservation as joint premise covering SNaN quieting + raised invalid.
  Acceptance criterion: a bit-observing form or `STMXCSR` reader in a
  validated image re-opens the lemma by name. No model change needed.
- **P2 — Control-state dynamics (C4 EntryState lane 348 + A6 + reserve 424
  FeatureProfile):** entry-establishes MXCSR/XMM, enumerated `LDMXCSR`/
  `STMXCSR` preserves, handler save/restore contracts, CPUID-gated profile
  (scalar-SSE2 baseline; packed/AVX/FMA refused while unadmitted). Note the
  layering: establishment is validator-checked image data + binding-logic
  contracts (user logic), silicon behaviour under the entry value is the
  only hardware assumption.
- **P3 — Vector footprints and cost (reserve 426 VectorFootprints, C3 CostSummary
  lane 347, TSO bridge owners):** 128-bit access footprint/tail treatment
  reusing B2's checker (discharge `OhneUmbruch16` at the validator, §5 note);
  per-access tearing correspondence against the TSO bridge table (consuming,
  not repeating, `vecWrite_teilt`); two-chunk spill/fence/budget accounting
  (no constant absorbs the two accesses; unbounded retry nowhere hidden).
  FP lanes are a separate extension after scalar-f64 correspondence — never
  a peephole on top of integer lanes.

Explicit non-tasks (do not file as defects): hardware verification of MXCSR
bit positions; cycle bounds or benchmark claims (none exists, none claimed);
`Ty.fl` width extension (reviewed Spec diff, separate lane); C-emitter float
rows (legacy backend, untouched).

## 7. Verification log

| Check | Result |
|---|---|
| Isolation (`pwd`, toplevel, `muse/412`) | pass, before any edit |
| Owned files only (this audit + report) | pass — no Lean/Rust/checker/Spec/emitter/friend file touched |
| Full read `Gleitprofil.lean` (653 lines) + `Vektor.lean` (651 lines) | done, with CUTS cross-check |
| Source surface (`Typen.lean:79-114`, `Semantik.lean:288-302,351-352,625-654`, `Gleitkomma.lean` defs) | confirmed by direct read/grep |
| Pilot `Befehl` has no float form (`Typen.lean:53-67`) | confirmed by direct read + grep (zero SSE/FMA/XMM matches) |
| No FMA/fused op in model (grep `fma`/fused over `grammatik/Grammatik/`) | zero matches — §4 refusal vacuous-but-correct |
| `./lean-probe .tmp/probe412-float-simd.lean` | **0 error(s)**, exit 0 — reset word accepted, FTZ refused, f32 conflation / f64 separation, NaN-payload openness, `simdFreigabe = false`, `#check @vecWrite_teilt` + `@SSEAdd32Entspricht` print |
| `./lean-probe .tmp/probe412-snan.lean` | **0 error(s)**, exit 0 — SNaN-shaped payload classifies `.nan` with silent bit propagation; sticky flags verdict-neutral both directions |
| Prior reviews (`FLOAT-ZEIT.md`, `REVIEW-OPT-BINAER.md` §§2.9/3, `REVIEW-TSO.md`, `REVIEW-QUELLE-INVARIANTEN.md` §9) | cited for obligations, not duplicated — all findings above are implementation-anchored |
| Lean build / cargo / emission runs | none — docs-only audit task; no code changed, nothing to rebuild |

*Probes stay private in `.tmp/` per the task (experimental evidence, not
corpus files). No `sorry`/`admit`/`axiom`/`native_decide` anywhere in this
lane's work — there is no new Lean module, only `decide`/`rfl` probe
examples in scratch.*

## CUTS (of this audit)

- No hardware claim: MXCSR bit positions, silicon rounding, trap delivery,
  SNaN quieting behaviour, CPUID data and cycle timing are profile inputs,
  never verified here.
- No new correspondence: `SSEAdd32Entspricht` remains a named unproved `def`;
  no float `Befehl`, decoder, TSO float lemma, image theorem or cost
  transfer is proved or claimed here.
- Line numbers are as-read at write time and may drift; theorem names are
  the stable reference.
- Consumer lanes (340, 348, 424, 425, 426, 347) are task assignments, not
  completed work; their obligations stay OPEN until reviewed integration.
