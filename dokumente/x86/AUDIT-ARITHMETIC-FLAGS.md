# Audit: arithmetic, flags, overflow and strength reduction (lane 404)

*Owner: lane 404. Owns only this file plus `MUSE-REPORT-404.md`.
Status: review evidence, not a proof. Full source-to-final-bytes validation remains OPEN.
No model, goal, checker, emitter or ledger change is made or claimed here.*

Scope: the accepted modules `Wort`, `Ganzzahl`, `FlagBeweis`, `StaerkeReduktion`
plus their directly wired consumers/extensions `Ausfuehrung` (`schritt`),
`MulDiv` (`mulDivSchritt`), `ShiftLogic` (shift/logic evidence) and the source
definitions they must eventually meet (`Typen.lean` `Zahl` ops, `Syntax.lean`
`Expr` constructors). Read at the checked-out master; line numbers are as-read.
Method: read every definition/theorem cited, reproduced all probes below with
`./lean-probe` (0 errors, see §6), and checked consumer wiring with a
tree-wide grep. This audit does not repeat the broad architecture reviews
(`REVIEW-GRUNDLAGEN`, `REVIEW-TSO`, `REVIEW-OPT-BINAER`,
`REVIEW-QUELLE-INVARIANTEN`, counter-review 308); it covers only what the
arithmetic/flag implementations actually state and what their concrete
consumers still lack.

## 1. Wiring map (what consumes what)

| Producer | Consumed by | Wired? |
|---|---|---|
| `Wort.add64/sub64/xor64`, `bedingung` | `Ausfuehrung.schritt` (add/sub/xor/cmp/jumpIf), step equations | Yes, proved per-form equations |
| `Wort.cfAdd/cfSub/ofAdd/ofSub/afAdd/afSub`, `parityEven`, `sext` | `Wort` itself, `FlagBeweis`, `ShiftLogic` (NEG AF) | Yes |
| `FlagBeweis.add64_of_iff/sub64_of_iff`, no-overflow/no-carry transfers | No consumer yet (optimiser/lowering) | No (correctly OPEN per CUTS) |
| `Ganzzahl.mulTragU/MulGueltigU`, `mulTragS/MulGueltigS` | `MulDiv.mulFlagsU/mulFlagsS` (+ validity proofs) | Yes, internally |
| `Ganzzahl.divU/divS`, `passtU/passtS` | Nothing | No (OPEN per CUTS) |
| `Ganzzahl.shlB/shrB/sarB`, `schiebeZaehler`, `SchiebeGueltig` | `ShiftLogic` Nachweis constructors | Yes, internally |
| `MulDiv.mulDivSchritt`, `zugelassen`, `rein` | Nothing (`Befehl`/`schritt`/decoder wiring OPEN with Typen owner) | No (stated OPEN) |
| `ShiftLogic.negWf/NegGueltig`, `logikFlags`, `andW/orW`, `ShiftOp/shiftOpWert` | Nothing (no `Befehl` forms) | No (stated OPEN) |
| `StaerkeReduktion.staerkeMul`, `mul/div/rem_pow2` value theorems | Nothing (IR lane 287 working) | No (stated OPEN) |
| `Ganzzahl.and64/or64` (+ `Wort.xor64`) | Nothing in `schritt` (pilot `Befehl` has no AND/OR forms) | No (pilot subset, stated) |

## 2. Sound within the stated claim (do not "fix")

- **CF/OF independence by construction** (`Wort.lean:100-112`): CF from
  `toNat`, OF from the three sign bits. The boundary probes pin all four
  corners independently (`probe_add_carry_no_overflow`,
  `probe_add_overflow_no_carry`, `wit_add_both_flags` in `FlagBeweis.lean:399-439`).
- **OF iff exact signed range** (`FlagBeweis.lean:124-234`,
  `add64_of_iff`/`sub64_of_iff`): proved by sign-bit case analysis over the
  three `bmod` wrap cases, no overflow equivalence assumed. The transfer
  lemmas (`add64_sint_eq_of_no_overflow`, `add64_cf_false_nat`, …) name the
  exact values a lowering may reuse. Premises all used.
- **Unsigned/signed MUL carry split** (`Ganzzahl.lean:148-149,370-373`):
  `mulTragU` vs `mulTragS` are separate by name, with the planted divergence
  probe (`probe_mul_trag_vorzeichen`: `-1 * -1` at 8 bits sets the unsigned
  carry and clears the signed one). This is the exact shape a careless
  IMUL-as-MUL peephole would get wrong, and the files refuse it structurally.
- **Division refusals with causes both ways** (`Ganzzahl.lean:262-304`,
  `MulDiv.lean:81-122`): `divU/divS_verweigerung_ursache` prove `none` iff
  divisor-zero (resp. plus `sMin / -1`); wide forms add the quotient-overflow
  refusal with the 65-bit probe (`probe_div_weit_ueberlauf`). Truncation
  direction pinned against SAR floor (`probe_idiv_rumpf`: `-7 / 2 = -3`
  remainder `-1`).
- **Signed strength reduction refused with a value** (`StaerkeReduktion.lean:121-122`,
  `ShiftLogic.lean:314-318`): `sdiv_kein_shift` and `sdiv_ist_kein_sar`
  (`-3` truncates to `-1`, shifts to `-2`). The admitted reductions keep every
  source side condition as a premise (`mul_pow2_shl`, `div_pow2_shr`,
  `rem_pow2_band`; `hw1/hw2/h0` all forwarded, divisor `2 ^ k ≥ 1` proved
  inline). The result-RANGE texture difference (rewritten `shl` range vs source
  `mul` four corners) is documented as the checker's `M104` business, values
  only — an honest cut, not a bug.
- **Undefined flags never forced false**: AF is `Option` (`none` = undefined);
  MUL/SHIFT leave SF/ZF/PF existentially unconstrained behind validity
  relations, with `mulU_unbestimmt_unbeschraenkt`-style witnesses that two
  valid snapshots differ. The MUL/IMUL "preserve incoming SF/ZF/PF" choice in
  `MulDiv.lean:135-141` and the DIV "preserve all flags" step are each
  labelled an explicit modelling choice in CUTS — correct within the claim,
  but see F3: no consumer may read those bits as hardware facts yet.
- **Width-correct sign repair honoured**: `SchiebeGueltig` (`Ganzzahl.lean:172-178`)
  and `logikFlags`/`NegGueltig` (`ShiftLogic.lean:46-50,243-244`) read
  `negB b`, with the `sarB .b8 0x80 7` regression pinned
  (`schiebe_schmal_sf_korrekt`). Note the trap in F6: the older `LogikGueltig`
  still reads bit 63.

## 3. Findings

### F1 (latent unsoundness, repair needed): zero-count shift snapshots exist although the file claims none

`ShiftLogic.lean:199-203` documents that the §2 snapshots are "the
nonzero-count profile and the zero-count case is pinned separately … (value
identity, no snapshot claimed)". But `shlNachweis_ohne_eins` /
`shrNachweis_ohne_eins` / `sarNachweis_ohne_eins`
(`ShiftLogic.lean:149-153,171-175,193-197`) require only
`schiebeZaehler b c ≠ 1`, which a masked-zero count satisfies. At `c = 64`
the masked count is 0 (hardware: flags unchanged), yet the lemma hands out a
`CF = false` snapshot. Reproduced (`./lean-probe`, 0 errors):

```
schiebeZaehler .b64 64 = 0
∃ f, SchiebeGueltig .b64 (shlNachweis .b64 1 64) 64 f ∧ f.cf = false
```

No consumer is wired yet, so nothing is miscompiled today; but the first
shift-lowering lane that cites `SchiebeGueltig` at an unguarded count inherits
a false CF fact on every masked-zero shift. Necessary repair (one of): restrict
the three `ohne_eins` lemmas (and `schiebe_gueltig_existenz` call sites) to
`schiebeZaehler b c ≠ 0`, or add an explicit zero-count preservation shape
(flags kept, value identity) and route count-0 through it. The doc sentence in
§2 already promises the second; the code does not deliver it.

### F2 (missing bridge, highest priority): no source-to-target arithmetic lowering; source is total, target wraps and traps

Source arithmetic never faults: `Zahl.add/sub/mul/div/rem/sdiv/shl/shr`
(`Typen.lean:148-353`) are total functions returning widened ranges; even
`sdiv` (`Typen.lean:258-265`) takes only the denominator-excludes-zero proof
and always answers — `INT_MIN / -1` evaluates to the mathematical quotient in
`-M .. M`. Target arithmetic wraps (`addB/subB/mulLow`), masks counts, and
traps (`divS`/`divWeitU`/`divWeitS` answer `none` → `hardwareHalt`).
Consequences, each a concrete lowering obligation with no theorem today:

1. **Wrap vs range**: `passtU`/`passtS` (`Ganzzahl.lean:188-193`) name when an
   unbounded sum fits, but no theorem connects any `eval` to any target word.
   There is no add/sub lowering at all, and no recorded policy (prove fit via
   `passtU/S`, or specify wrap). The `mul_pow2`-style value bridge is the only
   template; add/sub need the same treatment first since every address
   computation depends on it.
2. **Fault introduction**: lowering source `sdiv`/`div` to IDIV/DIV introduces
   a fault the source does not have (quotient overflow; plus the wide-dividend
   shape). The discharging proof (quotient fits / dividend constructed) is the
   bridge lane 277's business and is OPEN — this audit only records that the
   target side already provides exactly the refusal shapes the discharge must
   meet (`divS_verweigerung_ursache`, `divWeitS_verweigert_bei_oben/unten`).
3. **Fault order**: source `eval` fixes an evaluation order; target flag
   clobbering (`cmp` overwrites the full snapshot, `Ausfuehrung.lean:87-89`)
   means reordered compares change branches. No ordering lemma exists. Any
   motion/DCE over flag producers needs the `rein`-style purityextendsion to
   ADD/SUB/CMP (currently only `MulDiv.rein` marks DIV/IDIV never-pure;
   ADD/SUB/XOR/CMP have no purity/motion statement at all).

### F3 (missing consumer discipline, high): flag liveness/definedness is untracked

`md_div_erfolg`/`md_idiv_erfolg` (`MulDiv.lean:227-259`) preserve the whole
incoming snapshot; `mulFlagsU/S` preserve incoming SF/ZF/PF while those bits
are architecturally undefined. `bedingung` (`Wort.lean:151-167`) and
`jumpIf32` (`Ausfuehrung.lean:99-101`) read any flag. Nothing tracks which
bits are defined at a read: a branch on PF after MUL, or on any flag after
DIV, would read a preserved-but-undefined bit with a proved-sounding
`Flags` value behind it. The coming ControlFlow consumer (SETcc/CMOVcc read
flags) and any dead-flag elimination must carry a definedness premise per
bit; today the validity relations (`MulGueltigU/S`, `SchiebeGueltig`,
`LogikGueltig`, `NegGueltig`) are producer-side only. Suggested shape: a
`FlagsDefiniert` mask (which bits the last producer defined) threaded through
steps, with `bedingung` reads requiring the bits they consume.

### F4 (two models diverge, clarify): unmasked `shlW/shrW` vs masked `shlB/shrB`

`StaerkeReduktion.shlW/shrW` use raw `BitVec` shifts (large counts saturate
to zero); `Ganzzahl.shlB/shrB/sarB` mask the count (`schiebeZaehler`).
Reproduced (`./lean-probe`, 0 errors):

```
shlB .b64 1 64 = 1   (masked to count 0)
shlW 1 64 = 0        (saturated)
shlB .b64 1 64 ≠ shlW 1 64
```

Partly documented (`StaerkeReduktion.lean` CUTS; `shrW_breite` pins counts for
`shrW`, `shlW_keinUeberlauf` effectively excludes large counts except `x = 0`
where both agree). What is missing is a proved in-range agreement lemma
(`k < b.bits → shlW/shrW agree with shlB/shrB`) and a rule that hardware steps
cite only the masked family. The lowering lane must not mix them; recommend
canonicalizing hardware reasoning on `shlB/shrB/sarB` and keeping `shlW/shrW`
behind width pins until the agreement lemma exists.

### F5 (missing obligation, medium): dividend construction for DIV/IDIV lowering

`divU/divS` (single-width, `Ganzzahl.lean:77-98`) and `divWeitU/divWeitS`
(128-bit dividend, `MulDiv.lean:58-79`) are two unlinked models; no theorem
relates them (e.g. zero-high-word `divWeitU 0` vs `divU`). A source-`div`
lowering must construct the dividend (RDX = 0 unsigned; RDX = sign extension
signed) and the quotient-fit proof — neither construction has a statement.
`zugelassen` (admission) mirrors the step's own check, so guard/trap agreement
(`verweigert_heisst_halt`) holds, but admission is not connected to any source
range. Task: `divU`-to-`divWeitU` bridge lemmas plus dividend-setup theorems
owned by the lowering lane, not by arithmetic.

### F6 (narrow + wiring gaps, lower): booked absences with one trap

- Narrow ADD/SUB have modular values but no flag snapshots (`Wort.lean` CUTS
  books them absent; NarrowOps lane 335 is a pending candidate, not a
  foundation). Any narrow lowering currently has no flag producer to cite.
- `and64/or64` flag facts have no step consumer (pilot `Befehl` has no
  AND/OR forms) — consistent with the pilot subset, no action except keeping
  the wiring table (§1) current when forms are added.
- Trap: `LogikGueltig` (`Ganzzahl.lean:139-141`) pins `sf = sfTest r`
  (bit 63). It is correct for the 64-bit `and64/or64` results it was written
  for, but a future narrow consumer must use `ShiftLogic.logikFlags`
  (`negB b`), not `LogikGueltig`. One-line doc fix at the `LogikGueltig`
  definition ("64-bit results only") would prevent the reuse mistake the
  shift side already hit once.

### F7 (minor): `passtU` name collision

`Ganzzahl.passtU` (range predicate, `Ganzzahl.lean:188`) shares its grep
prefix with `SperreBeweis.passtU_leer/passtU_append` (an unrelated lock-step
predicate). No semantic issue; it wastes reviewer time on every textual
search. Consider renaming at the next touch of either file.

## 4. Prioritized necessary work

1. **P1 — F1**: restrict the shift `ohne_eins` snapshots to nonzero masked
   counts (or add the promised zero-count preservation shape). Blocks the
   first shift lowering; small, local to `ShiftLogic.lean`.
2. **P2 — F2.1**: add/sub value lowering with an explicit fit-or-wrap policy
   (`passtU/S` discharging to `add64/sub64` facts). Blocks every later
   lowering including address computation.
3. **P3 — F3**: flag-definedness discipline for consumers (ControlFlow reads,
   DCE/motion over producers). Blocks SETcc/CMOVcc validation and any
   flag-reuse optimisation.
4. **P4 — F2.2/F2.3 + F5**: division lowering with dividend construction and
   quotient-fit discharge; purity/motion statements for ADD/SUB/CMP.
5. **P5 — F4/F6**: in-range shift-model agreement lemma; `LogikGueltig`
   64-bit-only doc pin; keep the §1 wiring table current as `Befehl` grows.

## 5. Negative probes (what must stay refused)

All reproduced with `./lean-probe` (0 errors); the first two are new in this
audit, the rest re-confirm the files' planted refusals:

- `shlB .b64 1 64 ≠ shlW 1 64` — the two shift models diverge (F4).
- `∃ f, SchiebeGueltig .b64 (shlNachweis .b64 1 64) 64 f ∧ f.cf = false` —
  masked-zero snapshot leak (F1).
- `sVal .b64 (sarB .b64 (-3) 1) ≠ Int.tdiv (-3) 2` — shift is not signed
  division (files' claim, holds).
- `divS .b64 0x8000000000000000 0xFFFFFFFFFFFFFFFF = none` — signed overflow
  refuses while source `sdiv` is total (F2.2 cut).
- `(add64 0xFFFFFFFFFFFFFFFF 1).1 = 0 ∧ ¬ passtU .b64 …` — modular wrap
  where the range check fails (F2.1 cut).

## 6. Probe record

- `.tmp/probe404.lean` (pre-existing): carry-without-overflow, `divS`
  `INT_MIN/-1` refusal, SAR-vs-`tdiv` mismatch, wrap-vs-`passtU` cut —
  `./lean-probe`: **0 error(s), exit 0**.
- `.tmp/probe404b.lean` (this audit, private, not committed): F1 and F4
  exhibits plus the `divS` control — `./lean-probe`: **0 error(s), exit 0**.
- No Lean, Rust, checker, emitter or goal file was touched; `./lean-bau`
  state is unchanged from master (docs-only change).

## 7. CUTS of this audit

No instruction execution, decoder, encoding, memory/state transition beyond
the cited round-trips, TSO bridge, source correspondence, ABI/loader theorem,
cost transfer or final-image acceptance is proved here. Silicon behaviour
(count masks, MUL carry rules, truncation direction, parity/AF readings) is
audited as *stated* semantics against the files' own claims and probes, not
verified against hardware. Line numbers are as-read and may drift.

---

*End of audit. Findings F1–F7 with P1–P5 above are the actionable output;
§2 lists what was checked and found sound within its stated claim.*
