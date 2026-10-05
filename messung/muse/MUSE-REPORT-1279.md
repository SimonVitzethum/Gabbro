# MUSE-REPORT-1279: Bit scan and count — BSF, BSR, POPCNT, BSWAP
# (with vendor-neutrality repair of 2026-10-05)

Clone `/home/simon/Dokumente/gabbro-muse/a1279`, branch `muse/1279`
(verified first; no mismatch). Owned files only:
`grammatik/Grammatik/X86/IntBitScan.lean` (new, ~1700 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was done

New family module `Grammatik.X86.IntBitScan`, structured after the
accepted `HwMulDivWidth.lean` (dispatcher prefers the unified chain;
register-path `HwAdapter` with exact agreement) with decode style
from `ShiftLogic`/`MulDivCodec`/`ShiftCodec`:

- §1 vocabulary + canonical encoder: `BsBreite` (b16/b32/b64; no
  8-bit scan/count form exists), `BswapBreite` (b32/b64),
  `BsQuelle` (reg / raw mem with ModRM byte + displacement bytes),
  `BsBefehl` (bsf/bsr/popcnt/bswap), `BsDecodiert`, `encodeBs`
  (0F BC/BD, F3 0F B8, 0F C8+r; 66H for 16-bit, F3 for POPCNT,
  canonical REX with W/R/B).
- §2 parsing decoder `decodeBs` (single-byte legacy stages, REX,
  0F, opcode, ModRM; SIB, F2, doubled legacy and F3-on-scan
  refused; LOCK has no rule).
- §3 round trips + pins: decode-inverts-encode generally for every
  register row (`encodeBsf_decodeBs`, `encodeBsr_decodeBs`,
  `encodePopcnt_decodeBs`, `encodeBswap_decodeBs`), `bsMemOk` with
  general parse lemma `bsParseModrm_mem_ok`, `modrmMitDst_id`,
  `nimmBytes_laenge`, kernel-checked positive pins (incl. mem
  shapes), 7 no-shadow pins (`ext_weist_*_zurueck`), 16 planted
  decode refusals (`bs_nichts_*`: LOCK, TZCNT/LZCNT shapes incl.
  16-bit, bare B8, 66H/F3/F2 on BSWAP, SIB, doubled prefixes,
  truncation, missing displacement).
- §4 value semantics + step: SDM-093 reference snapshots
  (`bsFlagsScan`, `bsFlagsPopcnt`, BSWAP untouched),
  narrow-merge destination discipline (the untouched-destination
  reference was superseded by FREE since the repair, see below),
  `bswap32_merge`, `bsSchritt` with length guard and the
  reused `PopcntMerkmal` CPUID gate, per-constructor selection
  equations, feature/length/memory refusals
  (`bs_popcnt_verweigert`, `bs_ohne_merkmal_kein_ok`,
  `bs_laenge_misslungen`, `bs_bsf/bsr/popcnt_mem_misslungen`),
  step-level write theorems and lifted index/count/swap laws
  (`bs_bsf_bereich/bit/min`, `bs_bsr_bereich/bit/max`,
  `bs_popcnt_schranke/wort_schranke`, `bs_bswap64/32_invol`).
- §5 dispatcher (`BsHwInstr`, `decodeBsHw`, `bsHwLen`, three
  selection theorems, pilot/family/refusal pins) + deferred-scan
  recognizer (`istVerzoegertScan`, `bsVerzF3`, `bsVerz0F`) with
  pins and the deciding profile rule (`scanProfilUrteil` +
  `profil_urteilt_*`: supporting profile defers to the BMI lane,
  otherwise #UD; never executed here either way).
- §§6–7 machine connection: `bsSchritt_speicher`,
  `adapterBitScan` (CPUID bit as observed-answer plug parameter,
  mirroring `adapterFeatureTor`, since `PerfMerkmal` has no POPCNT
  row and no existing file may change) with wf/agreement/
  projection/refusal theorems, `bsHwRegSchritt` over the reused
  `HwRegAusgang` with selection + wf theorems (no trap in this
  family).
- §8 joint witness `bsHw_zeuge`: scan on core 0 (index 4, ZF
  clear), count on core 1 (8, ZF clear), in-place swap (flags
  kept), owner-only forwarding of byte 42, drain changing actual
  shared memory 0 → 42, zero-source ZF set (universal over all
  admissible destinations; the destination value was dropped
  since the repair), feature/length/memory/decode refusals
  beside it.
- CUTS block + `#print axioms` for 29 main theorems (21 old +
  8 new; all within propext/Classical.choice/Quot.sound; no new
  axioms).

No diagnostic/gift/example numbers taken (pure Lean lane).

## Repair of 2026-10-05 (FREE modeling as portability abstraction;
revised after independent re-review 1280, verdict REPAIR)

The three pinned vendor-specific facts were reworked; all
architecturally DEFINED results stay exact:

1. Zero-source destination is FREE: new relation
   `BsScanZulaessig` (index write + exact ZF + frame pinned,
   destination-on-zero and non-ZF flags free). The reference
   (unchanged) is proved as one admitted member
   (`bsScanNach_zulaessig`,
   `bsScan_null_unveraendert_zulaessig`); universality over all
   members proved (`bsScan_zf/index/rahmen_allgemein`); freedom
   proved real (`bsScan_null_frei`: two admissible successors
   disagree on the destination; `bsScan_flags_frei`: on CF).
   Deleted: `bs_bsf/bsr_null_laesst_liegen` (pinned the free
   choice). The witness drops the destination value and keeps
   ZF (universal).
2. Scan flags: only ZF defined. `BsScanZulaessig` pins exactly
   `nach.flags.zf = scanZF`; CF/OF/SF/AF/PF unconstrained. The
   SDM-093 cleared snapshot survives only as the reference
   member inside `bsScanNach_zulaessig`.
3. 16-bit BSWAP: refused, never valued — structurally
   unstatable (`BswapBreite` has no 16-bit constructor, decoder
   arm yields 32/64-bit only, 66H refused by pin
   `bs_nichts_bswap66`). POPCNT (all flags defined) and 32/64-bit
   BSWAP stay exact.
- CUTS rewritten for neutrality; `#print axioms` extended to
  the 8 new main theorems (all standard).
- Previous verdict is stale: the changed candidate needs a fresh
  independent review (coordinator assigns; lanes never review
  themselves).

## Re-review fixes (R1–R4 of report 1280, this commit)

- R1: the admissibility comment no longer claims Intel leaves
  the destination/flags undefined and no longer claims AMD
  behavior. It states the Intel-defined facts with extract
  lines (destination unmodified ll. 42739/42822; full flag row
  ll. 42755-42758/42838-42840) and marks FREE an explicitly
  beyond-evidence portability abstraction; no AMD reference is
  claimed (`REFERENCES.json` bars it).
- R2: the AGENTS.md standing-rule citation is removed from CUTS
  and this report (no such rule exists in this tree); the FREE
  modeling cites the repair instruction itself and no rule.
- R3: this report now describes one candidate (current head):
  superseded corrections above are marked historical.
- R4: counts fixed — 29 `#print axioms` lines (21 old + 8 new,
  incl. the added `bsScan_rahmen_allgemein`), 16 `bs_nichts_*`
  decode refusals; `popNull` is now used in code (concrete
  agreement pins `pin_popnull_scanZF_voll/null`: count-zero and
  source-zero agree on `0xFF` and `0`, no general equivalence
  claimed).

## Verification (after repair)

- `./lean-probe grammatik/Grammatik/X86/IntBitScan.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (659 jobs).`
- Forbidden tactics: none (`sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`/`sorryAx` absent; one English "admit"
  in a comment).
- `gabbro_ziel` axioms not re-printed (untouched files only;
  additive import cannot change them; merge gate re-checks).

## What remains open (see CUTS for the full list)

- General `decodeBs ∘ encodeBs = id` for memory rows: parse half
  and reg-field half proved generally, memory rows pinned on
  representative shapes. The composed simp unfolding exceeds the
  tactic budget (deterministic heartbeat timeout at `whnf` over
  the nested decoder matches; diagnostics showed no rewrite
  cycle, only deep `casesOn` unfolding — `Option.casesOn ↦ 1200`).
- TZCNT/LZCNT execution (deferred to the BMI lane by design).
- Memory-source execution (address computation/SIB open; TSO
  event path only).
- No source/IR/loader/entry/budget link, no W/GX simulation, no
  timing, no hardware correspondence beyond self-consistency.
- POPCNT ZF reads source-zero; equivalence with count-zero needs
  the truncation mask bound (inherited open from `BitCount`);
  concrete agreement on `0xFF`/`0` pinned
  (`pin_popnull_scanZF_voll/null`).

## Task-text corrections (historical: described commit cf407e52;
superseded by the repair section above, which governs the
current head)

1. (Superseded.) For cf407e52 the destination was modeled as
   UNMODIFIED per SDM 093 operation text; since the repair the
   destination on a zero source is FREE (`BsScanZulaessig`),
   with unchanged proved as one admitted member.
2. The task's POPCNT flag row overrides the accepted `BitCount`
   undefined-modeling (`popcntFlags` keeps CF/OF/SF/PF, AF none):
   value agreement with `popWort`/`popCount` is exact, flags
   follow the manual (all cleared, ZF = source zero).
3. (Superseded.) For cf407e52 BSF/BSR PF was modeled as DEFINED;
   since the repair only ZF is defined and CF/OF/SF/AF/PF stay
   free in `BsScanZulaessig`, with the cleared snapshot kept
   solely as the reference member.
4. 16-bit POPCNT carries 66H **and** F3 (found by a failing
   round-trip: the encoder emitted 66H alone and decode rightly
   refused); the legacy parser accepts both orders and refuses
   F2/doubled prefixes.
5. `PerfMerkmal` has no POPCNT row, so the CPUID gate arrives as
   a plug parameter (observed answer), not through
   `HwFeatureGates` state legs — same wrapper-enforced discipline
   documented in that file's CUTS.

## Silicon provenance

`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
(SDM 325462-093US, Sept 2026): BSF ll. 42722–42804, BSR ll.
42805–42886, BSWAP l. 42890f, POPCNT ll. 83587–83662, EFLAGS
cross-reference l. 28794. No AMD snapshot; no silicon proof
claimed.
