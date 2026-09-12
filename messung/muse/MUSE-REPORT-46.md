# MUSE-REPORT-46 — Read-only audit of `grammatik/Grammatik/KetteMehrfadenC.lean` + premise-probe fixtures BLIND-WEAK/BLIND-STRONG

Branch: `muse/46`. No existing file was modified (read-only audit);
new files only under `messung/muse-audit/46/` plus this report.
Method and report format follow the wave-1 audits (`MUSE-REPORT-23.md`):
pattern catalogue (a)-(e) per MUSE-REPORT-26 §Method --
(a) conclusion is a premise under another name,
(b) unused / `Prop`-typed / restated-field premise,
(c) definition making a predicate trivially true/false,
(d) prose claiming more than the Lean states,
(e) premises false for ordinary programs (theorem vacuous);
every finding has a `./lean-probe`-green demonstration.

Scope: the full file (977 lines), read in full, plus the merged reviewer
notes in its header (lines 12-19). Cross-checked against `Maschine.lean`
(`PCAtom` :1268, `PCSchritt.take/rel` successor equations, `GenStart` :717,
`Speicher.welt` :364, `pc_gesittet` :1743), `Semantik.lean` (`World` :77,
`offen`, `Ereignis.nimmt/gibt`), `Satz.lean` (`Rahmen` :193),
`InterferenzAllgemein.lean` (`GemeinsamerLauf`, `EintrittPasst`,
`SchuldnerHaelt`, `InvSichtHaelt`), and `instrumente/pruefe-praemisse.py`
in full (1914 lines; fixtures at :1571-1623, blind-spot pair at :1595-1610,
claimed readings at :1725-1793). Tree-wide grep for consumers of the
audited names (`LockSchrittGedeckt[Bei]`, `KettenSpurDeckung`, all six
theorems): zero uses outside the file itself.

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration file | status | severity |
|---|-----------|---------|----------------------|--------------------|--------|----------|
| F1 | KetteMehrfadenC.lean:337-395, 558-605 (`hFrameNew` both bullets) | (c)-adjacent | New-step frame closes by `rfl` because both worlds are `M.speicher.welt ...` over the SAME memory -- the `Rahmen` halves never read the lock event; `blatt` (memory-changing) steps stay owed | `messung/muse-audit/46/F1_LockFrameRfl.lean` (`audit46_lock_frame_is_rfl`: `Rahmen W G (s.welt e1) (s.welt e2)` for ANY footprints/traces) | VERIFIED | informational -- file discloses it ("frame closes by `rfl`", CUTS book `blatt`); the audit value is that the frame duty is vacuous exactly where the SATZKARTE needs memory-changing steps |
| F2 | KetteMehrfadenC.lean:105-107 (`LockSchrittGedeckt`, non-Bei) | (b)-adjacent | Defined but never referenced in any proof term: in-file uses all say `LockSchrittGedecktBei`; tree-wide exact-word grep finds only the definition, one docstring line, and MUSE-REPORT-11 | `messung/muse-audit/46/F2_ToteDefinition.lean` (shape pinned as `Iff.rfl`; deadness is grep evidence, cited in CUTS) | VERIFIED | low -- one membership conjunction, honestly unused, not load-bearing anywhere |
| F3 | KetteMehrfadenC.lean:879-895 (`kette_aus_deckung`) | (a) | Conclusion is `hDeck M pc tr hReach htr` restated: all five kept legs travel argument-for-argument from the witness `Jx`; only the trailing membership leg is dropped. File docstring discloses it ("follows by direct application") | `messung/muse-audit/46/F3_DeckungForward.lean` (`audit46_forwarding_shape`: the forwarding skeleton on a minimal signature) | VERIFIED | high for the N-thread reading -- the theorem derives nothing; the booked N-thread induction (discharge of `KettenSpurDeckung` itself) is the entire remaining work, cf. MUSE-REPORT-23 F6 precedent (honest forwarding still earns a row) |
| F4 | KetteMehrfadenC.lean:909-936 (`deckung_strikt_schwaecher`) | (d) | Billed as "strictly weaker than hJw/hJsf (rule 4a certificate)" but exhibits the SEED `J₀` breaking both equations while a DIFFERENT chain discharges the deckung -- no one witness with `premise ∧ ¬equations`; file CUTS admit it | `messung/muse-audit/46/F4_StrictnessLuecke.lean` (`audit46_joint_needs_colocated` + `Bool` countermodel: split witnesses entail nothing joint) | VERIFIED | medium -- the theorem proves what it states; the "strictly weaker" direction is not established by it |
| F5 | KetteMehrfadenC.lean:766-869 (`kette_zwei_aus_lauf`, via `hlock_prog`/`hforeign`) | (e) | Covered class is lock-only two-thread programs: `take`/`rel` atoms touch no carrier (`PCAtom.carriers = []`), name no marks; any writing/reading thread fails `hlock_prog` (leaf routing dies by `cases hL'`), any third nonempty thread fails `hforeign` (`simp at hpc`) | `messung/muse-audit/46/F5_LockOnlyFragment.lean` (`audit46_lock_atoms_touch_nothing` by `rfl`; `audit46_leaf_breaks_lock_only`: a `leaf` text is not lock-only) | VERIFIED | medium -- file discloses scope ("covers LOCK-ONLY", line 15); fit finding for SATZKARTE §3-flag-5 (`hJw`/`hJsf` for ordinary writing programs stay owed) |

Zero additional pattern-(c)/(e-as-false) verdicts beyond F5 are claimed:
no predicate is shown trivially true/false by quantification (the file has
no `∀ ρ`/`∀ v` erasure; contracts hold at their place per the entry legs),
and worlds come from `PCReach` machine steps (lock worlds keep `M.speicher`,
`blatt` worlds through `execStmt`), so no rule-4b/4c violation is filed.

## What I checked and cleared (no finding)

- `kette_zwei_start`: seed over `GenStart sp` is genuine construction
  (worlds/run `rfl` at literals, `faeden = [f, g]`, pair legs from `hNb`/
  `hNbSymm`, entry legs from the three premises). `_hne` is honestly
  underscore-named (seed needs no distinctness -- only the pair routing does).
- `zwei_lauf_mitgliedschaft`: genuine `PCReach` induction; foreign actors die
  at `hpc` against `prog g0 = []`. Every premise fires.
- `kette_zwei_schritt`: substantive threading step. Checked the three
  suspected-dead premises individually and CLEARED all three: `hne : f ≠ g`
  fires in BOTH bullets (lines 519/522, 725/728: the `f/f` and `g/g` cases of
  `BeschraenkteVerschraenkung` close by `absurd rfl hne12`, so without `hne`
  the pair legs would not discharge); `hmemJ` (line 326) is used in the nimmt
  bullet's prefix-membership routing (lines 498-500); `hReach` feeds
  `genWelten_letzte`/`pcReach_gen` (lines 360, 570) and the membership
  transport (500/511/706/717). `hMSep`/`hCSep` feed `pc_gesittet` (488/698).
  No `have _ :=` discard, no `intro _` in the file.
- Reviewer note "all six theorems depend only on
  [propext, Classical.choice, Quot.sound]" re-verified via `./lean-probe`
  (0 errors; axioms lines printed for all six).
- No `sorry/admit/axiom/native_decide/unsafe` in the file (only `#print axioms`;
  the word `sorry` occurs once in a stale-note sentence, line 13, not as a term).
- `LockSchrittGedecktBei` successor equations match the `PCSchritt.take/rel`
  definiens field-for-field (checked against Maschine.lean constructor bodies:
  same `M.speicher`, same `welt`-appended world, same `pcAdvance`) -- honest
  repackaging of the machine rule, not a new semantics.
- The header scope note ("Such programs never change memory, so the frame
  closes by `rfl`", line 16) is accurate -- F1 is its demonstration, not its
  refutation.

## Premise-probe fixtures BLIND-WEAK / BLIND-STRONG (code review + Lean demos)

`--sprechprobe` was NOT run (it calls `lean` directly: `run([LEAN, tmpname])`
at lines 1377/1659/1676/1804 -- hard rule 2 forbids it). Reviewed by reading
(verdict engine: `check_conjunct_variant` :1348, `check_single_variant` :1626,
`speech_probe` blind cases :1752-1793) and rebuilt as Lean demonstrations:

- `messung/muse-audit/46/FixtureBlindWeak.lean`: fixture source
  (`mid (h : 0 < 1) (k : 1 < 2) : 0 < 2 ∧ 1 < 2 ∧ 0 < 1`, lines 1600-1601)
  with per-conjunct tripwires -- c1 needs `h` jointly (`Nat.lt_trans h k`),
  c2 FREE of `h` (proved from `k` alone), c3 ALONE in `h` (proved from `h`
  alone; weakening `k` leaves it green). Claimed instrument reading: thm
  DERIVED, need [NEEDS, FREE, NEEDS], strength ALONE.
- `messung/muse-audit/46/FixtureBlindStrong.lean`: same shape except c3 is
  `Nat.lt_trans h k` (JOINT -- weakening `k` breaks it). Claimed reading:
  thm DERIVED, need [NEEDS, FREE, NEEDS], strength JOINT. The instrument-level
  difference is exactly the closer difference (`h` vs `Nat.lt_trans h k`).

Code-review notes on the instrument (read, not executed):
- The blind-spot claim is coherent: per-theorem DERIVED coincides for both
  fixtures (A red via c1/c3, B red via c1/c2 in each), per-conjunct need
  coincides ([NEEDS, FREE, NEEDS] -- c2 never mentions `h`), and only the
  strength variant at c3 (weaken `k`, keep `h`) separates ALONE from JOINT.
  The speech-test vocabulary stays closed: `parse_conjunct_proof` handles only
  `exact`/`refine`-tuple closers (:1161-1294); anything else reports
  INCONCLUSIVE rather than guessing -- same honesty as the wave-1 auditors noted.
- One modeling remark (not a bug): the WEAK c3 closer `h : 0 < 1` against
  conclusion `0 < 1` is a restatement shape at the CONJUNCT level -- the
  strength probe legitimizes calling it ALONE/weak, which is exactly the word
  the per-theorem FORWARDED verdict uses at the theorem level. The two
  "weak"s are consistent by construction, not by discovery.
- The NEEDS/FREE/ALONE/JOINT verdict words themselves are instrument-measured
  (lane builds + hermetic `lean`); the demos pin their Lean CONTENT
  (tripwire copies), not the verdicts. Stated in each file's CUTS.

Deliberate-license note (per MUSE-REPORT-26 §"What I believe is wrong"):
`audit46_blindweak_c2_ignores_h` / `audit46_blindweak_c3_strength` carry an
unread premise on purpose -- the unused-premise shape IS the FREE/ALONE
demonstration. The `./lean-probe` linter warnings on `h`/:40 and `k`/:50
are filed as evidence, in the MUSE-REPORT-23 F2 tradition. All other demo
theorems use every premise.

## What in the task I believe is wrong

- Rule 5 ("put new Lean work in the NEW file named in your task and add
  `import Grammatik.<Name>` at the end of `grammatik/Grammatik.lean`") conflicts
  with the read-only order ("Do NOT modify any existing file"): like lane 26,
  I placed demonstrations under `messung/muse-audit/46/` and did NOT touch
  `Grammatik.lean`. I privilege the explicit read-only order, as lane 26 did.
- Rule 3 ("every premise of every theorem you add must be used by its proof")
  would forbid exhibiting an unused premise; the two WEAK-fixture strength
  demos deliberately carry one (linter warnings kept as evidence).
- Nothing else: the reviewer notes merged in the file header held up on
  re-verification (axioms triple confirmed; scope note accurate; the F4
  caveat in CUTS is real and is filed as finding F4, not as a header error).

## Build record

- `./lean-probe` per demo file (first line of output trusted): all 7 report
  `0 error(s)`. Expected linter warnings kept as evidence: unused `h` in
  `FixtureBlindWeak.lean:40`, unused `k` in `:50`, unused `hQb` (fixed --
  removed in final F4 rewrite; final F4 is warning-free), unused `W` (fixed
  in F3). No warnings in F1/F2/F5/FixtureBlindStrong.
- `./lean-bau` last line: `Build completed successfully (33 jobs).`
  (demos live outside `grammatik/` and cannot affect it; the audited file
  itself is untouched).
- `#print axioms`: F1/F2/F5 theorems depend on
  `[propext, Classical.choice, Quot.sound]`; F3 `audit46_forwarding_shape`
  same triple; F4 `audit46_joint_needs_colocated` depends on no axioms;
  fixture theorems depend on no axioms (pure `Nat.lt` terms).

## New definitions/theorems (all in `messung/muse-audit/46/`, audit-only)

- F1: `audit46_lock_frame_is_rfl` (+ 1 example)
- F2: 1 shape example (`Iff.rfl` over `LockSchrittGedeckt`)
- F3: `audit46_forwarding_shape`
- F4: `audit46_joint_needs_colocated` (+ 1 countermodel example)
- F5: `audit46_lock_atoms_touch_nothing`, `audit46_leaf_breaks_lock_only`
- FixtureBlindWeak: `audit46_blindweak_c1_needs_h`, `audit46_blindweak_c2_free`,
  `audit46_blindweak_c2_ignores_h`, `audit46_blindweak_c3_alone`,
  `audit46_blindweak_c3_strength`, `audit46_blindweak_mid`
- FixtureBlindStrong: `audit46_blindstrong_c1_needs_h`,
  `audit46_blindstrong_c2_free`, `audit46_blindstrong_c3_needs_both`,
  `audit46_blindstrong_h_alone_weaker`, `audit46_blindstrong_mid`

## Open / recommended follow-ups

1. F3 is the load-bearing gap: discharging `KettenSpurDeckung` in general
   (per-level frame + witness + routing for arbitrary members, `blatt`
   included) is the whole N-thread task; `kette_aus_deckung` names the
   premise but does not advance it.
2. F4: either prove the joint witness (deckung AT the seed, i.e. `Q J₀` --
   likely needs the lock-only induction at every prefix, which exists as
   `kette_zwei_aus_lauf`) or downgrade the header to "weakness in the
   existential-quantifier reading only".
3. F2: delete `LockSchrittGedeckt` or use it (e.g. state `kette_zwei_schritt`
   over it with the membership leg).
4. F5/SATZKARTE: the `blatt` frame + `SerialLink` witnesses are the priced
   remainder for `hJw`/`hJsf` on ordinary programs; the lock-only induction is
   the base to extend, not to re-prove.
