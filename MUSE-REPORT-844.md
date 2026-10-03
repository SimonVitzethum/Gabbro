# MUSE-REPORT-844: Composition closing — profile-selection closing

## What was done

New file `grammatik/Grammatik/X86/ComposeProfileSelect.lean`
(+1 import line in `grammatik/Grammatik.lean`) closes backend form choice
to the named CPU profile by composing three already-accepted producer
modules, reusing their definitions and theorems by name without
re-proving any internals and without duplicating any interpreter:

- Producer/consumer interface closed: `FeatureProfile.fallback`
  (profile names a feature; refused feature -> scalar path, tuning only)
  x `Anweisungswahl.waehleNull` (zeroing form gated by flag liveness)
  x `Codec.roundtrip` (the same canonical decoder `ValidatorSkeleton`
  uses for coverage) x `Bild.schreibLese_zeuge` (reached
  memory-changing run over loaded image memory).
- `composeInstr flagsLive dst`: the single element of `waehleNull`
  (pinned by `composeInstr_eq_waehleNull`); the CPU profile never changes
  its meaning.
- `composeMerkmal hw b m`: exactly `fallback hw b m`.
- `ComposeProfileSelect_verbindung` (generic over arbitrary `hw`, `b`,
  `m`, `flagsLive`, `dst`, `suffix`, `s`): composed bytes re-decode
  (`compose_bytes_revalidated` via `roundtrip`), the composed step
  zeroes its register (`compose_zero` via `schritt_null_mov` /
  `schritt_null_xor` + `null_laengen`, so profile choice is tuning only
  for values), refusal falls back to scalar
  (`compose_fallback_closed` via `fallback_verweigert_bleibt_skalar`),
  and a nonzero memory-changing write/read is reached
  (`schreibLese_zeuge`).
- Planted refusals: `compose_profil_verweigert` (FTZ control word
  refuses scalar double on full silicon, via `sse_verweigert_bei_ftz` +
  `waehle_verweigert_strikt`), `compose_live_refuses_clobber` (clobbering
  composed form under live flags refused, via
  `wahlOk_verweigert_xor_le`), with positive twin
  `compose_dead_allows_clobber` (via `wahlOk_erlaubt_tot`).
- `ComposeProfileSelect_verbindung_zeuge`: joint companion at concrete
  values (baseline profiles, scalar feature, dead flags, `rax`, empty
  suffix, `valZeugeZustand`) obtained by ONE joint application of
  `verbindung`, plus the non-degenerate source side
  (`wit_schreibt`: contract writes its table; `wit_step`: reached run
  whose slot reads 5).

## Exact new names

Defs: `composeInstr`, `composeMerkmal`.
Theorems: `composeInstr_eq_waehleNull`, `compose_fallback_closed`,
`compose_zero`, `compose_bytes_revalidated`, `compose_profil_verweigert`,
`compose_live_refuses_clobber`, `compose_dead_allows_clobber`,
`ComposeProfileSelect_verbindung`,
`ComposeProfileSelect_verbindung_zeuge`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposeProfileSelect.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (509 jobs).`
- `#print axioms` for all nine theorems: subsets of
  `[propext, Classical.choice, Quot.sound]` (the `gabbro_ziel`
  standard); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- No new diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
  files. `git status` shows only the owned new file modified
  (plus this report); the `Grammatik.lean` import line went in with the
  green skeleton commit.

## What remains open (CUTS in the file)

- No `valX86` image embedding of the composed bytes (re-validation is
  decode-level); full `valX86_sound` stays with owner 349.
- No source lowering correspondence (source appears only as the
  non-degeneracy witness); no budget transfer, no call-log effect.
- No hardware claim (model bytes/memory only); no cost/time claim
  (tuning-only is about values, never speed).
- Only the zeroing form family is composed; multiply/shift/vector/LOCK
  stay with their owners.

## Task remarks

Nothing in the task statement was found wrong. One scoping note: the
ZEUGE inhabitation rule is written for source-syntax premises, while
this composition closes X86 backend legs; the companion therefore
carries BOTH the joint concrete backend instance AND the reused
source-level non-degeneracy witnesses (`wit_schreibt`, `wit_step`) so
the merge gate's table-writing/reached-run requirement is met
literally rather than by analogy.
