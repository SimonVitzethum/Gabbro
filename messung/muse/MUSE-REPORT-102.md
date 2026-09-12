# MUSE-REPORT-102 (lane 102, D3: guards only where they are needed)

## What was done

New file `grammatik/Grammatik/DisziplinBedarf.lean` (wired into
`grammatik/Grammatik.lean`), closing SATZKARTE §7 row `hGuardEx` in the
narrowed form the D3 proposal asks for.

- `traegerStill_ohneSchreiber` (helper): a carrier no member thread
  writes keeps its invariant at every chain index. Proof: `kette_erhaelt`
  with entry at the head and `nichtschreiber_erhaelt` at every step (the
  step's writer comes from `J.hSchritt`, its non-writer status from the
  `hNie` premise).
- `invariantenKontext_aus_disziplin_bedarf` (TARGET, premise- and
  conclusion-identical to the task): case split (`by_cases`) on whether
  some member writes the carrier. Written carriers go through the
  existing `hinv_kette_aus_disziplin` with the guard from `hGuardBedarf`
  (the old proof shape, guard source swapped); unwritten carriers go
  through the helper. Every premise is used across the two branches.
- Rule-13 witness `invariantenKontext_aus_disziplin_bedarf_zeuge` plus
  the separate `bedGuardEx_falsch` lemma (old `hGuardEx` is false on the
  fixture).

## Exact names of new definitions/theorems

Fixture: `bedSigSchreib`, `bedSigLies`, `bedD` (Tab `Bool`: `true` =
written guarded `konto`, `false` = never-written unguarded `config`),
`bedSp0`, `bedW0` (lock taken), `bedV100`, `bedW1` (`konto[0] := 100`),
`bedNb`, `bedJ` (one member thread, two worlds, one step), `bedI`
(trivially true invariant with proved discipline), `bedWc`, `bedGc`.
Facts: `bedW1_slot`, `bedW0_slot`, `bedMemWechsel`,
`bedSchreibt_konto`, `bedSchreibt_config_schreiber`,
`bedSchreibt_konto_leser`, `bedSchreibt_config_leser`,
`bedGuard_konto`, `bedW0_haelt`, `bedAnfang_schreib`,
`bedBraucht_konto`, `bedBraucht_config`, `bedRahmen`, `bedJ_faeden`,
`bedJ_welten`, `bedAb`, `bedFrameT`, `bedFrameG`, `bedGuardBedarf`,
`bedEntry`, `bedReturn`, `bedWatch`, `bedGuardEx_falsch`.

## Last `./lean-bau` result line

`== 0 error line(s) in the COMPLETE output`, `Build completed
successfully (54 jobs)`. `./lean-probe` on the new file: `0 error(s)`.
`#print axioms` for the helper, the target, the witness, and the
guard-false lemma: `[propext, Classical.choice, Quot.sound]` only, no
`sorryAx`. Commit `dfa28416` (Lean work).

## What remains open

Nothing in-lane: target proved, witness joint, build green. Adjacent
(unchanged by this lane): global watches still checker-side (D6),
`GeteiltGedeckt` untouched, the `hReturn` per-step restoration stays a
user obligation per carrier.

## Notes on the task (deviations and findings)

1. The witness is NOT on the reference fixture, deliberately: `refD`
   has exactly one carrier (`Tab = Unit`, `Glob = Empty`), so the old
   `hGuardEx` cannot fail there and the demanded shape (one written
   guarded carrier plus one read-only unguarded carrier) is
   uninhabitable on it. `bedD` carries the same non-degeneracy instead
   (a written table, a memory-changing chain step), and the witness
   additionally cites the reference reached run
   (`refB_pc_erreicht`/`refB_pc_schreibt`) as a final conjunct.
2. The witness invariant is trivially true, so `bedEntry`/`bedReturn`
   consume only the world-identification hypotheses; the guard
   hypotheses of `bedReturn` are unused on a one-step chain (a minimal
   chain cannot exercise restoration). Same shape as the merged
   precedent `refInv81_release` (documented redundant hypothesis);
   booked in the file's `CUTS`.
3. Proof-engineering note: `simp` cannot unfold `World.storeSlot`'s
   dependent match (type-correctness failure at implicit
   transparency); kernel evaluation (`rfl`, `decide`, `absurd … (by
   decide)`) goes through. `List.mem_singleton` would not fire under
   `simp only` here, so the watch proof uses `mem_singleton.mp` in
   term mode plus `injection`.
4. Text guardians: `pruefe-kennungen` passes; `pruefe-englisch` is red
   on a Rust-comment ratchet (7905 vs 7881, `crates/` scope, does not
   read `grammatik/`) and `pruefe-todo` needs `cargo` (absent here) --
   both pre-existing and unrelated to this lane.
