# MUSE-REPORT-122 (lane 122, audit of the wave 4-5 theorems)

## What was done

Read-and-probe lane. Read `dokumente/SATZKARTE.md` (§§7-10), the
`messung/muse/MUSE-REPORT-*.md` wave-4/5 reports, and every main theorem
listed in the task. Added ONE Lean file,
`grammatik/Grammatik/AuditW5.lean` (registered as
`import Grammatik.AuditW5` at the end of `grammatik/Grammatik.lean`),
with two proved counter-lemmas backing the two "no/partial" rows.
No other file in `grammatik/` was touched. No code/probe/example
numbers were added (task assigns none).

New theorems (exact names):

- `Gabbro.Grammatik.fussB_all_falsch :
  (∀ f : refD.Fn, vertragFussB refP f = true) → False` — the joint
  checker premise of the four `hReqTAll_aus_B` / `hReqGAll_aus_B` /
  `hEnsTAll_aus_B` / `hEnsGAll_aus_B` theorems (`VertragsFuss.lean`)
  is false on the reference fixture itself (`lies` ensures
  `result = konto[0]` with an empty write signature, so
  `vertragFussB refP refLies = false` by computation). Every premise
  is used.
- `Gabbro.Grammatik.hkey_schliesst_frei_aus` — the `hkey` premise of
  `profil_modell` (`Profil.lean`, `∀ a ∈ P, ∃ k v, istModus a k v`)
  is unsatisfiable for any profile containing a `frei` entry (no
  `frei` entry equals a `modus` entry). Every premise is used.

Both depend only on `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of the file). No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`; no `Prop`-typed premise; no discarded
premise.

## Last `./lean-bau` result line

`Build completed successfully (62 jobs).` — whole project green.
`./lean-probe grammatik/Grammatik/AuditW5.lean` reports
`0 error(s) in the COMPLETE output`.

## Audit table

`SAT` = premises jointly satisfiable by a non-degenerate program
(>= 1 written table, reached run with a memory change). Witness
quality judges the filed `_zeuge`, including whether a premise is
discharged only because the witness world makes it vacuous.

| Theorem (file) | Premises | SAT | Witness quality | Finding |
|---|---|---|---|---|
| `csl_ressourceninvariante` (CSLInvariante) | `hO`, `hGuard` (declaration fact), `hLokal`, `hStart`, `hRelease` | yes | strong: `csl_ressourceninvariante_zeuge` on `refB_prog`; invariant nontrivial (`badSp81`); run moves slot 0 → 100 | none. No premise quantifies over all syntax. |
| `eigenzustand_nur_eigene_schritte` (EigenZustand) | `hO`, `hNurG` (other threads never name `t`) | yes | weak-but-honest: `_zeuge` uses `ezdProg` (constant carrier-free text, so `hNurG` holds because NO thread names any carrier) and a `leave` step; memory change rides on a separate `prog2` (`refB_prog`/`refPC2`). Documented in the file. | Split witness (premises on a degenerate text, non-degeneracy on another program). Not vacuous — premises are satisfiable — so no counter-lemma; flagged, not failed. |
| `eigenzustand_nur_eigene_schritteD_rep` (EigenZustandD) | `hO`, `hNurG`, `hNoAx` (∀-over-`Stmt`, but conclusion is a negated existential about `axiomCall` shapes only) | yes | same split pattern as above; `hNoAx` holds vacuously over the empty `Ax` of `refD` — inherent to the fixture (any `refD` program has no axioms), documented as "vacuous over the empty Ax" in the file. The `axiomCall_ohne_ereignis_gegenbeispiel` shows `hNoAx` is load-bearing, not decoration. | none (vacuity is fixture-inherent and disclosed). |
| `rufG_treu` (RufMaschineG) | reachability derivation only (run DATA) | yes | strong: `rufG_treu_zeuge` (7-step run, slot 0 → 2, `M7G_moves`) + second `bind_leave` witness | none. |
| `hoare_call` (HoareRuf) | `hR : RespektiertVertraege`, `hp`, `hr` (all used) | yes | WEAK: `hoare_call_zeuge` runs on `rufPD`/`Rwit70`, which returns the world unchanged — no written table and no memory-changing step in the witness. Premises are satisfiable, so no counter-lemma; but the witness does not meet the non-degeneracy bar (no `∃ f t, schreibt`). | witness gap (minor): add a memory-moving call witness or book the exemption. Not a theorem defect. |
| `axiomCall_haelt_waechter` (FremdSperre) | `hw`/`hg`/`hd`/`hgd` (per-axiom shapes, all used), `hO`, `hh`, `hexec` | yes | strong: `_zeuge` + `gutO_bewacht_zeuge` with `hdiffF` (slot flips) and `zeuge_schreibt` | none. `axiomCall_ohne_sperre_nicht_ableitbar` is the matching refusal. |
| `wache_global_aus_schuld` (WacheGlobal) | `hGuardG`, `hg`, `hW`, `hTouch` (∀ over member threads, all used) | yes | adequate: single-thread `gJ`, `hTouch` discharged over one thread (weak — no second writer — but the theorem is single-writer-shaped); memory moves (global 0 → 5, `welten[0] ≠ welten[1]`); table write exists (`gTabWrite`) though the witnessed write is the global one | note only, no defect. |
| `invariantenKontext_aus_disziplin_bedarf` (DisziplinBedarf) | `hAbD`, `hFrameTD`, `hFrameGD`, `hGuardBedarf` (narrowed: only written carriers need guards), `hEntry`, `hReturn`, `hWatch` | yes | strong: two-table `bedD` (guarded writer + unguarded reader); `bedGuardEx_falsch` proves the OLD full premise false there, so the narrowing is strictly weaker and proved | none. Model narrowing. |
| `stabil_ohne_form` (StabilBewacht) | `hKopf`, `hEigen`, `hStabil` (all used; no syntax universals) | yes | good: `zbJ` two-thread chain | none. |
| `stabil_aus_bewachung` (StabilBewacht) | `hDep`, `hWacheT`, `hWacheG`, rely pair (all used) | yes | strong: `Q` reads slots 0,1 while slot 5 moves (`zbMemMoved`); `HaengtAb` derived, not assumed | none. |
| `sperre_exklusiv`, `rely_aus_sperre`, `rely_aus_sperre_global` (RelySperre) | `hO` + reachability/step (run DATA); guard memberships | yes | strong: both `_zeuge`s on the `ref` fixture, lock held, slot 0 → 100 | none. |
| `markSep_aus_B`, `nurG_aus_B` (+ `progAus` corollaries) (Trennung) | `hcov` (thread coverage, proved by `refB_prog_abdeckung`), `hB` (decided check) | yes | mixed: joint zeugen on `refB_prog` with written table + moving run — BUT `refD.Marke = Empty`, so the mark check passes vacuously (no marks exist to collide). The check is unexercised, not the premises unsaturated. | vacuous-discharge note (fixture-inherent). `pcMarkSep_scheitert_geteilte_marke` documents the real boundary. |
| `unsharedSep_aus_B` (Trennung) | same shape as above | yes | GAP: only an `example ... := by decide`, no joint `_zeuge` (file says "no witness obligation"). Premises are computable, risk low. | witness gap (minor, filed by the owning lane itself). |
| `pcMarkSep_aus_verschiedenen_funktionen` (Trennung) | `hFn`, `hDisj` (distinct bodies name disjoint codes — load-bearing after the lane-100 falsification of the sketch) | yes (vacuously on `refD`) | none filed, none owed (no syntax universals) | none. B8 (same-function threads) still open, as reported. |
| `hReqTAll_aus_B` etc. ×4 (VertragsFuss) | `hB : ∀ f, vertragFussB P f = true` | NO on `refP` | none filed — deliberately, reported as finding in MUSE-REPORT-101 | PROVED (`fussB_all_falsch`): write-signature containment excludes ordinary read contracts (`lies`). Repair direction (read-or-write footprint) is a statement change, not proved here. |
| `syscall_paarung`, `paarung_gibt_gutO` (SyscallPaarung) | per-axiom pairing premises (∀ over `Ax`, used; `swD.Ax` is a singleton, discharged by cases) | yes | strong: joint zeugen + `syscall_paarung_abgelehnt` rejection counterpart | none. |
| `profil_modell` (Profil) | `hgut`, `hkey : ∀ a ∈ P, ...` | PARTIAL | `profil_modell_zeuge` is keyed-only | PROVED (`hkey_schliesst_frei_aus`): profiles with free-prose assumptions cannot use the theorem. Scope restriction, not unsoundness. |
| `bindung_fuegt_nichts_hinzu`, `widerspruch_abgelehnt` (Profil) | membership + agreement premises (all used) | yes | adequate (`bindung_fuegt_nichts_hinzu_zeuge` takes `m` as a parameter — exhibits nothing, but the conclusion is an implication, so this is the natural shape) | none. |
| `g001_korrekt` family, `erasure` (Geist) | `h : g001 b = true` (decided check) | yes | good (`g001_korrekt_zeuge`, `erasure_zeuge`) | none. No syntax universals. |
| `sysAbiGutB_sound`, `dekodiere_total` (Syscall) | decided check / none | yes | good (three `_zeuge`s) | none. Pure. |
| `clz_log2`, `popcount_rotl`, `rotl_rotr`, `bswap_*` (Bits); `addS_*`, `addW_c_gleich` (Ueberlauf); `alloc_*`, `keine_fragmentierung` (Arena) | arithmetic/pure premises | yes | good (all have `_zeuge`s) | none. Out of the vacuity class (no program syntax in premises). |
| HoareRegeln (`hoare_skip/assignVar/seq/ite/konsequenz/Runabhaengig`) | single triples / shapes; NO ∀-over-syntax premise (`ht`/`he` in `hoare_ite` are single-triple premises with a read-projection shape, satisfiable when `c.orte` is inhabited) | yes | none filed, none owed under rule 13 | none found. (Loop rules still open per file CUTS — not vacuity.) |

No premise of the form `∀ V : Vertrag D` / `∀ s : Stmt …` with a
positively-demanded preservation property (the wave 1-2 defect class)
was found in any wave 4-5 main theorem. The two ∀-over-syntax premises
that exist (`hNoAx` in EZD, `hB` in VertragsFuss) are a negated
existential and a decided check respectively; the first is satisfiable,
the second is provably not (on `refP`) and is reported as such.

## What remains open

- The four VertragsFuss conclusions are unusable for programs with read
  contracts; the repair (containment in a read-or-write footprint)
  changes the target statement and belongs to a follow-up lane.
- `profil_modell` covers keyed-only profiles; free-prose assumptions
  need a separate satisfiability argument (D11-adjacent).
- Witness gaps (not defects): `hoare_call_zeuge` has no written table /
  memory-moving step; `unsharedSep_aus_B` has an `example` instead of a
  joint `_zeuge`; Trennung mark-separation zeugen run on a mark-free
  fixture; EZD/EigenZustand zeugen pair a degenerate program text with
  separate non-degeneracy evidence.
- B8 (same-function threads vs `PCMarkSep`), D1/D4/D5/D11 wiring, and
  the Hoare loop rules remain open per the owning lanes' CUTS.

## Task discrepancies

- The task lists `Konstanten` among the merged files: no such file
  exists in this tree (`ls grammatik/Grammatik/` has no match; nothing
  imports it). It was not audited.
- The task's "every rule-13 witness is built on [ReferenzB]" does not
  hold literally: `WacheGlobal` (gD), `DisziplinBedarf` (bedD),
  `SyscallPaarung` (swD), `HoareRuf` (rufD), `EigenZustandD` (BG.D1 +
  refD), `RelySperre` (own + global fixtures) use dedicated fixtures,
  each documented in its file. This is legitimate (the fixtures are
  non-degenerate where it matters) and was treated as compliant.
