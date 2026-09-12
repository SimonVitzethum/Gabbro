# MUSE-REPORT-19: read-only audit of Ziel.lean lines 1-1200

Lane 19. Slice: `grammatik/Grammatik/Ziel.lean` lines 1-1200 only.
No existing file was modified. All findings carry a checked Lean
demonstration in `messung/muse-audit/19/` (each ends with `CUTS:` and
`#print axioms`, and each passed `./lean-probe`).

Coverage: read the full slice (defs, theorems, docstrings, `#print
axioms` lines) plus the referenced definitions behind the audited
claims: `zwei_fehler`/`bedeutung_total`/`Brav`/`exec_spur`
(`Satz.lean`), `Gesittet`/`lauf_aus_brav`/`ForeignExclusion`/
`bruecke_exec_gesittet` (`Wettlauf.lean`), `SpecQ`/`SpecTriple`/
`InterferenceFree`/`SeqTriple`/`InvariantForm`/
`invErhalt_aus_Kontext`/`stabil_from_spec`/
`stabil_from_spec_invariantForm` (`InterferenzAllgemein.lean`),
`QRequires`/`QEnsures`/`QExpr` (`Extraktion.lean`),
`sampling_closes_frist`/`deadlineSpacing` (`Fristlauf.lean`), `rufAt`
entry/return check vs `SpecTriple` fields (`Semantik.lean`),
`Programm.requires/ensures` types (`Syntax.lean`). Checked for bare
`Prop` premises and `have _ :=` discards by grep (none in proofs;
only docstring mentions). Did not re-verify proofs below the slice
(lines 1200+).

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration | status | severity |
|---|-----------|---------|----------------------|---------------|--------|----------|
| 1 | Ziel.lean:107,110,114-120;478-485 | (a) conclusion = premise/def unfolding | `absenkung_wert` is `rfl`, `absenkung_haelt_schranke` is the field `A.begrenzt`; L5 legs repeat both | `messung/muse-audit/19/Audit19Definitional.lean` (a1,a2,a6) | VERIFIED | low |
| 2 | Ziel.lean:125-129,275-279 (§2, §4) | (a) conclusion = constructor list restated | `ziel_zwei_fehler`/`ziel` case-split the `Ausgang` inductive; provable from the constructors alone | `Audit19Definitional.lean` (a3) | VERIFIED | low |
| 3 | Ziel.lean:132-135,139-141 | (a) totality/determinism by `⟨_,rfl⟩`/`rfl` | `ziel_total` holds for any function, `ziel_deterministisch` is `x = x`; neither observes `exec` | `Audit19Definitional.lean` (a4,a5) | VERIFIED | low |
| 4 | Ziel.lean:207-211 (`ziel_brav_aus_exec`) | (a) conclusion = premise under unfolding | `Brav` (Satz.lean:258) is literally the conclusion of `exec_spur` (Satz.lean:1331); the proof is direct application | cited in report, shown by `rfl`-level defeq (no new file; defeq check is `exec_spur ... = Brav ...` by unfolding) | UNVERIFIED (no separate demo file) | info |
| 5 | Ziel.lean:218-232 (`ExecEng.provenienz`) | (d)/(e) docstring claims `exec` provenance; shape admits any `Brav` pair | `Brav.refl` over an empty-trace world discharges `provenienz` with no `exec`/`eval`/program in context; memory need never change | `Audit19ExecEng.lean` | VERIFIED | medium |
| 6 | InterferenzAllgemein.lean:1069-1072 (`SpecQ`), consumed Ziel.lean:454s | (b) contract params/result quantified away at use site | `SpecQ f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`: Pre and Post coincide at the same σ; degenerate `True/True` triple is inhabited and its conclusion is `True ∧ True` by `rfl` | `Audit19SpecQ.lean` | VERIFIED | medium |
| 7 | InterferenzAllgemein.lean:1078-1091 (`SpecTriple`), consumed Ziel.lean:454+ | (b) premise admits contracts ignoring ρ and v | Triple fields bind only `k vor nach`; `rufAt` checks requires at entry ρ and ensures at return (v,ρ) (Semantik.lean:771-776), but the triple never mentions `Env`/`ErgVal` | `Audit19NoRhoV.lean` | VERIFIED | medium |
| 8 | Ziel.lean:522 (`hForm`), §7 docstring "same conclusion" | (b)/(d) `InvariantForm` collapses requires/ensures to one invariant | `Q f σ ↔ I.inv c σ` forces Pre∧Post-at-σ to equal one invariant; `True↔True` coincidence is inhabited | `Audit19InvariantForm.lean` | VERIFIED | medium |
| 9 | InterferenzAllgemein.lean:426-431 (`invErhalt_aus_Kontext`), via §7/§8 legs | (a) `iff` = premise applied twice, payloads discarded | Proof term `⟨fun _ => hInv c nach hkn, fun _ => hInv c vor hkv⟩` ignores both invariant facts; "no per-run proof" rests on `hInv` (every world) doing all work | `Audit19InvErhalt.lean` | VERIFIED | medium |
| 10 | Fristlauf.lean:395-405, consumed Ziel.lean:387 | (a)/(e) `hspace` negates exactly the open miss arm | `hspace : d+S ≤ p.lauf` vs miss arm `p.lauf < d+S`: `Nat.not_lt.mpr`; sampling content is the window disjunction minus the deleted arm | `Audit19Frist.lean` | VERIFIED | low |
| 11 | Ziel.lean:379-380,388-389 (outcome + lowering legs of `ziel_nutzer_last`) | (a) legs provable from single premises, independent of run/contract/probe legs | `zwei_fehler o` uses only `o`; `hLowering.begrenzt` uses only `hLowering`; §4's own rule (line 271) would call `ziel` such a comment | `Audit19Legs.lean` | VERIFIED | low |
| 12 | Ziel.lean:343-391 (`ziel_nutzer_last` load-bearing claim) | negative control, NOT a finding | `hLink` (`rw [hLink]`) and `hspace` (fed to `sampling_closes_frist`) are genuinely consumed at elaboration level | `Audit19NegativeControl.lean` | VERIFIED (pass) | info |

Zero findings of type (c) in the strict sense (no world fold making a
predicate trivially true/false for ordinary programs was found in
1-1200; the closest is finding 5, where `Brav.refl` supplies
memory-constant witnesses). No `sorry`/`admit`/`axiom`/`native_decide`
in the slice. No premise of type `Prop` itself in the slice's theorems.
No `have _ :=` discards in proofs (grep confirms; matches are
docstring prose only). All `#print axioms` in the slice report only
`propext, Classical.choice, Quot.sound`.

## What I believe is wrong in the task or the tree

1. The task's rule 4(b) ("contracts hold at their place with the actual
   values") is not satisfiable by the current `SpecQ` shape even in
   principle: `SpecQ` is `World → Prop` per thread, so entry-vs-return
   can only ever be encoded by choosing different `Pre`/`Post`
   predicates over the same world type, never by binding entry ρ and
   return v distinctly. Findings 6-8 are consequences of this shape, not
   of any single mis-proved lemma. Fixing it means changing `SpecQ`
   (e.g. relating entry world + return world + value), not adding
   another leg.
2. Findings 2-3 and 11 are flagged low deliberately: restating an
   inductive split or a field projection as a named leg is legitimate
   bookkeeping. The file already models this honesty once (the withdrawn
   `ziel_zeit_ist_hardware`, lines 255-263). The residual issue is only
   that the §5 docstring's "every premise is load-bearing" is true at
   elaboration level (finding 12 confirms) while two legs are
   semantically independent of the rest (finding 11 shows) -- the two
   senses of "load-bearing" should not share one sentence.
3. Finding 4 is marked UNVERIFIED: it needs only an unfold-check
   (`Brav` vs `exec_spur` conclusion), and I ran out of budget to wrap
   it in a probe file. It is the weakest claim in the table; treat it
   as a reading note, not a finding.

## New definitions/theorems

None added to `grammatik/` (read-only audit). New demo files only, all
under `messung/muse-audit/19/`: `Audit19SpecQ.lean`,
`Audit19InvariantForm.lean`, `Audit19ExecEng.lean`,
`Audit19Definitional.lean`, `Audit19NoRhoV.lean`,
`Audit19InvErhalt.lean`, `Audit19Frist.lean`, `Audit19Legs.lean`,
`Audit19NegativeControl.lean`. No `import Grammatik.<Name>` line was
added to `grammatik/Grammatik.lean` (nothing new to export).

## Last build result

`./lean-bau` was not run: the task is read-only and I changed no file
under `grammatik/`, so the build is untouched by construction. Every
demo file passed `./lean-probe` individually (outputs: axioms lines
only, plus unused-variable linter warnings in demos A/B/D).

## What remains open

- Finding 4 deserves its own probe file (unfold-check `Brav` =
  `exec_spur` conclusion).
- Whether `hForm`/`hEntry`/`hReturn`/`hWatch` are dischargeable for
  ordinary (non-degenerate) programs is the load-bearing practical
  question behind findings 5-9; answering it needs a concrete program
  and lies outside slice 1-1200.
- Slice lines 1200+ (`ziel_nutzer_last_aus_pc_Q` and the Q-binder
  corollaries) were explicitly out of scope and were not audited.
