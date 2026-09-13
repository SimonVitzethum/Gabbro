/-
  File:      Grammatik/AuditFinal.lean
  Subject:   FINAL AUDIT WAVE (lane 134): probes and counter-lemmas on the
              goal theorems (`ziel_ort_voll`, `ziel_ort_geraet`), register
              locality (`RegLokal`), race freedom (`rennfrei_g`), the cost
              bounds (`KostenG`) and the runnable fragment of machine G.

              The verdict table with evidence is in `MUSE-REPORT-134.md`;
              every negative verdict there is backed by a proved lemma here
              or by a precise description pointing at the exact shape.
-/
import Grammatik.ZielOrtGeraetZeuge
import Grammatik.ZielOrtVollZeuge
import Grammatik.RennfreiG
import Grammatik.KostenGZeuge

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Goal premises: the `voll` witness contracts are `true`. -/

/-- The `voll` witness reasons about no contract: the requires gate is `true`. -/
theorem audit_vP_requires_true : vP.requires vHaupt = .wahr := rfl

/-- The ensures gate is `true` as well: joint satisfiability without frame reasoning. -/
theorem audit_vP_ensures_true : vP.ensures vHaupt = .wahr := rfl

/-! ## 2. `RegLokal`: satisfiable by a memory-dependent oracle. -/

/-- `RegLokal` does not force constant answers: `geO` is local and reads memory. -/
theorem audit_geO_zeitveraenderlich_lokal : RegLokal geO ∧
    (∃ σ σ' : World geD, geO.regLies () σ ≠ geO.regLies () σ') :=
  ⟨geO_lokal, geO_liest_speicher⟩

/-- A device whose answer changes with NO write to its carriers is outside:
    differing answers on carrier-agreeing worlds refute `RegLokal`. -/
theorem audit_regwechsel_braucht_traeger (O : Orakel D) (r : D.Reg)
    (σ σ' : World D) (hG : GleichAuf (D.rtraeger r) σ σ')
    (hN : O.regLies r σ ≠ O.regLies r σ') : ¬ RegLokal O := by
  intro hRL
  exact hN (hRL.1 r σ σ' hG)

/-! ## 3. Race freedom: what `SchreibRasse` does not see. -/

/-- Lock steps record no carrier access: the race notion is blind to them. -/
theorem audit_zugriff_nimmt : zugriffVon (D := geD) (.nimmt GeLock.lg []) = none :=
  rfl

/-- Releases record no carrier access either. -/
theorem audit_zugriff_gibt : zugriffVon (D := geD) (.gibt GeLock.lg) = none :=
  rfl

/-- Reads are not races by definition: if EITHER step leaves `c` alone,
    the pair is no `SchreibRasse`. Both premises are consumed by the case split. -/
theorem audit_lesen_kein_rennen {M M' M'' : RufMaschineG D} {f g : Faden}
    {c : D.Tab ⊕ D.Glob}
    (h : TraegerGleich M'.speicher M.speicher c ∨
      TraegerGleich M''.speicher M'.speicher c) :
    ¬ SchreibRasse M M' M'' f g c := by
  intro hR
  obtain ⟨_, hw1, hw2, _⟩ := hR
  cases h with
  | inl h => exact hw1 h
  | inr h => exact hw2 h

/-- The race notion covers guarded carriers only: a race names its guard. -/
theorem audit_schreibrasse_braucht_waechter {M M' M'' : RufMaschineG D}
    {f g : Faden} {c : D.Tab ⊕ D.Glob}
    (hR : SchreibRasse M M' M'' f g c) : ∃ L : D.Lock, Bewacht c L :=
  hR.2.2.2.1

/-! ## 4. Costs: the loop run sits strictly under its bound. -/

/-- The witnessed `retry`-loop run takes 9 own steps against a bound of 18. -/
theorem audit_schleife_unter_schranke :
    9 ≤ kostenTief hP 0 2 (initF 0).1 := by
  rw [hP_kosten]
  decide

/-! ## 5. The machine runs every construct with a step rule. -/

/-- The `locks`-block-plus-call program reaches a machine with changed memory:
    `locks`, calls (direct, indirect, `else`-caught) and axioms all fire on G. -/
theorem audit_vlauf_schreibt :
    ∃ M : RufMaschineG vD, RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M ∧
      M.speicher.slots () 0 () = true := by
  obtain ⟨M, hr, _, hmem, _, _, _, _, _, _⟩ :=
    ziel_ort_voll_zeuge.2.2.2.2.2.2.2.2
  exact ⟨M, hr, hmem⟩

/-- The `geraet` witness contract is non-trivial: `leser` ensures its result. -/
theorem audit_geP_ensures_leser : geP.ensures geLeser = .var .hier := rfl

/-- The `geraet` run is genuinely two-threaded: thread 0's reader (two
    register reads with its own write between them) interleaved with
    thread 1's write, both memory changes reached. -/
theorem audit_gelauf_zwei_faeden :
    ∃ M : RufMaschineG geD,
      RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M ∧
      (M.speicher.slots GeTab.tafel 0 ()).n = 1 ∧
      (M.speicher.slots GeTab.notiz 0 ()).n = 1 := by
  obtain ⟨M, hr, htafel, hnotiz, _, _⟩ := geLauf
  exact ⟨M, hr, htafel, hnotiz⟩

end Gabbro.Grammatik

/-! ## CUTS:

  What is proved: each probe above is a checked lemma over an existing
  witness or definition (no new program, no new run built here).

  What is NOT proved (precise descriptions, see `MUSE-REPORT-134.md`):
  * no joint instance of `ziel_ort_voll` with a non-`true` contract and
    two moving threads exists in the tree (`vP` has `true` contracts and
    moves thread 0 only);
  * no `traverse` or `forever` reached run exists in the tree (step rules
    `dannTrav`/`travNext`/`travFort`/`travDone` exist in `RufMaschineG.lean`,
    the step lemma `schrittArt` covers them, but no run fires one);
  * no `awaits` reached run exists (rule `dannAwaits` exists, no run fires it);
  * no non-adjacent race theorem with an explicit release exists
    (`rennfrei_g_nah` concludes adjacent steps only);
  * no hand translation of corpus programs into Lean syntax is built here.
-/

#print axioms Gabbro.Grammatik.audit_vP_requires_true
#print axioms Gabbro.Grammatik.audit_vP_ensures_true
#print axioms Gabbro.Grammatik.audit_geO_zeitveraenderlich_lokal
#print axioms Gabbro.Grammatik.audit_regwechsel_braucht_traeger
#print axioms Gabbro.Grammatik.audit_zugriff_nimmt
#print axioms Gabbro.Grammatik.audit_zugriff_gibt
#print axioms Gabbro.Grammatik.audit_lesen_kein_rennen
#print axioms Gabbro.Grammatik.audit_schreibrasse_braucht_waechter
#print axioms Gabbro.Grammatik.audit_schleife_unter_schranke
#print axioms Gabbro.Grammatik.audit_vlauf_schreibt
#print axioms Gabbro.Grammatik.audit_geP_ensures_leser
#print axioms Gabbro.Grammatik.audit_gelauf_zwei_faeden
