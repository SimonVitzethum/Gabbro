module

public import Grammatik.Zielsatz.Einbettung.Koerper.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Einbettung
open Gabbro.Grammatik
variable {D D' : Deklaration}
namespace Einbettung
variable (E : Einbettung D D')
variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)
section Sim
variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option linter.unusedSectionVars false in
theorem sim_end_ret {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e)
    (hΛ)
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.ret e hΛ : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.ret e hΛ : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
    e.orte (E.exErg e).orte (E.orte_exErg e).symm
  have hev0 := E.frei_alle hZ (@hev) hρ
  have he := E.evalErg_exErg hZ hI.treu hI.treu e ρ ρ' hρ
  refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
  · simp only [execEndHA, hΦ Φ hP]
  · exact ⟨hI, he⟩

set_option linter.unusedSectionVars false in
theorem sim_end_retScoped {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (R)
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retScoped e R : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.retScoped e R : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
    e.orte (E.exErg e).orte (E.orte_exErg e).symm
  have hev0 := E.frei_alle hZ (@hev) hρ
  have he := E.evalErg_exErg hZ hI.treu hI.treu e ρ ρ' hρ
  refine ⟨M₁, .zurueck σ₁ (evalErg σ₁ e σ₁ ρ), hs, fun Φ hP => ?_, ?_⟩
  · simp only [execEndHA, hΦ Φ hP]
  · exact ⟨hI, he⟩

set_option linter.unusedSectionVars false in
theorem sim_end_retWhy {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (hΛ)
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retWhy r hΛ : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.retWhy r hΛ : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .why σ r, teil_refl M, fun Φ hP => by simp only [execEndHA],
    by simp only [exEnd, execEndHA]; exact ⟨hM, rfl⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_end_retWhyScoped {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (r)
    (R)
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retWhyScoped r R : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.retWhyScoped r R : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .why σ r, teil_refl M, fun Φ hP => by simp only [execEndHA],
    by simp only [exEnd, execEndHA]; exact ⟨hM, rfl⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_end_leave {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (h)
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.leave h : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.leave h : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .leave h σ ρ, teil_refl M, fun Φ hP => by simp only [execEndHA],
    by simp only [exEnd, execEndHA]; exact ⟨hM, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_end_next {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (h)
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.next h : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.next h : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact ⟨M, .next h σ ρ, teil_refl M, fun Φ hP => by simp only [execEndHA],
    by simp only [exEnd, execEndHA]; exact ⟨hM, hρ⟩⟩

set_option linter.unusedSectionVars false in
theorem sim_end_cons {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (ih_sim_stmt_s : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') s) (execStmtHA S' O' U' A' passes R' (exS hS s)))
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, o₁, hs, hΦ, hR⟩ := ih_sim_stmt_s M σ σ' ρ ρ' hM hρ
  generalize ho : execStmtHA S' O' U' A' passes R' (exS hS s) σ' ρ' = o₁' at hR
  rcases o₁ with ⟨σ₂, ρ₂⟩ | ⟨σ₂, v⟩ | ⟨σ₂, r⟩ | ⟨h₂, σ₂, ρ₂⟩ | ⟨h₂, σ₂, ρ₂⟩ | e | e <;>
  rcases o₁' with ⟨σ₂', ρ₂'⟩ | ⟨σ₂', v'⟩ | ⟨σ₂', r'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | ⟨h₂', σ₂', ρ₂'⟩ | e' | e' <;>
  simp only [AusRel] at hR <;> (try exact hR.elim)
  · obtain ⟨M₂, o, hs2, hΦ2, hR2⟩ := ih_sim_end_rest M₁ σ₂ σ₂' ρ₂ ρ₂' hR.1 hR.2
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
      exact hΦ2 Φ hP
    · simp only [exEnd, execEndHA, ho]
      exact hR2
  · exact ⟨M₁, .zurueck σ₂ v, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
      by simp only [exEnd, execEndHA, ho]; exact hR⟩
  · exact ⟨M₁, .why σ₂ r, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
      by simp only [exEnd, execEndHA, ho]; exact hR⟩
  · exact ⟨M₁, .leave h₂ σ₂ ρ₂, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
      by simp only [exEnd, execEndHA, ho]; exact hR⟩
  · exact ⟨M₁, .next h₂ σ₂ ρ₂, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
      by simp only [exEnd, execEndHA, ho]; exact hR⟩
  · exact ⟨M₁, .logik e, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
      by simp only [exEnd, execEndHA, ho]; exact hR⟩
  · exact ⟨M₁, .hardware e, hs, fun Φ hP => by simp only [execEndHA, hΦ Φ hP],
      by simp only [exEnd, execEndHA, ho]; exact hR⟩

set_option linter.unusedSectionVars false in
theorem sim_end_bind {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_end_rest M₁ σ₁ _ (.cons (eval σ₁ e σ₁ ρ) ρ)
    (.cons (eval (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) (exE E e) (leseA A' σ' (Λ.map E.resE) (e.orte.map E.ortE)) ρ') ρ') hI (E.envR_cons hZ hρ _ _ rfl (hev e ρ ρ' hρ))
  refine ⟨M₂, o.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
  · simp only [execEndHA, hΦ Φ (passt_teil hP hs2)]
    exact congrArg EndAusgang.schrumpf (hΦ2 Φ hP)
  · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
    exact E.endRel_schrumpf hR

set_option linter.unusedSectionVars false in
theorem sim_end_bindCall {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (τ)
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCall (τ := τ) f args he hp hr rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.bindCall (τ := τ) f args he hp hr rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (evalArgs σ₁ args σ₁ ρ) (E.fn f)
    (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ'))
    ((E.envR_um hZ (paramsE hS f) _ _).mpr (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)) (Or.inl rfl)
  generalize ha : R' (E.fn f) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE))
    (castE (paramsE hS f) (evalArgs (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)) ρ')) = a' at hRΦ
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he' : D'.erg (E.fn f) = some (E.tyE τ) := by rw [← ergE_fn hS, he]; rfl
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he (E.ergZ hZ (D.erg f) (castV (ergE_fn hS f).symm v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (ergE_fn hS f) he he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha,
        execEnd_umΛ]
      exact E.endRel_schrumpf hR3
  · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exEnd, execEndHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs, ha]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_end_bindCallInd {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n)
    (τ)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (ih_sim_end_rest : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') rest) (execEndHA S' O' U' A' passes R' (exEnd hS rest)))
    : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.bindCallInd (n := n) (τ := τ) p args he hp hr rest : Endblock D V l Γ Λ)) (execEndHA S' O' U' A' passes R' (exEnd hS (.bindCallInd (n := n) (τ := τ) p args he hp hr rest : Endblock D V l Γ Λ))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
  have hp' := hev p ρ ρ' hρ
  rw [hvd] at hp'
  rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
  rw [hvd'] at hp'
  have hk : E.Konform hZ f f' := by
    rcases hp' with h | ⟨hz, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hz, hr, hf'⟩
  have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · have he₁ : D.erg f = some τ := ergSig hf he
    have heS : (D'.sigNr (E.num n)).erg = some (E.tyE τ) := by
      rw [hS.sigNr]; show Option.map E.tyE (D.sigNr n).erg = _; rw [he]; rfl
    have he' : D'.erg f' = some (E.tyE τ) := ergSig hf' heS
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_rest M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (ergWert he₁ (E.ergZ hZ (D.erg f) (castV (konform_sig hS hk).2.1 v'))) ρ)
      (.cons (ergWert he' v') ρ')
      (hI2 W)
      (E.envR_cons hZ hρ _ _ rfl (E.ergWert_ergZ hZ (konform_sig hS hk).2.1.symm he₁ he' v'))
    refine ⟨M₃, o.schrumpf, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg EndAusgang.schrumpf (hΦ3 Φ hP)
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha,
        execEnd_umΛ]
      exact E.endRel_schrumpf hR3
  · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
    exact (Fin.cast h0 r').elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execEndHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exEnd, execEndHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      trivial

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
