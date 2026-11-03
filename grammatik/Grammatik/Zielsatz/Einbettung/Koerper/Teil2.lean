module

public import Grammatik.Zielsatz.Einbettung.Simulation
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil1

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
theorem sim_stmt_call {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (f)
    (args)
    (hp)
    (hr)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.call f args hp hr : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.call f args hp hr : Stmt D V l Γ Λ _))) :=
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
  · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, ha]
      exact ⟨hI2 W, hρ⟩
  · exact (Fin.cast (by rw [gruendeE hS, hr]) r' : Fin 0).elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, ha]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_stmt_callInd {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n)
    (p)
    (args)
    (hp)
    (hr)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.callInd (n := n) p args hp hr : Stmt D V l Γ Λ _))) :=
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
  · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact ⟨hI2 W, hρ⟩
  · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
    exact (Fin.cast h0 r').elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      trivial

set_option linter.unusedSectionVars false in
theorem sim_stmt_locks {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (hr)
    (body)
    (ih_sim_block_body : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') body) (execBlockHA S' O' U' A' passes R' (exB hS body)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.locks L hr body : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.locks L hr body : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI⟩ := E.umwelt_schritt hM S hB.havocU hB.orte L
  obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_body M₁ (σ₁.nimmt L) _ ρ ρ'
    hI hρ
  refine ⟨M₂, freiH S L o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2)]
    exact congrArg (freiH S L) (hΦ2 Φ hP)
  · simp only [exS, execStmtHA]
    exact E.freiH_rel S hB.inv L hR

set_option linter.unusedSectionVars false in
theorem sim_stmt_breaking {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (i)
    (body)
    (ih_sim_block_body : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') body) (execBlockHA S' O' U' A' passes R' (exB hS body)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.breaking i body : Stmt D V l Γ Λ Λ')) (execStmtHA S' O' U' A' passes R' (exS hS (.breaking i body : Stmt D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, o, hs, hΦ, hR⟩ := ih_sim_block_body M σ σ' ρ ρ' hM hρ
  exact ⟨M₁, o, hs, fun Φ hP => by simp only [execStmtHA]; exact hΦ Φ hP,
    by simp only [exS, execStmtHA]; exact hR⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_traverse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (ih_sim_block_body : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') body) (execBlockHA S' O' U' A' passes R' (exB hS body)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.traverse t inv body : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.traverse t inv body : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  have hsb := E.koerperSim_block_um hZ S' O' U' A' passes R'
    (show (Ty.index (D.count t) :: Γ).map E.tyE = Ty.index (D'.count (E.tab t)) :: Γ.map E.tyE by
      rw [List.map_cons, E.count]) _ _ (ih_sim_block_body)
  have hi := E.pruef_sim hZ T hB.havocA hB.atom inv
  exact E.traverse_sim (l := l) _ _ _ _ hsb hi
    (fun k => castW (D := D') (show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by
      rw [E.count]) k)
    (fun k => ⟨(show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by rw [E.count]).symm,
      castW_symm (D := D') (τ := Ty.index (D'.count (E.tab t))) (σ := Ty.index (D.count t)) _ k⟩)
    (alleIndizes (D.count t))
    (alleIndizes (D'.count (E.tab t)))
    (Einbettung.alleIndizes_bild (D' := D') (E.count t)) M σ σ' ρ ρ' hM hρ

set_option linter.unusedSectionVars false in
theorem sim_stmt_consumeTraverse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (member)
    (edge)
    (inv)
    (bound)
    (mass)
    (body)
    (ih_sim_block_body : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') body) (execBlockHA S' O' U' A' passes R' (exB hS body)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  have hsb := E.koerperSim_block_um hZ S' O' U' A' passes R'
    (show (Ty.index (D.count t) :: Γ).map E.tyE = Ty.index (D'.count (E.tab t)) :: Γ.map E.tyE by
      rw [List.map_cons, E.count]) _ _ (ih_sim_block_body)
  have hi := E.pruef_sim hZ T hB.havocA hB.atom inv
  have hf : ∀ k : Wert D (.index (D.count t)),
      ∃ h : (Ty.index (D'.count (E.tab t))) = E.tyE (Ty.index (D.count t)),
        E.VRel hZ _ k (castW h ((fun k => castW (D := D')
          (show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by rw [E.count]) k))) :=
    fun k => ⟨(show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by rw [E.count]).symm,
      castW_symm (D := D') (τ := Ty.index (D'.count (E.tab t))) (σ := Ty.index (D.count t)) _ k⟩
  simp only [execStmtHA, exS]
  rw [show (D'.count (E.tab t)).toNat + bound.toNat + 1 =
    (D.count t).toNat + bound.toNat + 1 from by rw [E.count t]]
  refine E.verbrauch_sim (l := l) t bound _ _ _ _ _ _ _ _ hsb hi
    (fun k => castW (D := D') (show Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) by
      rw [E.count]) k)
    hf ?hsel ?hmass ((D.count t).toNat + bound.toNat + 1) M σ σ' ρ ρ' hM hρ
  · intro M₀ σ₀ σ₀' ρ₀ ρ₀' hM₀ hρ₀
    obtain ⟨M₁, σ₁, hs1, hΦ1, hI1, hev⟩ := E.lese_eval' hZ T hM₀ hB.havocA hB.atom
      Λ (Λ.map E.resE) (member.orte ++ edge.orte)
      ((exE E member).orte ++ (exE E edge).orte)
      (by simp only [List.map_append, E.orte_exE])
    simp only [verbrauchSelA, Expr.orte_umΓ] at ⊢
    refine ⟨M₁, σ₁, _, _, _, hs1, ?_, ?_, ?_⟩
    · intro Φ hP
      simp only [verbrauchSelA, hΦ1 Φ hP]
    · simp only [verbrauchSelA, Expr.orte_umΓ, eval_umΓ]
      rw [Prod.mk.injEq, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · rfl
      · rw [alleIndizes_bild ((E.count t).symm)]
        refine verbrauchWahl_map _ _ _ _ _ _ _ _ ?_ ?_ ?_
        · intro k _
          have henv : E.EnvR hZ (Env.cons k ρ₀)
              (Env.cons ((fun k => castW (D := D') (show Ty.index (D.count t) =
                Ty.index (D'.count (E.tab t)) by rw [E.count]) k) (castE _ ρ₀')) :=
            ⟨hf k, (E.envR_um hZ _ _ _).mpr hρ₀⟩
          have h := hev member (Env.cons k ρ₀) _ henv
          simp only [VRel] at h
          show wahr? _ = wahr? _
          simp only [h]
        · intro j _ k _
          have henv : E.EnvR hZ (Env.cons j (Env.cons k ρ₀))
              (Env.cons ((fun k => castW (D := D') (show Ty.index (D.count t) =
                Ty.index (D'.count (E.tab t)) by rw [E.count]) j)
                (Env.cons ((fun k => castW (D := D') (show Ty.index (D.count t) =
                  Ty.index (D'.count (E.tab t)) by rw [E.count]) k) (castE _ ρ₀'))) :=
            ⟨hf j, hf k, (E.envR_um hZ _ _ _).mpr hρ₀⟩
          have h := hev edge (Env.cons j (Env.cons k ρ₀)) _ henv
          simp only [VRel] at h
          show wahr? _ = wahr? _
          simp only [h]
        · intro j _ k _
          show decide (_ = _) = decide (_ = _)
          rw [castW_index_n, castW_index_n]
      · exact map_all_beibehalt _ _ _ _ (fun k _ => by
          have henv : E.EnvR hZ (Env.cons k ρ₀)
              (Env.cons ((fun k => castW (D := D') (show Ty.index (D.count t) =
                Ty.index (D'.count (E.tab t)) by rw [E.count]) k) (castE _ ρ₀')) :=
            ⟨hf k, (E.envR_um hZ _ _ _).mpr hρ₀⟩
          have h := hev member (Env.cons k ρ₀) _ henv
          simp only [VRel] at h
          show (!(wahr? _)) = (!(wahr? _))
          simp only [h])
    · exact hI1
  · intro M₀ σ₀ σ₀' ρ₀ ρ₀' hM₀ hρ₀
    obtain ⟨M₁, σ₁, hs1, hΦ1, hI1, hev⟩ := E.lese_eval' hZ T hM₀ hB.havocA hB.atom
      Λ (Λ.map E.resE) mass.orte (exE E mass).orte (E.orte_exE mass).symm
    refine ⟨M₁, σ₁, _, (eval σ₁ mass σ₁ ρ₀).n, hs1, ?_, ?_, ?_⟩
    · intro Φ hP
      simp only [hΦ1 Φ hP]
    · have hm' := hev mass ρ₀ ρ₀' hρ₀
      simp only [VRel] at hm'
      simp only [hm']
    · exact hI1

set_option linter.unusedSectionVars false in
theorem sim_stmt_retry {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (ueber)
    (ih_sim_block_body : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') body) (execBlockHA S' O' U' A' passes R' (exB hS body)))
    (ih_sim_block_ueber : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') ueber) (execBlockHA S' O' U' A' passes R' (exB hS ueber)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.retry n bis body ueber : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.retry n bis body ueber : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact E.retry_sim _ _ _ _ _ _ (ih_sim_block_body) (E.pruef_sim hZ T hB.havocA hB.atom bis)
    (ih_sim_block_ueber) n M σ σ' ρ ρ' hM hρ

set_option linter.unusedSectionVars false in
theorem sim_stmt_forever {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (ih_sim_block_body : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') body) (execBlockHA S' O' U' A' passes R' (exB hS body)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.forever a inv body : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.forever a inv body : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  exact E.forever_sim a (E.annahme a) _ _ _ _ (ih_sim_block_body)
    (E.pruef_sim hZ T hB.havocA hB.atom inv) passes M σ σ' ρ ρ' hM hρ

set_option linter.unusedSectionVars false in
theorem sim_stmt_axiomCall {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (a)
    (args)
    (h)
    (hw)
    (hg)
    (hd)
    (hgd)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.axiomCall a args h hw hg hd hgd : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  obtain ⟨M₂, hs2, hOΦ, hI2⟩ := E.ax_schluessel hZ pad O' (hI.fragt E (.inl a) (.inl (E.ax a))) a (evalArgs σ₁ args σ₁ ρ)
  have hargs := E.envR_eq_frei hZ (hZ.frei.aparamsFrei a) _ _ (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ)
  have hw' := E.axiom_wert hZ (fun _ => Option.none) O'.zeiger a
    (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a)))
      (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 (E.aerg a)
  cases hx : einpassenErg (fun _ => Option.none) (D.aerg a)
      (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE) (args.orte.map E.ortE)).fragt (.inl (E.ax a)))
        (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).2 with
  | none =>
      refine ⟨M₂, .hardware (.annahme a), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger]
        rw [hx]
      · simp only [exS, execStmtHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Einbettung.orte_exA,
          evalArgs_umτs, hargs, aparamsUm_falt, hw']
        rw [hx]
        trivial
  | some v =>
      refine ⟨M₂, .ok (E.antwortWelt hZ pad (σ₁.fragt (.inl a)) (O'.wirkt (E.ax a) ((leseA A' σ' (Λ.map E.resE)
        (args.orte.map E.ortE)).fragt (.inl (E.ax a))) (E.aparamsUm a (evalArgs σ₁ args σ₁ ρ))).1) ρ, teil_trans hs hs2,
        fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, axiomAntwort, hΦ Φ (passt_teil hP hs2), hOΦ Φ hP, orakelΦ_zeiger, hx]
      · simp only [exS, execStmtHA, axiomAntwort, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, evalArgs_umτs, hargs, aparamsUm_falt, hw', hx,
          Option.map_some]
        exact ⟨E.inv_antwort hZ hB.pad hI2 _, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_callIndElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (n)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.callIndElse (n := n) p args he hp hr err : Stmt D V l Γ Λ _))) :=
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
  have hchan : (D'.sigNr (E.num n)).gruende = (D.sigNr n).gruende := by rw [hS.sigNr]; rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact ⟨hI2 W, hρ⟩
  · have hc : (Ty.why (D.sigNr n).gruende :: Γ).map E.tyE
        = Ty.why (D'.sigNr (E.num n)).gruende :: Γ.map E.tyE := by rw [hS.sigNr]; rfl
    have hrw : D'.gruende f' = (D'.sigNr (E.num n)).gruende :=
      (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hchan.symm)
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad σ₁ W) W
      (.cons (Fin.cast ((konform_sig hS hk).2.2.trans (D.passt_sig hf).gruende) r') ρ)
      (castE hc.symm (.cons (Fin.cast hrw r') ρ'))
      (hI2 W)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons hZ hρ _ _ rfl (by rw [castW_why]; rfl)))
    refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg (fun x => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
    · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · simp only [exS, exec_nachΛ, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hvd', evalArgs_umτs, ha]
      trivial

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
