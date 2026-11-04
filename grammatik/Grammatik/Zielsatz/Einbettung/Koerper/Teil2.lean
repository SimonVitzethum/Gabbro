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
  have pointerReads : Expr.orte (D := D') (Γ := Γ.map E.tyE) (Λ := Λ.map E.resE)
      (τ := .fnptr (E.num n)) (exE E p) = p.orte.map E.ortE := E.orte_exE p
  have actualReads : List.append (Expr.orte (D := D') (τ := .fnptr (E.num n)) (exE E p))
      (List.map E.ortE args.orte) = List.map E.ortE (List.append p.orte args.orte) :=
    (congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => List.append xs (List.map E.ortE args.orte))
      pointerReads).trans List.map_append.symm
  have readWorld : leseA A' σ' (Λ.map E.resE)
      (List.append (Expr.orte (D := D') (τ := .fnptr (E.num n)) (exE E p)) (List.map E.ortE args.orte)) =
      leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE) :=
    congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => leseA A' σ' (Λ.map E.resE) xs) actualReads
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
  have hp' := hev p ρ ρ' hρ
  rw [hvd] at hp'
  rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
  rw [hvd'] at hp'
  have pointerValue : eval (D := D') (τ := .fnptr (E.num n))
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p)
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' = ⟨f', hf'⟩ := hvd'
  have hk : E.Konform hZ f f' := by
    rcases hp' with h | ⟨hz, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hz, hr, hf'⟩
  have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
  let read : World D' := leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)
  let callArgs : Env D' (D'.params f') := umsig hf' (castE hsig (evalArgs read (exA E args) read ρ'))
  have noReason : (D'.sigNr (E.num n)).gruende = 0 := by rw [hS.sigNr]; exact hr
  have target : execStmtHA S' O' U' A' passes R' (exS hS (.callInd p args hp hr : Stmt D V l Γ Λ _)) σ' ρ' =
      (match R' f' read callArgs with
      | .ok W _ => .ok W ρ'
      | .why _ r => keinGrundSig hf' noReason r
      | .logik e => .logik e
      | .hardware e => .hardware e : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exS, exec_nachΛ, execStmtHA, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs]
    erw [readWorld, pointerValue] <;> rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  have answer : R' f' read callArgs = a' := ha
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      exact ⟨hI2 W, hρ⟩
  · have h0 : D'.gruende f' = 0 := (konform_sig hS hk).2.2.trans ((D.passt_sig hf).gruende.trans hr)
    exact (Fin.cast h0 r').elim0
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
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
      rw [List.map_cons, E.count] <;> rfl) _ _ (ih_sim_block_body)
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
  have countTy : Ty.index (D.count t) = Ty.index (D'.count (E.tab t)) :=
    congrArg Ty.index (E.count t).symm
  have scope : (Ty.index (D.count t) :: Γ).map E.tyE =
      Ty.index (D'.count (E.tab t)) :: Γ.map E.tyE := by
    rw [List.map_cons, E.count] <;> rfl
  have scope2 : (Ty.index (D.count t) :: Ty.index (D.count t) :: Γ).map E.tyE =
      Ty.index (D'.count (E.tab t)) :: Ty.index (D'.count (E.tab t)) :: Γ.map E.tyE := by
    rw [List.map_cons, List.map_cons, E.count] <;> rfl
  let castIndex (k : Wert D (.index (D.count t))) : Wert D' (.index (D'.count (E.tab t))) :=
    castW (D := D') countTy k
  let member' : Expr D' (.index (D'.count (E.tab t)) :: Γ.map E.tyE) (Λ.map E.resE) .bool :=
    Expr.umΓ scope (exE E member)
  let edge' : Expr D' (.index (D'.count (E.tab t)) :: .index (D'.count (E.tab t)) :: Γ.map E.tyE)
      (Λ.map E.resE) .bool := Expr.umΓ scope2 (exE E edge)
  have selectorReads : List.append
      (Expr.orte (D := D') (τ := .bool) (Expr.umΓ scope (exE E member)))
      (Expr.orte (D := D') (τ := .bool) (Expr.umΓ scope2 (exE E edge))) =
      List.append (exE E member).orte (exE E edge).orte :=
    congr (congrArg List.append (Expr.orte_umΓ (D := D') (τ := .bool) scope (exE E member)))
      (Expr.orte_umΓ (D := D') (τ := .bool) scope2 (exE E edge))
  have hsb := E.koerperSim_block_um hZ S' O' U' A' passes R'
    scope _ _ ih_sim_block_body
  have hi := E.pruef_sim hZ T hB.havocA hB.atom inv
  have hf : ∀ k : Wert D (.index (D.count t)),
      ∃ h : Ty.index (D'.count (E.tab t)) = E.tyE (Ty.index (D.count t)),
        E.VRel hZ _ k (castW h (castIndex k)) := by
    intro k
    refine ⟨countTy.symm, ?_⟩
    change castW (D := D') countTy.symm (castW (D := D') countTy k) = k
    exact castW_symm (D := D') countTy.symm k
  simp only [execStmtHA, exS]
  rw [show (D'.count (E.tab t)).toNat + bound.toNat + 1 =
    (D.count t).toNat + bound.toNat + 1 from by rw [E.count t]]
  refine E.verbrauch_sim (l := l) t bound _ _ _ _ _ _ _ _ hsb hi
    castIndex hf ?hsel ?hmass ((D.count t).toNat + bound.toNat + 1) M σ σ' ρ ρ' hM hρ
  · intro M₀ σ₀ σ₀' ρ₀ ρ₀' hM₀ hρ₀
    have reads : (exE E member).orte ++ (exE E edge).orte =
        (member.orte ++ edge.orte).map E.ortE :=
      (congr (congrArg List.append (E.orte_exE member)) (E.orte_exE edge)).trans List.map_append.symm
    obtain ⟨M₁, σ₁, hs1, hΦ1, hI1, hev⟩ := E.lese_eval' hZ T hM₀ hB.havocA hB.atom
      Λ (Λ.map E.resE) (member.orte ++ edge.orte)
      ((exE E member).orte ++ (exE E edge).orte) reads.symm
    let W := leseA A' σ₀' (Λ.map E.resE) ((exE E member).orte ++ (exE E edge).orte)
    have selectorWorld : leseA A' σ₀' (Λ.map E.resE) (List.append
        (Expr.orte (D := D') (τ := .bool) (Expr.umΓ scope (exE E member)))
        (Expr.orte (D := D') (τ := .bool) (Expr.umΓ scope2 (exE E edge)))) = W :=
      congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => leseA A' σ₀' (Λ.map E.resE) xs) selectorReads
    let p (w : World D) (k : Wert D (.index (D.count t))) : Bool :=
      wahr? (D := D) (eval w member w (Env.cons (τ := .index (D.count t)) k ρ₀))
    let e (w : World D) (j k : Wert D (.index (D.count t))) : Bool :=
      wahr? (D := D) (eval w edge w (.cons j (.cons k ρ₀)))
    let same (j k : Zahl 0 (D.count t - 1)) : Bool := decide (j.n = k.n)
    let p' (k : Wert D' (.index (D'.count (E.tab t)))) : Bool :=
      wahr? (D := D') (eval W member' W (.cons k ρ₀'))
    let e' (j k : Wert D' (.index (D'.count (E.tab t)))) : Bool :=
      wahr? (D := D') (eval W edge' W (.cons j (.cons k ρ₀')))
    let same' (j k : Zahl 0 (D'.count (E.tab t) - 1)) : Bool := decide (j.n = k.n)
    have hp : ∀ k, p' (castIndex k) = p σ₁ k := by
      intro k
      have henv := (E.envR_um hZ scope.symm _ _).mpr
        (show E.EnvR hZ (Env.cons k ρ₀) (Env.cons (castIndex k) ρ₀') from ⟨hf k, hρ₀⟩)
      have h := hev member (.cons k ρ₀) _ henv
      change (eval W (exE E member) W (castE scope.symm (.cons (castIndex k) ρ₀')) : Bool) =
        eval σ₁ member σ₁ (.cons k ρ₀) at h
      exact (congrArg (wahr? (D := D')) (eval_umΓ (τ := .bool) scope (exE E member) W W
        (.cons (castIndex k) ρ₀'))).trans h
    have he : ∀ j k, e' (castIndex j) (castIndex k) = e σ₁ j k := by
      intro j k
      have henv := (E.envR_um hZ scope2.symm _ _).mpr
        (show E.EnvR hZ (.cons j (.cons k ρ₀)) (.cons (castIndex j) (.cons (castIndex k) ρ₀'))
          from ⟨hf j, hf k, hρ₀⟩)
      have h := hev edge (.cons j (.cons k ρ₀)) _ henv
      change (eval W (exE E edge) W (castE scope2.symm (.cons (castIndex j) (.cons (castIndex k) ρ₀'))) : Bool) =
        eval σ₁ edge σ₁ (.cons j (.cons k ρ₀)) at h
      exact (congrArg (wahr? (D := D')) (eval_umΓ (τ := .bool) scope2 (exE E edge) W W
        (.cons (castIndex j) (.cons (castIndex k) ρ₀')))).trans h
    have hs : ∀ j k, same' (castIndex j) (castIndex k) = same j k := by
      intro j k
      have hj : (castIndex j).n = j.n := castW_index_n (D₀ := D') countTy j
      have hk : (castIndex k).n = k.n := castW_index_n (D₀ := D') countTy k
      exact congr (congrArg (fun a b : Int => decide (a = b)) hj) hk
    have domain : alleIndizes (D'.count (E.tab t)) = (alleIndizes (D.count t)).map castIndex :=
      alleIndizes_bild (D' := D') (E.count t)
    have choice := (congrArg (fun ks : List (Wert D' (.index (D'.count (E.tab t)))) =>
      verbrauchWahl ks p' e' same') domain).trans
      (verbrauchWahl_map castIndex (alleIndizes (D.count t)) (p σ₁) p' (e σ₁) e' same same'
        (fun k _ => hp k) (fun j _ k _ => he j k) (fun j _ k _ => hs j k))
    have remaining := congrArg Bool.not ((congrArg
      (fun ks : List (Wert D' (.index (D'.count (E.tab t)))) => ks.all (fun k => !(p' k))) domain).trans
      (map_all_beibehalt castIndex (alleIndizes (D.count t)) (fun k => !(p σ₁ k)) (fun k => !(p' k))
        (fun k _ => congrArg Bool.not (hp k))))
    refine ⟨M₁, σ₁, W, verbrauchWahl (alleIndizes (D.count t)) (p σ₁) (e σ₁) same,
      !((alleIndizes (D.count t)).all (fun k => !(p σ₁ k))), hs1, ?_, ?_, hI1⟩
    · intro Φ hP
      change (fun w : World D => (w, verbrauchWahl (alleIndizes (D.count t)) (p w) (e w) same,
        !((alleIndizes (D.count t)).all (fun k => !(p w k)))))
          (leseA (E.aumweltΦ hZ Φ T A') σ₀ Λ (member.orte ++ edge.orte)) = _
      exact congrArg (fun w : World D => (w, verbrauchWahl (alleIndizes (D.count t)) (p w) (e w) same,
        !((alleIndizes (D.count t)).all (fun k => !(p w k))))) (hΦ1 Φ hP)
    · simp only [verbrauchSelA]
      erw [selectorWorld]
      change (W, verbrauchWahl (alleIndizes (D'.count (E.tab t))) p' e' same',
        !((alleIndizes (D'.count (E.tab t))).all (fun k => !(p' k)))) = _
      exact congrArg (fun data : Option (Wert D' (.index (D'.count (E.tab t)))) × Bool => (W, data))
        (congr (congrArg Prod.mk choice) remaining)
  · intro M₀ σ₀ σ₀' ρ₀ ρ₀' hM₀ hρ₀
    obtain ⟨M₁, σ₁, hs1, hΦ1, hI1, hev⟩ := E.lese_eval' hZ T hM₀ hB.havocA hB.atom
      Λ (Λ.map E.resE) mass.orte (exE E mass).orte (E.orte_exE mass).symm
    let W : World D' := leseA A' σ₀' (Λ.map E.resE) (exE E mass).orte
    let m : Zahl 0 bound := eval σ₁ mass σ₁ ρ₀
    have hm' : (eval W (exE E mass) W ρ₀' : Zahl 0 bound) = m := by
      have same := hev mass ρ₀ ρ₀' hρ₀
      change (eval W (exE E mass) W ρ₀' : Zahl 0 bound) = m at same
      exact same
    have measured : (W, (eval W (exE E mass) W ρ₀' : Zahl 0 bound).n) = (W, m.n) :=
      congrArg (fun value : Zahl 0 bound => (W, value.n)) hm'
    refine ⟨M₁, σ₁, W, m.n, hs1, ?_, measured, hI1⟩
    intro Φ hP
    exact congrArg (fun w : World D => (w, (eval (D := D) (τ := .int 0 bound) w mass w ρ₀ : Zahl 0 bound).n)) (hΦ1 Φ hP)

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
theorem sim_stmt_callIndElse {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (n)
    (p)
    (args)
    (he : (D.sigNr n).erg = some τ)
    (hp)
    (hr)
    (err)
    (ih_sim_end_err : E.EndSim hZ (fun Φ => execEndHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') err) (execEndHA S' O' U' A' passes R' (exEnd hS err)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.callIndElse (n := n) (τ := τ) p args he hp hr err : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.callIndElse (n := n) (τ := τ) p args he hp hr err : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  have pointerReads : Expr.orte (D := D') (Γ := Γ.map E.tyE) (Λ := Λ.map E.resE)
      (τ := .fnptr (E.num n)) (exE E p) = p.orte.map E.ortE := E.orte_exE p
  have actualReads : List.append (Expr.orte (D := D') (τ := .fnptr (E.num n)) (exE E p))
      (List.map E.ortE args.orte) = List.map E.ortE (List.append p.orte args.orte) :=
    (congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => List.append xs (List.map E.ortE args.orte))
      pointerReads).trans List.map_append.symm
  have readWorld : leseA A' σ' (Λ.map E.resE)
      (List.append (Expr.orte (D := D') (τ := .fnptr (E.num n)) (exE E p)) (List.map E.ortE args.orte)) =
      leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE) :=
    congrArg (fun xs : List (D'.Tab ⊕ D'.Glob) => leseA A' σ' (Λ.map E.resE) xs) actualReads
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ args.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  rcases hvd : eval σ₁ p σ₁ ρ with ⟨f, hf⟩
  have hp' := hev p ρ ρ' hρ
  rw [hvd] at hp'
  rcases hvd' : eval (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' with ⟨f', hf'⟩
  rw [hvd'] at hp'
  have pointerValue : eval (D := D') (τ := .fnptr (E.num n))
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exE E p)
      (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ' = ⟨f', hf'⟩ := hvd'
  have hk : E.Konform hZ f f' := by
    rcases hp' with h | ⟨hz, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hz, hr, hf'⟩
  have hsig : (D.sigNr n).params.map E.tyE = (D'.sigNr (E.num n)).params := by rw [hS.sigNr]; rfl
  have hchan : (D'.sigNr (E.num n)).gruende = (D.sigNr n).gruende := by rw [hS.sigNr]; rfl
  have hc : (Ty.why (D.sigNr n).gruende :: Γ).map E.tyE =
      Ty.why (D'.sigNr (E.num n)).gruende :: Γ.map E.tyE := by rw [hS.sigNr]; rfl
  let read : World D' := leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)
  let callArgs : Env D' (D'.params f') := umsig hf' (castE hsig (evalArgs read (exA E args) read ρ'))
  let error : Endblock D' (E.vertragE V) l (.why (D'.sigNr (E.num n)).gruende :: Γ.map E.tyE)
      (nachSig D' (D'.sigNr (E.num n)) (Λ.map E.resE)) :=
    Endblock.umΓ hc (Endblock.umΛ (nachSigE_nr hS n Λ) (exEnd hS err))
  have target : execStmtHA S' O' U' A' passes R'
      (exS hS (.callIndElse (τ := τ) p args he hp hr err : Stmt D V l Γ Λ _)) σ' ρ' =
      (match R' f' read callArgs with
      | .ok W _ => .ok W ρ'
      | .why W r => (execEndHA S' O' U' A' passes R' error W
          (Env.cons (τ := .why (D'.sigNr (E.num n)).gruende) (grundSig hf' r) ρ')).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e : Ausgang (E.vertragE V) l (Γ.map E.tyE)) := by
    simp only [exS, exec_nachΛ, execStmtHA, indSonst, Args.orte_umτs, Einbettung.orte_exA, evalArgs_umτs]
    erw [readWorld, pointerValue] <;> rfl
  obtain ⟨M₂, hs2, hRΦ, hI2⟩ := E.ruf_schritt hZ hS pad R' hB.pad hI f (umsig hf (evalArgs σ₁ args σ₁ ρ)) f'
    (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ')))
    (E.envR_umsig hZ hf hf' _ _ ((E.envR_um hZ hsig _ _).mpr
      (E.evalArgs_exA hZ hI.treu hI.treu args ρ ρ' hρ))) hk
  generalize ha : R' f' (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (umsig hf' (castE hsig (evalArgs (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) (exA E args) (leseA A' σ' (Λ.map E.resE) ((p.orte ++ args.orte).map E.ortE)) ρ'))) = a' at hRΦ
  have answer : R' f' read callArgs = a' := ha
  rcases a' with ⟨W, v'⟩ | ⟨W, r'⟩ | e' | e'
  · refine ⟨M₂, .ok (E.antwortWelt hZ pad σ₁ W) ρ, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, indSonst, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      exact ⟨hI2 W, hρ⟩
  · let sourceReason : Fin (D.sigNr n).gruende :=
      grundSig hf (Fin.cast (konform_sig hS hk).2.2 r')
    let targetReason : Fin (D'.sigNr (E.num n)).gruende := grundSig hf' r'
    have sourceNumber : sourceReason.val = r'.val :=
      congrArg Fin.val (grundSig_eq_cast hf (D.passt_sig hf).gruende
        (Fin.cast (konform_sig hS hk).2.2 r'))
    have targetNumber : targetReason.val = r'.val :=
      congrArg Fin.val (grundSig_eq_cast hf' (D'.passt_sig hf').gruende r')
    have reasonTy : Ty.why (D'.sigNr (E.num n)).gruende = E.tyE (.why (D.sigNr n).gruende) := by
      rw [hchan] <;> rfl
    have reasons : E.VRel hZ (.why (D.sigNr n).gruende) sourceReason (castW reasonTy targetReason) := by
      change (castW (D := D') reasonTy targetReason : Fin (D.sigNr n).gruende) = sourceReason
      apply Fin.ext
      exact (congrArg Fin.val (castW_why (D' := D') reasonTy targetReason)).trans
        (targetNumber.trans sourceNumber.symm)
    obtain ⟨M₃, o, hs3, hΦ3, hR3⟩ := ih_sim_end_err M₂ (E.antwortWelt hZ pad σ₁ W) W
      (Env.cons (τ := .why (D.sigNr n).gruende) sourceReason ρ)
      (castE hc.symm (Env.cons (τ := .why (D'.sigNr (E.num n)).gruende) targetReason ρ'))
      (hI2 W)
      ((E.envR_um hZ hc.symm _ _).mpr (E.envR_cons (τ := .why (D.sigNr n).gruende)
        (τ' := .why (D'.sigNr (E.num n)).gruende) hZ hρ sourceReason targetReason reasonTy reasons))
    refine ⟨M₃, o.schrumpf.zuAusgang, teil_trans (teil_trans hs hs2) hs3, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, indSonst, hΦ Φ (passt_teil hP (teil_trans hs2 hs3)), hvd, hRΦ Φ (passt_teil hP hs3),
        antwortR]
      exact congrArg (fun x : EndAusgang V l (.why (D.sigNr n).gruende :: Γ) => x.schrumpf.zuAusgang) (hΦ3 Φ hP)
    · rw [target, answer]
      simp only [error, execEnd_umΓ, execEnd_umΛ]
      exact E.endRel_zuAusgang (E.endRel_schrumpf ((E.endRel_um hc o _).mpr hR3))
  · refine ⟨M₂, .logik (logikZ f e'), teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, indSonst, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      exact ⟨logikRel_logikZ f e', (hI2 σ').keyOk E⟩
  · refine ⟨M₂, .hardware .ieee, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, indSonst, hΦ Φ (passt_teil hP hs2), hvd, hRΦ Φ hP, antwortR]
    · rw [target, answer]
      trivial

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
