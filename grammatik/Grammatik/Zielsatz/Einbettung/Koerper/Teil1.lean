module
public import Grammatik.Zielsatz.Einbettung.Koerper.Teil1Basis
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

private theorem eval_index_n {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab}
    {σ : World D} {σ' : World D'} (i : Expr D Γ Λ (.index (D.count t)))
    (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE))
    (hi : E.VRel hZ (.index (D.count t)) (eval σ i σ ρ) (eval σ' (exE E i) σ' ρ')) :
    (eval σ' (Expr.umTy (E.countE t) (exE E i)) σ' ρ').n = (eval σ i σ ρ).n := by
  let mapped : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.index (D.count t)) := exE E i
  have same : (eval σ' mapped σ' ρ' : Zahl 0 (D.count t - 1)) = eval σ i σ ρ := hi
  exact ((congrArg (fun v : Zahl 0 (D'.count (E.tab t) - 1) => v.n)
    (eval_umTy (E.countE t) mapped σ' σ' ρ')).trans (castW_index_n (E.countE t) _)).trans
      (congrArg Zahl.n same)

section Sim

variable (hB : E.Bed hZ pad S T S' T' U' A')
include hB

set_option linter.unusedSectionVars false in
theorem sim_stmt_assignSlot {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.assignSlot t f i e hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' h hρ
  let index : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.index (D'.count (E.tab t))) :=
    Expr.umTy (E.countE t) (exE E i)
  let value : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (D'.typ (E.tab t) (E.feld t f)) :=
    Expr.umTy (E.typ t f).symm (exE E e)
  have reads : index.orte ++ value.orte = (i.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append ((Expr.orte_umTy (E.countE t) (exE E i)).trans (E.orte_exE i)))
      ((Expr.orte_umTy (E.typ t f).symm (exE E e)).trans (E.orte_exE e))).trans List.map_append.symm
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ h T hB.havocA hB.atom Λ (Λ.map E.resE)
    (i.orte ++ e.orte)
  let W := leseA A' σ' (Λ.map E.resE) ((i.orte ++ e.orte).map E.ortE)
  have hi : (eval W index W ρ').n = (eval σ₁ i σ₁ ρ).n := eval_index_n E hZ i ρ ρ' (hev i ρ ρ' hρ)
  have hv : E.VRel hZ _ (eval σ₁ e σ₁ ρ) (castW (E.typ t f) (eval W value W ρ')) := by
    simpa only [value, eval_umTy] using E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)
  refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
    fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · change E.AusRel hZ M₁ (.ok _ ρ)
      (.ok ((leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)).schreibSlot (E.tab t)
        (Λ.map E.resE)
        (eval (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) index
          (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) ρ').n (E.feld t f)
        (eval (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) value
          (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) ρ')) ρ')
    rw [reads]
    change E.Inv hZ M₁ _ (W.schreibSlot (E.tab t) (Λ.map E.resE)
      (eval W index W ρ').n (E.feld t f) (eval W value W ρ')) ∧ E.EnvR hZ ρ ρ'
    rw [hi]
    exact ⟨hI.schreibSlot E t Λ (Λ.map E.resE) _ f _ _ hv, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_assignVar {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_τ}
    (x)
    (e)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.assignVar (τ := zi_τ) x e : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' h hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ h T hB.havocA hB.atom Λ (Λ.map E.resE) e.orte
  have hev0 := E.frei_alle hZ (@hev) hρ
  refine ⟨M₁, .ok σ₁ (ρ.set x (eval σ₁ e σ₁ ρ)), hs, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
    exact ⟨hI, E.envR_set hZ ρ ρ' x _ _ hρ (hev e ρ ρ' hρ)⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_assignThru {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t ht f i e hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let index : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.index (D'.count (E.tab t))) :=
    Expr.umTy (E.countE t) (exE E i)
  let value : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (D'.typ (E.tab t) (E.feld t f)) :=
    Expr.umTy (E.typ t f).symm (exE E e)
  have tailReads : index.orte ++ value.orte = (i.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append ((Expr.orte_umTy (E.countE t) (exE E i)).trans (E.orte_exE i)))
      ((Expr.orte_umTy (E.typ t f).symm (exE E e)).trans (E.orte_exE e))).trans List.map_append.symm
  have reads : (exE E p).orte ++ index.orte ++ value.orte = (p.orte ++ i.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append (E.orte_exE p)) tailReads).trans List.map_append.symm
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ i.orte ++ e.orte)
  let W := leseA A' σ' (Λ.map E.resE) ((p.orte ++ i.orte ++ e.orte).map E.ortE)
  have hi : (eval W index W ρ').n = (eval σ₁ i σ₁ ρ).n := eval_index_n E hZ i ρ ρ' (hev i ρ ρ' hρ)
  have hv : E.VRel hZ _ (eval σ₁ e σ₁ ρ) (castW (E.typ t f) (eval W value W ρ')) := by
    simpa only [value, eval_umTy] using E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)
  refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
    fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · change E.AusRel hZ M₁ (.ok _ ρ)
      (.ok ((leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)).schreibSlot (E.tab t)
        (Λ.map E.resE)
        (eval (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) index
          (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) ρ').n (E.feld t f)
        (eval (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) value
          (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) ρ')) ρ')
    rw [reads]
    change E.Inv hZ M₁ _ (W.schreibSlot (E.tab t) (Λ.map E.resE)
      (eval W index W ρ').n (E.feld t f) (eval W value W ρ')) ∧ E.EnvR hZ ρ ρ'
    rw [hi]
    exact ⟨hI.schreibSlot E t Λ (Λ.map E.resE) _ f _ _ hv, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_assignThruOwn {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (ht)
    (f)
    (i)
    (e)
    (m)
    (s)
    (ho)
    (he)
    (hg)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.assignThruOwn (n := zi_n) (read := zi_read) (space := zi_space) (o := zi_eig) p t ht f i e m s ho he hg hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let index : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.index (D'.count (E.tab t))) :=
    Expr.umTy (E.countE t) (exE E i)
  let value : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (D'.typ (E.tab t) (E.feld t f)) :=
    Expr.umTy (E.typ t f).symm (exE E e)
  have tailReads : index.orte ++ value.orte = (i.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append ((Expr.orte_umTy (E.countE t) (exE E i)).trans (E.orte_exE i)))
      ((Expr.orte_umTy (E.typ t f).symm (exE E e)).trans (E.orte_exE e))).trans List.map_append.symm
  have reads : (exE E p).orte ++ index.orte ++ value.orte = (p.orte ++ i.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append (E.orte_exE p)) tailReads).trans List.map_append.symm
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (p.orte ++ i.orte ++ e.orte)
  let W := leseA A' σ' (Λ.map E.resE) ((p.orte ++ i.orte ++ e.orte).map E.ortE)
  have hi : (eval W index W ρ').n = (eval σ₁ i σ₁ ρ).n := eval_index_n E hZ i ρ ρ' (hev i ρ ρ' hρ)
  have hv : E.VRel hZ _ (eval σ₁ e σ₁ ρ) (castW (E.typ t f) (eval W value W ρ')) := by
    simpa only [value, eval_umTy] using E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)
  refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (eval σ₁ e σ₁ ρ)) ρ, hs,
    fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · change E.AusRel hZ M₁ (.ok _ ρ)
      (.ok ((leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)).schreibSlot (E.tab t)
        (Λ.map E.resE)
        (eval (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) index
          (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) ρ').n (E.feld t f)
        (eval (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) value
          (leseA A' σ' (Λ.map E.resE) ((exE E p).orte ++ index.orte ++ value.orte)) ρ')) ρ')
    rw [reads]
    change E.Inv hZ M₁ _ (W.schreibSlot (E.tab t) (Λ.map E.resE)
      (eval W index W ρ').n (E.feld t f) (eval W value W ρ')) ∧ E.EnvR hZ ρ ρ'
    rw [hi]
    exact ⟨hI.schreibSlot E t Λ (Λ.map E.resE) _ f _ _ hv, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_assignSlotRef {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_n}
    (r)
    (t)
    (ht)
    (ho)
    (f)
    (e)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.assignSlotRef (n := zi_n) r t ht ho f e hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let reference : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.ref (E.tnum zi_n)) := exE E r
  let value : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (D'.typ (E.tab t) (E.feld t f)) :=
    Expr.umTy (E.typ t f).symm (exE E e)
  have reads : reference.orte ++ value.orte = (r.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append (E.orte_exE r))
      ((Expr.orte_umTy (E.typ t f).symm (exE E e)).trans (E.orte_exE e))).trans List.map_append.symm
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (r.orte ++ e.orte)
  let W := leseA A' σ' (Λ.map E.resE) ((r.orte ++ e.orte).map E.ortE)
  have hr : (eval W reference W ρ').zelle = (eval σ₁ r σ₁ ρ).zelle := by
    have same := hev r ρ ρ' hρ
    change (eval W reference W ρ' : Nat) = (eval σ₁ r σ₁ ρ : Nat) at same
    exact same
  have hv : E.VRel hZ _ (eval σ₁ e σ₁ ρ) (castW (E.typ t f) (eval W value W ρ')) := by
    simpa only [value, eval_umTy] using E.vrel_um hZ (E.typ t f) (hev e ρ ρ' hρ)
  refine ⟨M₁, .ok (σ₁.schreibSlot t Λ ((eval σ₁ r σ₁ ρ).zelle : Int) f (eval σ₁ e σ₁ ρ)) ρ, hs,
    fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · change E.AusRel hZ M₁ (.ok _ ρ)
      (.ok ((leseA A' σ' (Λ.map E.resE) (reference.orte ++ value.orte)).schreibSlot (E.tab t)
        (Λ.map E.resE)
        ((eval (leseA A' σ' (Λ.map E.resE) (reference.orte ++ value.orte)) reference
          (leseA A' σ' (Λ.map E.resE) (reference.orte ++ value.orte)) ρ').zelle : Int) (E.feld t f)
        (eval (leseA A' σ' (Λ.map E.resE) (reference.orte ++ value.orte)) value
          (leseA A' σ' (Λ.map E.resE) (reference.orte ++ value.orte)) ρ')) ρ')
    rw [reads]
    change E.Inv hZ M₁ _ (W.schreibSlot (E.tab t) (Λ.map E.resE)
      ((eval W reference W ρ').zelle : Int) (E.feld t f) (eval W value W ρ')) ∧ E.EnvR hZ ρ ρ'
    rw [hr]
    exact ⟨hI.schreibSlot E t Λ (Λ.map E.resE) _ f _ _ hv, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_assignGlob {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g)
    (e)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.assignGlob g e hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.assignGlob g e hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (e.orte)
  have hev0 := E.frei_alle hZ (@hev) hρ
  refine ⟨M₁, .ok (σ₁.schreibGlob g Λ (eval σ₁ e σ₁ ρ)) ρ, hs, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · simp only [exS, execStmtHA, Expr.orte_umTy, Args.orte_umτs, Expr.orte_umΓ, Einbettung.orte_exE, Einbettung.orte_exA, Einbettung.orte_exErg, ← List.map_append, ← List.map_cons, ortE_inl, ortE_inr, eval_umTy, castW_index_n, valE_index_n, hev0 _ _ _ zf_int, hev0 _ _ _ zf_index, hev0 _ _ _ zf_bool, hev0 _ _ _ zf_opt, hev0 _ _ _ zf_why, hev0 _ _ _ zf_fl, hev0 _ _ _ zf_ref]
    exact ⟨hI.schreibGlob E g Λ _ _ _ (E.vrel_um hZ (E.gtyp g) (hev e ρ ρ' hρ)), hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_putBytes {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hf)
    (n)
    (i)
    (hlo)
    (hhi)
    (e)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.putBytes (lo := zi_lo) (hi := zi_hi) t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let index : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.int zi_lo zi_hi) := exE E i
  let value : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.int 0 (256 ^ n - 1)) := exE E e
  have reads : index.orte ++ value.orte = (i.orte ++ e.orte).map E.ortE :=
    (congr (congrArg List.append (E.orte_exE i)) (E.orte_exE e)).trans List.map_append.symm
  have hf' : D'.typ (E.tab t) (E.feld t f) = .int 0 255 :=
    (E.typ t f).trans (by simp only [hf, tyE, tyN, Ty.mapNumbers])
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (i.orte ++ e.orte)
  let W := leseA A' σ' (Λ.map E.resE) ((i.orte ++ e.orte).map E.ortE)
  have hi : (eval W index W ρ').n = (eval σ₁ i σ₁ ρ).n := by
    have same := hev i ρ ρ' hρ
    change (eval W index W ρ' : Zahl zi_lo zi_hi) = eval σ₁ i σ₁ ρ at same
    exact congrArg Zahl.n same
  have hv : (eval W value W ρ').n = (eval σ₁ e σ₁ ρ).n := by
    have same := hev e ρ ρ' hρ
    change (eval W value W ρ' : Zahl 0 (256 ^ n - 1)) = eval σ₁ e σ₁ ρ at same
    exact congrArg Zahl.n same
  refine ⟨M₁, .ok (σ₁.schreibBytes t f hf Λ (eval σ₁ i σ₁ ρ).n (zahlZuBytes n (eval σ₁ e σ₁ ρ).n)) ρ,
    hs, fun Φ hP => ?_, ?_⟩
  · simp only [execStmtHA, hΦ Φ hP]
  · change E.AusRel hZ M₁ (.ok _ ρ)
      (.ok ((leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)).schreibBytes (E.tab t)
        (E.feld t f) hf' (Λ.map E.resE)
        (eval (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) index
          (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) ρ').n
        (zahlZuBytes n (eval (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) value
          (leseA A' σ' (Λ.map E.resE) (index.orte ++ value.orte)) ρ').n)) ρ')
    rw [reads]
    change E.Inv hZ M₁ _ (W.schreibBytes (E.tab t) (E.feld t f) hf' (Λ.map E.resE)
      (eval W index W ρ').n (zahlZuBytes n (eval W value W ρ').n)) ∧ E.EnvR hZ ρ ρ'
    rw [hi, hv]
    exact ⟨hI.schreibBytes E t f hf hf' Λ (Λ.map E.resE) _ _, hρ⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_shift {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (t)
    (f)
    (hτ)
    (i)
    (von)
    (nach)
    (hn)
    (he)
    (hw)
    (hL)
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.shift (lo := zi_lo) (hi := zi_hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _)) (execStmtHA S' O' U' A' passes R' (exS hS (.shift (lo := zi_lo) (hi := zi_hi) t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ _))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let index : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.index (D'.count (E.tab t))) :=
    Expr.umTy (E.countE t) (exE E i)
  have reads : Sum.inl (E.tab t) :: index.orte = (Sum.inl t :: i.orte).map E.ortE :=
    congrArg (E.ortE (.inl t) :: ·) ((Expr.orte_umTy (E.countE t) (exE E i)).trans (E.orte_exE i))
  have hτ' : D'.typ (E.tab t) (E.feld t f) = .int zi_lo zi_hi :=
    (E.typ t f).trans (by simp only [hτ, tyE, tyN, Ty.mapNumbers])
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval hZ hM T hB.havocA hB.atom Λ (Λ.map E.resE)
    (Sum.inl t :: i.orte)
  let W := leseA A' σ' (Λ.map E.resE) ((Sum.inl t :: i.orte).map E.ortE)
  have hi : (eval W index W ρ').n = (eval σ₁ i σ₁ ρ).n := eval_index_n E hZ i ρ ρ' (hev i ρ ρ' hρ)
  have hn' := E.zahl_cast_n hZ hτ hτ' (E.typ t f)
    (σ₁.slots t (eval σ₁ i σ₁ ρ).n f) _ (hI.treu.1 t (eval σ₁ i σ₁ ρ).n f)
  have slot : (hτ' ▸ W.slots (E.tab t) (eval W index W ρ').n (E.feld t f) : Zahl zi_lo zi_hi).n =
      (hτ ▸ σ₁.slots t (eval σ₁ i σ₁ ρ).n f : Zahl zi_lo zi_hi).n :=
    (congrArg (fun k : Int => (hτ' ▸ W.slots (E.tab t) k (E.feld t f) : Zahl zi_lo zi_hi).n) hi).trans hn'
  have target : execStmtHA S' O' U' A' passes R'
      (exS hS (.shift t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ)) σ' ρ' =
      if (hτ ▸ σ₁.slots t (eval σ₁ i σ₁ ρ).n f : Zahl zi_lo zi_hi).n = von then
        .ok (W.schreibSlot (E.tab t) (Λ.map E.resE) (eval σ₁ i σ₁ ρ).n (E.feld t f)
          (hτ' ▸ (⟨nach, hn.1, hn.2⟩ : Zahl zi_lo zi_hi))) ρ'
      else .logik .vorzustand := by
    change (let w := leseA A' σ' (Λ.map E.resE) (Sum.inl (E.tab t) :: index.orte)
      if (hτ' ▸ w.slots (E.tab t) (eval w index w ρ').n (E.feld t f) : Zahl zi_lo zi_hi).n = von then
        .ok (w.schreibSlot (E.tab t) (Λ.map E.resE) (eval w index w ρ').n (E.feld t f)
          (hτ' ▸ (⟨nach, hn.1, hn.2⟩ : Zahl zi_lo zi_hi))) ρ'
      else .logik .vorzustand) = _
    rw [reads]
    change (if (hτ' ▸ W.slots (E.tab t) (eval W index W ρ').n (E.feld t f) : Zahl zi_lo zi_hi).n = von then
      .ok (W.schreibSlot (E.tab t) (Λ.map E.resE) (eval W index W ρ').n (E.feld t f)
        (hτ' ▸ (⟨nach, hn.1, hn.2⟩ : Zahl zi_lo zi_hi))) ρ' else .logik .vorzustand) = _
    rw [slot, hi]
  by_cases hc : (hτ ▸ σ₁.slots t (eval σ₁ i σ₁ ρ).n f : Zahl _ _).n = von
  · refine ⟨M₁, .ok (σ₁.schreibSlot t Λ (eval σ₁ i σ₁ ρ).n f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ,
      hs, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ hP]
      rw [if_pos hc]
    · rw [target, if_pos hc]
      exact ⟨hI.schreibSlot E t Λ (Λ.map E.resE) _ f _ _ (E.zahl_cast_wert hZ hτ hτ' (E.typ t f) _), hρ⟩
  · refine ⟨M₁, .logik .vorzustand, hs, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ hP]
      rw [if_neg hc]
    · rw [target, if_neg hc]
      exact ⟨logikRel_kein (fun _ h' => by cases h'), hI.keyOk E⟩

set_option linter.unusedSectionVars false in
theorem sim_stmt_ite {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (c)
    (t)
    (e)
    (ih_sim_block_e : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') e) (execBlockHA S' O' U' A' passes R' (exB hS e)))
    (ih_sim_block_t : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') t) (execBlockHA S' O' U' A' passes R' (exB hS t)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.ite c t e : Stmt D V l Γ Λ Λ')) (execStmtHA S' O' U' A' passes R' (exS hS (.ite c t e : Stmt D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let condition : Expr D' (Γ.map E.tyE) (Λ.map E.resE) .bool := exE E c
  have reads : condition.orte = c.orte.map E.ortE := E.orte_exE c
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
    c.orte condition.orte reads.symm
  let W := leseA A' σ' (Λ.map E.resE) condition.orte
  have hc : (eval W condition W ρ' : Bool) = eval σ₁ c σ₁ ρ := by
    have same := hev c ρ ρ' hρ
    change (eval W condition W ρ' : Bool) = eval σ₁ c σ₁ ρ at same
    exact same
  have target : execStmtHA S' O' U' A' passes R' (exS hS (.ite c t e : Stmt D V l Γ Λ Λ')) σ' ρ' =
      if (eval W condition W ρ' : Bool) then execBlockHA S' O' U' A' passes R' (exB hS t) W ρ'
      else execBlockHA S' O' U' A' passes R' (exB hS e) W ρ' := rfl
  cases hb : (eval σ₁ c σ₁ ρ : Bool)
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_e M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), wahr?, hb, Bool.false_eq_true, ↓reduceIte]
      exact hΦ2 Φ hP
    · simp only [target, hc, hb, Bool.false_eq_true, ↓reduceIte]
      exact hR
  · obtain ⟨M₂, o, hs2, hΦ2, hR⟩ := ih_sim_block_t M₁ σ₁ _ ρ ρ' hI hρ
    refine ⟨M₂, o, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
    · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), wahr?, hb, ↓reduceIte]
      exact hΦ2 Φ hP
    · simp only [target, hc, hb, ↓reduceIte]
      exact hR

set_option linter.unusedSectionVars false in
theorem sim_stmt_onOption {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (n)
    (o)
    (p)
    (a)
    (ih_sim_block_a : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') a) (execBlockHA S' O' U' A' passes R' (exB hS a)))
    (ih_sim_block_p : E.KoerperSim hZ (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') p) (execBlockHA S' O' U' A' passes R' (exB hS p)))
    : E.KoerperSim hZ (fun Φ => execStmtHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U') (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') (.onOption (n := n) o p a : Stmt D V l Γ Λ Λ')) (execStmtHA S' O' U' A' passes R' (exS hS (.onOption (n := n) o p a : Stmt D V l Γ Λ Λ'))) :=
  by
  intro M σ σ' ρ ρ' hM hρ
  let option : Expr D' (Γ.map E.tyE) (Λ.map E.resE) (.opt n) := exE E o
  let present : Block D' (E.vertragE V) l (.index n :: Γ.map E.tyE) (Λ.map E.resE) (Λ'.map E.resE) := exB hS p
  have reads : option.orte = o.orte.map E.ortE := E.orte_exE o
  obtain ⟨M₁, σ₁, hs, hΦ, hI, hev⟩ := E.lese_eval' hZ T hM hB.havocA hB.atom Λ (Λ.map E.resE)
    o.orte option.orte reads.symm
  let W := leseA A' σ' (Λ.map E.resE) option.orte
  have ho : (eval W option W ρ' : Option (Zahl 0 (n - 1))) = eval σ₁ o σ₁ ρ := by
    have same := hev o ρ ρ' hρ
    change (eval W option W ρ' : Option (Zahl 0 (n - 1))) = eval σ₁ o σ₁ ρ at same
    exact same
  have hp : E.KoerperSim hZ
      (fun Φ => execBlockHA S (E.orakelΦ hZ pad Φ O') (E.umweltΦ hZ Φ S U')
        (E.aumweltΦ hZ Φ T A') passes (E.rufΦ hZ hS pad Φ R') p)
      (execBlockHA S' O' U' A' passes R' present) := ih_sim_block_p
  have target : execStmtHA S' O' U' A' passes R' (exS hS (.onOption o p a : Stmt D V l Γ Λ Λ')) σ' ρ' =
      match (eval W option W ρ' : Option (Zahl 0 (n - 1))) with
      | none => execBlockHA S' O' U' A' passes R' (exB hS a) W ρ'
      | some k => (execBlockHA S' O' U' A' passes R' present W (.cons k ρ')).schrumpf := rfl
  cases hv : eval σ₁ o σ₁ ρ with
  | none =>
      obtain ⟨M₂, o', hs2, hΦ2, hR⟩ := ih_sim_block_a M₁ σ₁ _ ρ ρ' hI hρ
      refine ⟨M₂, o', teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hv]
        exact hΦ2 Φ hP
      · simp only [target, ho, hv]
        exact hR
  | some k =>
      obtain ⟨M₂, o', hs2, hΦ2, hR⟩ := hp M₁ σ₁ _ (Env.cons (τ := Ty.index n) k ρ)
        (Env.cons (τ := Ty.index n) k ρ') hI (E.envR_cons hZ hρ _ _ rfl rfl)
      refine ⟨M₂, o'.schrumpf, teil_trans hs hs2, fun Φ hP => ?_, ?_⟩
      · simp only [execStmtHA, hΦ Φ (passt_teil hP hs2), hv]
        exact congrArg Ausgang.schrumpf (hΦ2 Φ hP)
      · simp only [target, ho, hv]
        exact E.ausRel_schrumpf hR

end Sim
end Einbettung
end Gabbro.Grammatik.Einbettung
