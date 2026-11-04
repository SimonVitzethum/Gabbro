/- Part 10 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9EndFloat
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem schrittErhalt_g6 {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Lock → Prop}
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG6 P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestG A r) :
    ErhaltG O passes A M M' f z ρ r := by
  subst hz
  unfold ErhaltG
  cases hs with
  | endeBindAxiomElseOk =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | endeBindAxiomElseGrund =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | endeBindAxiomOptElseOk =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | endeBindAxiomOptElseGrund =>
    have hhead := ‹(M.faeden f).kopf.rest = _›; widerlege hhead
  | endeGleit l Γ Λ l₁ h₁ l₂ h₂ op a b lo hi rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    simp only [Endblock.ohneOrakel, Stmt.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende _ hb.gleit_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeGleit O passes op a b lo hi rest _ _ v hv)
  | endeGleitLit l Γ Λ q lo hi rest ρ hhead v hv =>
    rw [hR] at hhead
    cases hhead
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    simp only [Endblock.ohneOrakel, Stmt.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende _ hb.gleitLit_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeGleitLit O passes q lo hi rest _ _ v hv)
  | endeGleitVon l Γ Λ l₁ h₁ e lo hi rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    simp only [Endblock.ohneOrakel, Stmt.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende _ hb.gleitVon_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeGleitVon O passes e lo hi rest _ _ v hv)
  | endeGleitNarrowOk l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
    simp only [Endblock.ohneOrakel, Stmt.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestG.ende _ hr ho.2, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeGleitNarrowOk O passes e lo hi sonst rest _ _ v hv)
  | endeGleitNarrowElse l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    rw [hR] at hhead
    cases hhead
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
    simp only [Endblock.ohneOrakel, Stmt.ohneOrakel, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _,
      RestG.ende _ hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (sem_endeGleitNarrowElse O passes e lo hi sonst rest _ _ hn)

end Gabbro.Grammatik
