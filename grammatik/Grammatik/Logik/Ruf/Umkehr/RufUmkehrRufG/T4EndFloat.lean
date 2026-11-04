/- Part 4 of 6 of `RufUmkehrRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufUmkehrRufG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T3EndFloat
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG.T3
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

-- Identify the covered residue before inverting each machine-step head.
set_option hygiene false in
local macro "umkehr_head" : tactic => `(tactic| (
  try dsimp only [RufDannHeadG, RufEndHeadG] at hhead
  rw [hR] at hhead
  cases hhead))

set_option linter.unusedSimpArgs false in
/-- **Each step keeps the frame semantics, with calls.** The top frame of a
    covered residue either stays (same frame result), pops (logged value =
    frame result), or pushes an admitted callee above the frame it leaves
    waiting (`ErhaltK`). `hRSG`: the handler does not see the trace on the
    admitted callees (the trace may differ; the bare lock steps that
    changed only the trace were removed from G on 2026-09-13). -/
theorem schrittErhaltK_g6 {P : Programm D} {O : Orakel D} {passes : Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {A : D.Lock → Prop}
    {C : D.Fn → Prop} (hRSG : RufSG R C)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG6 P O passes M f M')
    (z : RufFadenG D) (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (ρ : Env D Γ) (r : GRest D (vertragVon D z.kopf.f) l Γ Λ)
    (hR : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩) (hcov : RestK A C r) :
    ErhaltK P O passes R A C M M' f z ρ r := by
  subst hz
  unfold ErhaltK
  cases hs with
  | endeBindAxiomElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeBindAxiomOptElseOk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeBindAxiomElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeBindAxiomOptElseGrund _ _ _ _ _ _ _ _ _ _ _ _ _ _ hhead => widerlegeK hhead
  | endeGleit l Γ Λ l₁ h₁ l₂ h₂ op a b lo hi rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    umkehr_head
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    simp only [Endblock.kOk, Stmt.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende _ hb.gleit_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeGleit O passes R op a b lo hi rest _ _ v hv)
  | endeGleitLit l Γ Λ q lo hi rest ρ hhead v hv =>
    umkehr_head
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    simp only [Endblock.kOk, Stmt.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende _ hb.gleitLit_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeGleitLit O passes R q lo hi rest _ _ v hv)
  | endeGleitVon l Γ Λ l₁ h₁ e lo hi rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    umkehr_head
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    simp only [Endblock.kOk, Stmt.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende _ hb.gleitVon_inv ho, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeGleitVon O passes R e lo hi rest _ _ v hv)
  | endeGleitNarrowOk l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    umkehr_head
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
    simp only [Endblock.kOk, Stmt.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende rest, _, rufUpdateG_self _ _ _, RestK.ende _ hr ho.2, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeGleitNarrowOk O passes R e lo hi sonst rest _ _ v hv)
  | endeGleitNarrowElse l Γ Λ l₁ h₁ e lo hi sonst rest ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    umkehr_head
    subst hs₁
    obtain ⟨hb, ho⟩ := hcov.ende_inv
    obtain ⟨hr, hs⟩ := hb.gleitNarrow_inv
    simp only [Endblock.kOk, Stmt.kOk, Bool.and_eq_true] at ho
    refine Or.inl ⟨_, _, _, _, .ende sonst, _, rufUpdateG_self _ _ _,
      RestK.ende _ hs ho.1, ?_⟩
    rw [weltVon_upd]
    exact REnde.gleich_of_eq (semK_endeGleitNarrowElse O passes R e lo hi sonst rest _ _ hn)

end Gabbro.Grammatik
