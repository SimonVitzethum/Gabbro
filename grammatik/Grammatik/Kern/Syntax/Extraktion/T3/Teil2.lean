module

public import Grammatik.Kern.Syntax.Extraktion.T2
public import Grammatik.Kern.Syntax.Extraktion.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Extraktion
variable {D : Deklaration}

mutual

/-- **Der Fussabdruck-Schlussstein (R1, Ausdruck):** `eval` liest nur
    `Expr.orte`. Stimmen zwei Welten -- Eintritt wie Gegenwart -- auf allen
    Orten von `os` ueberein, und deckt `os` die Orte von `e`, so liefert
    `eval` denselben Wert. Die Liste `os` bleibt durch die Induktion
    unveraendert stehen; nur die Deckung (`hsub`) wandert zu den
    Teilausdruecken. -/
theorem eval_liest_nur_orte {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (os : List (D.Tab ⊕ D.Glob))
    (hsub : ∀ o ∈ e.orte, o ∈ os)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hSG : ∀ g : D.Glob, .inr g ∈ os → σ.globs g = σ'.globs g)
    (h0T : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, .inr g ∈ os → σ₀.globs g = σ₀'.globs g) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ := by
  match e with
  | .lit _ => rfl
  | .tru => rfl
  | .fls => rfl
  | .var _ => rfl
  | .ptrOf _ _ _ _ => rfl
  | .fnref _ _ _ => rfl
  | .none _ => rfl
  | .why _ _ => rfl
  | .glob g _ =>
      simp only [eval]
      exact hSG g (hsub _ (by simp only [Expr.orte, List.mem_cons, List.not_mem_nil, or_false]))
  | .oldG g _ =>
      simp only [eval]
      exact h0G g (hsub _ (by simp only [Expr.orte, List.mem_cons, List.not_mem_nil, or_false]))
  | .slot t f i _ =>
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hi]
      exact hS t (hsub _ (by simp only [Expr.orte, List.mem_cons, true_or])) _ _
  | .oldS t f i _ =>
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hi]
      exact h0T t (hsub _ (by simp only [Expr.orte, List.mem_cons, true_or])) _ _
  | .thru _ t _ f i _ =>
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ho))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hi]
      exact hS t (hsub _ (by simp only [Expr.orte, List.mem_append, List.mem_cons, true_or, or_true])) _ _
  | .refEq a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho))) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho))) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .slotRef r t _ _ f _ =>
      have hr := eval_liest_nur_orte r os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval, hr]
      exact hS t (hsub _ (by simp only [Expr.orte, List.mem_cons, true_or])) _ _
  | .widen _ _ e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .neg a =>
      have h := eval_liest_nur_orte a os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .not a =>
      have h := eval_liest_nur_orte a os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .some e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .istSome e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [h]
  | .case _ _ nutz =>
      have hn := evalNutz_liest_nur_orte nutz os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [hn]
  | .add a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .sub a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .mul a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .div _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .rem _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .sdiv _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .srem _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .band _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .bor _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .bxor _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .shl _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .shr _ _ _ _ _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .lt a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .le a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .eq a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .fllt a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .flle a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .and a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .or a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .getBytes t f hf n i _ _ _ =>
      have hmemT : .inl t ∈ os := hsub _ (by simp only [Expr.orte, List.mem_cons, true_or])
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb : σ.bytesAb t f hf n (eval σ₀' i σ' ρ).n =
          σ'.bytesAb t f hf n (eval σ₀' i σ' ρ).n :=
        bytesAb_gleich (fun k f' => hS t hmemT k f') n _
      -- `simp only` rewrites under the dependent tuple proofs (where `rw`
      -- fails the motive check) but leaves the proof-irrelevant rest: `rfl`.
      simp only [eval, hi, hb]
      rfl
  | .forallSlots t body _ =>
      have hbody : ∀ k : Wert D (.index (D.count t)),
          k ∈ alleIndizes (D.count t) →
          wahr? (eval σ₀ body σ (.cons k ρ)) =
            wahr? (eval σ₀' body σ' (.cons k ρ)) := by
        intro k _
        exact congrArg wahr? (eval_liest_nur_orte body os
          (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
          σ₀ σ₀' σ σ' (.cons k ρ) hS hSG h0T h0G)
      simp only [eval]
      exact list_all_congr hbody
  | .existsSlots t body _ =>
      have hbody : ∀ k : Wert D (.index (D.count t)),
          k ∈ alleIndizes (D.count t) →
          wahr? (eval σ₀ body σ (.cons k ρ)) =
            wahr? (eval σ₀' body σ' (.cons k ρ)) := by
        intro k _
        exact congrArg wahr? (eval_liest_nur_orte body os
          (fun o ho => hsub o (List.mem_cons_of_mem _ ho))
          σ₀ σ₀' σ σ' (.cons k ρ) hS hSG h0T h0G)
      simp only [eval]
      exact list_any_congr hbody
  | .reaches t f hf a b _ =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl ho))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr ho))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hw : ∀ k, (fun k => hf ▸ σ.slots t k f) k =
          (fun k => hf ▸ σ'.slots t k f) k := by
        intro k
        show (hf ▸ σ.slots t k f) = (hf ▸ σ'.slots t k f)
        rw [hS t (hsub _ (by simp only [Expr.orte, List.cons_append, List.mem_cons, List.mem_append, true_or])) k f]
      simp only [eval]
      rw [ha, hb]
      exact kette_gleich _ _ _ hw
  | .arrNil => rfl
  | .strLit _ _ => rfl
  | .arrCons a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .arrGet a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .strCat a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .strGet a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .strEq a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .strLt a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .arrSet a i v =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ho)))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hi := eval_liest_nur_orte i os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ho)))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hv := eval_liest_nur_orte v os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hi, hv]
  | .strLen a =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha]
  | .strWeit _ a =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha]
  | .wenn c a b =>
      have hc := eval_liest_nur_orte c os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ho)))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ho)))))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [hc, ha, hb]
  | .eng e _ _ s =>
      have he := eval_liest_nur_orte e os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hs := eval_liest_nur_orte s os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [hs]
      exact eng_kongr he _
  | .intBuiltin1 _ a =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (ho))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha]
  | .intBuiltin2 _ a b =>
      have ha := eval_liest_nur_orte a os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inl ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      have hb := eval_liest_nur_orte b os
        (fun o ho => hsub o (List.mem_append.mpr (Or.inr ho)))
        σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [eval]
      rw [ha, hb]
  | .count n body =>
      have hbody : ∀ k : Zahl 0 ((n : Int) - 1), k ∈ alleIndizes (n : Int) →
          wahr? (eval σ₀ body σ (.cons k ρ)) = wahr? (eval σ₀' body σ' (.cons k ρ)) := by
        intro k _
        exact congrArg wahr? (eval_liest_nur_orte body os
          (fun o ho => hsub o (ho))
          σ₀ σ₀' σ σ' (.cons k ρ) hS hSG h0T h0G)
      simp only [eval]
      exact zaehleWahr_congr n _ _ hbody

/-- Die Nutzlast liest nur ihre Orte: die zweite Haelfte des Schlusssteins. -/
theorem evalNutz_liest_nur_orte {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (nutz : NutzlastExpr D Γ Λ c) (os : List (D.Tab ⊕ D.Glob))
    (hsub : ∀ o ∈ nutz.orte, o ∈ os)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hSG : ∀ g : D.Glob, .inr g ∈ os → σ.globs g = σ'.globs g)
    (h0T : ∀ t : D.Tab, .inl t ∈ os → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, .inr g ∈ os → σ₀.globs g = σ₀'.globs g) :
    evalNutz σ₀ nutz σ ρ = evalNutz σ₀' nutz σ' ρ := by
  match nutz with
  | .empty => rfl
  | .num e =>
      have h := eval_liest_nur_orte e os
        (fun o ho => hsub o ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G
      simp only [evalNutz]
      rw [h]

end
end Gabbro.Grammatik.Extraktion
