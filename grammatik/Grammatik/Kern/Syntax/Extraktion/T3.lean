/- Part 3 of 9 of `Extraktion` (split by instrumente/teile/lean-teilen.py; the umbrella `Extraktion.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Extraktion.T2

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
/-- **Der Fussabdruck-Schlussstein (R1):** `eval` liest nur `Expr.orte` --
    die Form ohne Deckungsliste: die Orte des Ausdrucks selbst genuegen. -/
theorem eval_liest_orte {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, .inl t ∈ e.orte → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hSG : ∀ g : D.Glob, .inr g ∈ e.orte → σ.globs g = σ'.globs g)
    (h0T : ∀ t : D.Tab, .inl t ∈ e.orte → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, .inr g ∈ e.orte → σ₀.globs g = σ₀'.globs g) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ :=
  eval_liest_nur_orte e _ (fun _ ho => ho) σ₀ σ₀' σ σ' ρ hS hSG h0T h0G

/-! ## 14. Vertraege als Welt-Praedikate: `HaengtAb` aus der gerechneten Huelle

    Ein Vertragsausdruck ist ein `Expr`; `vertragW`/`vertragG` lesen seine
    Huelle aus `Expr.orte`, und `QRequires`/`QEnsures`/`QInvariante` sind die
    Vertraege als Welt-Praedikate (je Umgebung -- kein Faden teilt sie, R1b;
    `old` faellt als Ein-Welt-Praedikat in die Gegenwart, R1a). `haengtAb_expr`
    loest `HaengtAb` aus der Huelle ein (`eval_aus_rahmen` ist die eine
    Zeile, die arbeitet); `haengtAb_weitet` traegt die Richtung in den
    Signaturrahmen, und `haengtAb_requires`/`haengtAb_ensures`/
    `haengtAb_invariante` benennen die Einloesung je Vertrag. Was in
    `InterferenzAllgemein.lean` als Praemisse getragen wird -- :211
    (`StabilSchritt`), :220 (`StabilKette`), :387 (`allgemeinStabil`, `hAb`),
    :431 (`allgemeinStabil_invariant`, `hAb`) -- loest sich hier ein, wo die
    Gestalt passt: `haengtAb_vertrag_gesamt` reicht die vereinte
    Vertrags-Huelle an :387 weiter, die `stabilKette_…_gilt`-Saetze schliessen
    :220 fuer vertragsgestaltiges `Q`. Fuer abstraktes `Q` bleiben die Stellen
    Praemissen -- das ist kein Rest, sondern die Aussage: was keinen
    gerechneten Fussabdruck hat, wird angenommen, nicht abgeleitet. -/

/-- The table half of a contract expression's footprint: named in `e.orte`
    (`List.any`, not `decide` over membership: only `DecidableEq` per side is
    needed, and `vertragW_mem` is the bridge back to `∈`). -/
def vertragW {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) :
    D.Tab → Bool :=
  fun t => e.orte.any fun o => match o with
    | .inl t' => decide (t' = t)
    | .inr _ => false

/-- The global half of a contract expression's footprint. -/
def vertragG {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) :
    D.Glob → Bool :=
  fun g => e.orte.any fun o => match o with
    | .inl _ => false
    | .inr g' => decide (g' = g)

/-- The table half names exactly the `.inl` members of `e.orte`. -/
theorem vertragW_mem {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) (t : D.Tab) :
    vertragW e t = true ↔ (.inl t : D.Tab ⊕ D.Glob) ∈ e.orte := by
  simp only [vertragW, List.any_eq_true]
  constructor
  · rintro ⟨o, ho, hpo⟩
    cases o with
    | inl t' =>
        simp only at hpo
        have heq : t' = t := of_decide_eq_true hpo
        subst heq
        exact ho
    | inr _ =>
        simp only [Bool.false_eq_true] at hpo
  · intro h
    exact ⟨.inl t, h, by simp only [decide_true]⟩

/-- The global half names exactly the `.inr` members of `e.orte`. -/
theorem vertragG_mem {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) (g : D.Glob) :
    vertragG e g = true ↔ (.inr g : D.Tab ⊕ D.Glob) ∈ e.orte := by
  simp only [vertragG, List.any_eq_true]
  constructor
  · rintro ⟨o, ho, hpo⟩
    cases o with
    | inl _ =>
        simp only [Bool.false_eq_true] at hpo
    | inr g' =>
        simp only at hpo
        have heq : g' = g := of_decide_eq_true hpo
        subst heq
        exact ho
  · intro h
    exact ⟨.inr g, h, by simp only [decide_true]⟩

/-- A contract expression as a world predicate: holds for every environment. -/
def QExpr {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) :
    World D → Prop :=
  fun σ => ∀ ρ : Env D Γ, wahr? (eval σ e σ ρ) = true

/-- `requires` as a world predicate (every parameter environment). -/
def QRequires (P : Programm D) (f : D.Fn) : World D → Prop :=
  QExpr (P.requires f)

/-- `ensures` as a world predicate (every return value, every parameter
    environment). -/
def QEnsures (P : Programm D) (f : D.Fn) : World D → Prop :=
  fun σ => ∀ (v : ErgVal D (D.erg f)) (ρ : Env D (D.params f)),
    wahr? (eval σ (P.ensures f) σ (ergEnv (D.erg f) v ρ)) = true

/-- An invariant as a world predicate (empty environment -- R1b). -/
def QInvariante (P : Programm D) (i : D.Inv) : World D → Prop :=
  fun σ => wahr? (eval σ (P.invariante i) σ .nil) = true

/-- A single environment: frame agreement makes `eval` agree. The workhorse
    behind every `HaengtAb` below. -/
theorem eval_aus_rahmen {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) {σ σ' : World D}
    (hRR : RahmenGleichAuf (vertragW e) (vertragG e) σ σ')
    (ρ : Env D Γ) :
    eval σ e σ ρ = eval σ' e σ' ρ :=
  eval_liest_orte e σ σ' σ σ' ρ
    (fun t ht k f => (hRR.1 t ((vertragW_mem e t).mpr ht) k f).symm)
    (fun g hg => (hRR.2 g ((vertragG_mem e g).mpr hg)).symm)
    (fun t ht k f => (hRR.1 t ((vertragW_mem e t).mpr ht) k f).symm)
    (fun g hg => (hRR.2 g ((vertragG_mem e g).mpr hg)).symm)

/-- **Contracts hang on their computed footprint:** what `e` reads decides
    what `QExpr e` sees. -/
theorem haengtAb_expr {Γ : Ctx} {Λ : List (Res D)}
    (e : Expr D Γ Λ .bool) :
    HaengtAb (vertragW e) (vertragG e) (QExpr e) := by
  intro σ σ' hRR
  constructor
  · intro h ρ
    have he := eval_aus_rahmen e hRR ρ
    rw [← he]
    exact h ρ
  · intro h ρ
    have he := eval_aus_rahmen e hRR ρ
    rw [he]
    exact h ρ

/-- `ensures` hangs on its computed footprint (return value and parameters). -/
theorem haengtAb_ensures_shape (P : Programm D) (f : D.Fn) :
    HaengtAb (vertragW (P.ensures f)) (vertragG (P.ensures f))
      (QEnsures P f) := by
  intro σ σ' hRR
  constructor
  · intro h v ρ
    have he := eval_aus_rahmen (P.ensures f) hRR (ergEnv (D.erg f) v ρ)
    rw [← he]
    exact h v ρ
  · intro h v ρ
    have he := eval_aus_rahmen (P.ensures f) hRR (ergEnv (D.erg f) v ρ)
    rw [he]
    exact h v ρ

/-- An invariant hangs on its computed footprint (empty environment). -/
theorem haengtAb_invariante_shape (P : Programm D) (i : D.Inv) :
    HaengtAb (vertragW (P.invariante i)) (vertragG (P.invariante i))
      (QInvariante P i) := by
  intro σ σ' hRR
  constructor
  · intro h
    show wahr? (eval σ' (P.invariante i) σ' .nil) = true
    have he := eval_aus_rahmen (P.invariante i) hRR .nil
    rw [← he]
    exact h
  · intro h
    show wahr? (eval σ (P.invariante i) σ .nil) = true
    have he := eval_aus_rahmen (P.invariante i) hRR .nil
    rw [he]
    exact h

/-- A frame may only grow: what hangs on the narrow frame hangs on the wide
    one. -/
theorem haengtAb_weitet {W W' : D.Tab → Bool} {G G' : D.Glob → Bool}
    {Q : World D → Prop}
    (hW : ∀ t, W t = true → W' t = true)
    (hG : ∀ g, G g = true → G' g = true)
    (h : HaengtAb W G Q) : HaengtAb W' G' Q := by
  intro σ σ' hRR
  apply h
  constructor
  · intro t ht k f
    exact hRR.1 t (hW t ht) k f
  · intro g hg
    exact hRR.2 g (hG g hg)


end Gabbro.Grammatik.Extraktion
