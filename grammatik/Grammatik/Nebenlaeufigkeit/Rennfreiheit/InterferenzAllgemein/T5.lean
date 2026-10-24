/- Part 5 of 5 of `InterferenzAllgemein` (split by instrumente/teile/lean-teilen.py; the umbrella `InterferenzAllgemein.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}
variable {D : Deklaration}

mutual

/-- **The memory-footprint stone, upstream:** `eval` reads only slots and
    globals. Worlds that agree on every slot and every global -- at entry and
    at present separately -- give `eval` the same value. The entry pair covers
    `old(...)`; the trace never matters. -/
theorem eval_liest_nur_speicher {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, σ.globs g = σ'.globs g)
    (h0S : ∀ t : D.Tab, ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, σ₀.globs g = σ₀'.globs g) :
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
  | .refEq a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .slotRef r t _ _ f _ =>
      have hr := eval_liest_nur_speicher r σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval, hr]
      exact hS t _ _
  | .glob g _ =>
      simp only [eval]
      exact hG g
  | .oldG g _ =>
      simp only [eval]
      exact h0G g
  | .slot t f i _ =>
      have hi := eval_liest_nur_speicher i σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval, hi]
      exact hS t _ _
  | .oldS t f i _ =>
      have hi := eval_liest_nur_speicher i σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval, hi]
      exact h0S t _ _
  | .thru _ t _ f i _ =>
      have hi := eval_liest_nur_speicher i σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval, hi]
      exact hS t _ _
  | .widen _ _ e =>
      have h := eval_liest_nur_speicher e σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [h]
  | .neg a =>
      have h := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [h]
  | .not a =>
      have h := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [h]
  | .some e =>
      have h := eval_liest_nur_speicher e σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [h]
  | .istSome e =>
      have h := eval_liest_nur_speicher e σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [h]
  | .case _ _ nutz =>
      have hn := evalNutz_liest_nur_speicher nutz σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [hn]
  | .add a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .sub a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .mul a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .div _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .rem _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .sdiv _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .srem _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .band _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .bor _ _ _ _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .bxor _ _ _ _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .shl _ _ _ _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .shr _ _ _ _ _ a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .lt a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .le a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .eq a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .fllt a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .flle a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .and a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .or a b =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [eval]
      rw [ha, hb]
  | .getBytes t f hf n i _ _ _ =>
      have hi := eval_liest_nur_speicher i σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb : σ.bytesAb t f hf n (eval σ₀' i σ' ρ).n =
          σ'.bytesAb t f hf n (eval σ₀' i σ' ρ).n :=
        speicher_bytesAb_gleich (fun k f' => hS t k f') n _
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
        exact congrArg wahr? (eval_liest_nur_speicher body σ₀ σ₀' σ σ' (.cons k ρ)
          hS hG h0S h0G)
      simp only [eval]
      exact speicher_list_all_congr hbody
  | .existsSlots t body _ =>
      have hbody : ∀ k : Wert D (.index (D.count t)),
          k ∈ alleIndizes (D.count t) →
          wahr? (eval σ₀ body σ (.cons k ρ)) =
            wahr? (eval σ₀' body σ' (.cons k ρ)) := by
        intro k _
        exact congrArg wahr? (eval_liest_nur_speicher body σ₀ σ₀' σ σ' (.cons k ρ)
          hS hG h0S h0G)
      simp only [eval]
      exact speicher_list_any_congr hbody
  | .reaches t f hf a b _ =>
      have ha := eval_liest_nur_speicher a σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hb := eval_liest_nur_speicher b σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      have hw : ∀ k, (fun k => hf ▸ σ.slots t k f) k =
          (fun k => hf ▸ σ'.slots t k f) k := by
        intro k
        show (hf ▸ σ.slots t k f) = (hf ▸ σ'.slots t k f)
        rw [hS t k f]
      simp only [eval]
      rw [ha, hb]
      exact speicher_kette_gleich _ _ _ hw

/-- The payload reads only its places: the second half of the stone. -/
theorem evalNutz_liest_nur_speicher {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (nutz : NutzlastExpr D Γ Λ c)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, σ.globs g = σ'.globs g)
    (h0S : ∀ t : D.Tab, ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, σ₀.globs g = σ₀'.globs g) :
    evalNutz σ₀ nutz σ ρ = evalNutz σ₀' nutz σ' ρ := by
  match nutz with
  | .empty => rfl
  | .num e =>
      have h := eval_liest_nur_speicher e σ₀ σ₀' σ σ' ρ hS hG h0S h0G
      simp only [evalNutz]
      rw [h]

end
/-- **The diagonal a `SpeicherVertrag` instance consumes:** where both the entry
    and the present world are read at once, one memory agreement suffices. Both
    premises fire twice (entry and present side). -/
theorem eval_liest_nur_speicher_diag {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ)
    (σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, σ.globs g = σ'.globs g) :
    eval σ e σ ρ = eval σ' e σ' ρ :=
  eval_liest_nur_speicher e σ σ' σ σ' ρ hS hG hS hG

#print axioms Gabbro.Grammatik.eval_liest_nur_speicher
#print axioms Gabbro.Grammatik.evalNutz_liest_nur_speicher
#print axioms Gabbro.Grammatik.eval_liest_nur_speicher_diag


end Gabbro.Grammatik
