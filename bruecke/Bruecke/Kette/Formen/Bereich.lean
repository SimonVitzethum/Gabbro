module
public import Bruecke.Anweisung.Bereich.Ende
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem narrowTest_eval {s : Gabbro.Body.State} {e : Gabbro.Body.Expr} {n lo hi : Int}
    (h : Gabbro.Body.eval s e = some (.int n)) :
    Gabbro.Body.eval s (narrowTest e lo hi) = some (.bool (decide (lo ≤ n ∧ n ≤ hi))) := by
  simp only [narrowTest, Gabbro.Body.eval, h, Gabbro.Body.binop,
    Gabbro.Body.andBool_some, Bool.decide_and]

theorem narrowName_eval {Γ : Ctx} {fn : UFn} {ns : BodyNames} {x id : String}
    {j : Nat} {a b : Int} {v : Var Γ (.int a b)} (hj : paramPos fn.params x = .ok j)
    (hv : lowVar Γ j (.int a b) = .ok v) (hid : ns.lookup fn x = some id)
    (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    Gabbro.Body.eval s (.name id) = some (.int (ρ.get v).n) := by
  have hi : ns.active[j]? = some id := by simpa only [BodyNames.lookup, hj] using hid
  simp only [Gabbro.Body.eval]
  rw [hL.values j id hi, Nat.zero_add, nthVal_lowVar Γ j (.int a b) v ρ hv] <;> rfl

/-- Both outcomes of a numeric narrow are represented: the success binder or the mandatory
    ending branch. Bounds are tested exactly, including an empty target interval. -/
theorem laufZiel_narrow_G {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames} {x id : String}
    {a b lo hi : Int} {j : Nat} {v : Var Γ (.int a b)}
    {err : Endblock (declOf u) (verOf u c) false Γ Λ}
    {rest : Endblock (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ}
    {errorBody ys : List Gabbro.Body.Stmt} (hj : paramPos fn.params x = .ok j)
    (hv : lowVar Γ j (.int a b) = .ok v) (hid : ns.lookup fn x = some id)
    (hU : UmfangB Γ fn ns)
    (hErr : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      EndZiel_G u C c O passes R err σ ρ s errorBody)
    (hRest : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitBindung x (lo, hi)) (ns.push x).active 0 ρ s.local' →
      LaufZielTeilB u C c O passes R rest σ ρ s ys)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    LaufZielTeilB u C c O passes R (.narrow (.var v) lo hi err rest) σ ρ s
      (narrowStep ns x lo hi (.name id) errorBody :: ys) := by
  let σl := σ.lese Λ (Expr.var (Λ := Λ) v).orte
  have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
  have hval := narrowName_eval hj hv hid ρ s hL
  have ht := narrowTest_eval (lo := lo) (hi := hi) hval
  by_cases hb : lo ≤ (ρ.get v).n ∧ (ρ.get v).n ≤ hi
  · let value : Wert (declOf u) (.int lo hi) := ⟨(ρ.get v).n, hb.1, hb.2⟩
    let s₁ : Gabbro.Body.State :=
      ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) (.int (ρ.get v).n)⟩
    have hs : ∀ ρB, RahmenAlleC u C ρB →
        Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s = .running s₁ := by
      intro ρB _
      unfold narrowStep
      rw [Gabbro.Body.step, ht, decide_eq_true hb]
      simp only [Gabbro.Body.exec, Gabbro.Body.step, hval]
      rfl
    have hL₁ := hL.push x (ns.fresh x) (lo, hi) (BodyNames.fresh_not_active hU.valid x) value
    apply laufZiel_schritt_teilB (b1 := rest) (σ₁ := σl) (ρ₁ := .cons value ρ)
      (s₁ := s₁) (x := narrowStep ns x lo hi (.name id) errorBody)
    · constructor
      · intro e h
        simp only [execEnd, eval] at h
        first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
        exact EndAusgang.schrumpf_logik h
      · intro σ' v' h
        simp only [execEnd, eval] at h
        first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
        exact endSchrumpf_zurueck h
    · exact hs
    · exact fun w => Int.le_refl _
    · exact hRest σl (.cons value ρ) s₁ hWl hL₁
  · have hstep : ∀ ρB, Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s =
        Gabbro.Body.exec ρB errorBody s := by
      intro ρB
      unfold narrowStep
      rw [Gabbro.Body.step, ht, decide_eq_false hb]
    have herr := hErr σl ρ s hWl hL
    refine ⟨fun e h => herr.1 e ?_, fun σ' v' h => ?_⟩
    · simp only [execEnd, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      exact h
    · have he : execEnd O passes R err σl ρ = .zurueck σ' v' := by
        simp only [execEnd, eval] at h
        first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
        exact h
      obtain ⟨A, hg, ho, hk, hr⟩ := herr.2 σ' v' he
      refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
      obtain ⟨s', hrun, hw⟩ := hr ρB hT hF
      refine ⟨s', ?_, ?_, hw⟩
      · simp only [Gabbro.Body.exec, hstep ρB, hrun, Gabbro.Body.finalState]
      · simp only [Gabbro.Body.exec, hstep ρB, hrun, finalValue_returned]

theorem blockZiel_narrow_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {ns : BodyNames} {x id : String}
    {a b lo hi : Int} {j : Nat} {v : Var Γ (.int a b)}
    {err : Endblock (declOf u) (verOf u c) loopMode Γ Λ}
    {rest : Block (declOf u) (verOf u c) loopMode (.int lo hi :: Γ) Λ Λ'}
    {errorBody ys : List Gabbro.Body.Stmt} (hj : paramPos fn.params x = .ok j)
    (hv : lowVar Γ j (.int a b) = .ok v) (hid : ns.lookup fn x = some id)
    (hU : UmfangB Γ fn ns)
    (hErr : ∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      EndZiel_G u C c O passes R err σ ρ s errorBody)
    (hRest : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitBindung x (lo, hi)) (ns.push x).active 0 ρ s.local' →
      BlockZiel_G u C c O passes R (fn.mitBindung x (lo, hi)) (ns.push x).active rest σ ρ s ys)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    BlockZiel_G u C c O passes R fn ns.active (.narrow (.var v) lo hi err rest) σ ρ s
      (narrowStep ns x lo hi (.name id) errorBody :: ys) := by
  let σl := σ.lese Λ (Expr.var (Λ := Λ) v).orte
  have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
  have hval := narrowName_eval hj hv hid ρ s hL
  have ht := narrowTest_eval (lo := lo) (hi := hi) hval
  by_cases hb : lo ≤ (ρ.get v).n ∧ (ρ.get v).n ≤ hi
  · let value : Wert (declOf u) (.int lo hi) := ⟨(ρ.get v).n, hb.1, hb.2⟩
    let s₁ : Gabbro.Body.State :=
      ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) (.int (ρ.get v).n)⟩
    have hs : ∀ ρB, RahmenAlleC u C ρB →
        Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s = .running s₁ := by
      intro ρB _
      unfold narrowStep
      rw [Gabbro.Body.step, ht, decide_eq_true hb]
      simp only [Gabbro.Body.exec, Gabbro.Body.step, hval]
      rfl
    have hL₁ := hL.push x (ns.fresh x) (lo, hi) (BodyNames.fresh_not_active hU.valid x) value
    have ih := hRest σl (.cons value ρ) s₁ hWl hL₁
    refine ⟨fun e h => ?_, fun σ' v' h => ?_, fun σ' ρ' h => ?_⟩
    · simp only [execBlock, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      exact ih.1 e (schrumpfZ_logik h)
    · simp only [execBlock, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      obtain ⟨A, hr⟩ := ih.2.1 σ' v' (schrumpfZ_zurueck h)
      exact ⟨A, RueckZ_G.vor hs (fun w => Int.le_refl _) hr⟩
    · simp only [execBlock, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      obtain ⟨ρ'', hin, htail⟩ := schrumpfZ_ok h
      subst ρ'
      obtain ⟨A, s₂, hS, hW₂, hL₂⟩ := ih.2.2 σ' ρ'' hin
      exact ⟨A, s₂, Strecke_G.vor hs (fun w => Int.le_refl _) hS, hW₂, hL₂.tail⟩
  · have hstep : ∀ ρB, Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s =
        Gabbro.Body.exec ρB errorBody s := by
      intro ρB
      unfold narrowStep
      rw [Gabbro.Body.step, ht, decide_eq_false hb]
    have herr := hErr σl ρ s hWl hL
    refine ⟨fun e h => ?_, fun σ' v' h => ?_, fun σ' ρ' h => ?_⟩
    · simp only [execBlock, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      exact herr.1 e (EndAusgang.zuAusgang_logik h)
    · simp only [execBlock, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      have he : execEnd O passes R err σl ρ = .zurueck σ' v' := by
        change (execEnd O passes R err σl ρ).zuAusgang = .zurueck σ' v' at h
        cases hh : execEnd O passes R err σl ρ <;>
          simp only [hh, EndAusgang.zuAusgang, reduceCtorEq, Ausgang.zurueck.injEq] at h
        obtain ⟨hσ, hv⟩ := h
        subst σ'
        subst v'
        first | exact hh | rfl
      obtain ⟨A, hg, ho, hk, hr⟩ := herr.2 σ' v' he
      refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
      obtain ⟨s', hrun, hw⟩ := hr ρB hT hF
      exact ⟨s', by simp only [Gabbro.Body.exec, hstep ρB, hrun], hw⟩
    · simp only [execBlock, eval] at h
      first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
      change (execEnd O passes R err σl ρ).zuAusgang = .ok σ' ρ' at h
      cases hh : execEnd O passes R err σl ρ <;>
        simp only [hh, EndAusgang.zuAusgang, reduceCtorEq] at h

end Gabbro.Bruecke
