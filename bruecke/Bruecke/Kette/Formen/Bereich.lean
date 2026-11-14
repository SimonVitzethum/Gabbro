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
      EndZiel_G u C c O passes R fn ns.active err σ ρ s errorBody)
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
    · refine ⟨?_, ?_, ?_⟩
      · intro e h
        simp only [execEnd, eval] at h
        first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
        exact EndAusgang.schrumpf_logik h
      · intro σ' v' h
        simp only [execEnd, eval] at h
        first | simp only [hb, and_self, dite_true, ↓reduceDIte] at h | simp only [hb, dite_false, ↓reduceDIte] at h
        exact endSchrumpf_zurueck h
      · intro σ' r' h
        simp only [execEnd, eval, hb, ↓reduceDIte] at h
        exact endSchrumpf_why h
    · exact hs
    · exact fun w => Int.le_refl _
    · exact hRest σl (.cons value ρ) s₁ hWl hL₁
  · have hstep : ∀ ρB, Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s =
        Gabbro.Body.exec ρB errorBody s := by
      intro ρB
      unfold narrowStep
      rw [Gabbro.Body.step, ht, decide_eq_false hb]
    have herr := hErr σl ρ s hWl hL
    refine ⟨fun e h => herr.1 e ?_, fun σ' v' h => ?_, fun σ' r' h => ?_⟩
    · simpa only [execEnd, eval, hb, ↓reduceDIte, EndAusgang.zuAusgang] using congrArg EndAusgang.zuAusgang h
    · have he : (execEnd O passes R err σl ρ).zuAusgang = .zurueck σ' v' := by
        simpa only [execEnd, eval, hb, ↓reduceDIte, EndAusgang.zuAusgang] using congrArg EndAusgang.zuAusgang h
      obtain ⟨A, hg, ho, hk, hr⟩ := herr.2.1 σ' v' he
      refine ⟨A, hg, ho, hk, fun ρB hT hF => ?_⟩
      obtain ⟨s', hrun, hw⟩ := hr ρB hT hF
      refine ⟨s', ?_, ?_, hw⟩
      · simp only [Gabbro.Body.exec, hstep ρB, hrun, Gabbro.Body.finalState]
      · simp only [Gabbro.Body.exec, hstep ρB, hrun, finalValue_returned]
    · have he : (execEnd O passes R err σl ρ).zuAusgang = .why σ' r' := by
        simpa only [execEnd, eval, hb, ↓reduceDIte, EndAusgang.zuAusgang] using congrArg EndAusgang.zuAusgang h
      obtain ⟨A, hg, ho, hk, hr⟩ := herr.2.2.2.2 σ' r' he
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
      EndZiel_G u C c O passes R fn ns.active err σ ρ s errorBody)
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
    simpa only [BlockZiel_G, execBlock, eval, hb, ↓reduceDIte, List.singleton_append] using
      ausgangZiel_schrumpf (Strecke_G.schritt hs (fun w => Int.le_refl _))
        (fun _ _ hl => hl.tail) ih
  · have hstep : ∀ ρB, Gabbro.Body.step ρB (narrowStep ns x lo hi (.name id) errorBody) s =
        Gabbro.Body.exec ρB errorBody s := by
      intro ρB
      unfold narrowStep
      rw [Gabbro.Body.step, ht, decide_eq_false hb]
    have herr := hErr σl ρ s hWl hL
    have hfull := ausgangZiel_suffix herr (fun σ' ρ' he => by
      cases hh : execEnd O passes R err σl ρ <;>
        simp only [hh, EndAusgang.zuAusgang] at he <;> cases he) ys
    unfold BlockZiel_G
    simp only [execBlock, eval, hb, ↓reduceDIte]
    exact ausgangZiel_map hfull (fun ρB => by simp only [exec_append, Gabbro.Body.exec, hstep ρB])

end Gabbro.Bruecke
