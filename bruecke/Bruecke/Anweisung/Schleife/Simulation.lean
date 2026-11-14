module
public import Bruecke.Anweisung.Schleife.Schreiben
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- Induction over the canonical index list. Each pass runs the existing write simulation;
    the iteration neither invents a successful outcome nor drops a loop-control outcome. -/
theorem finiteWrites_sim {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {ns : BodyNames} {x : String}
    {t : Fin u.tabs.length}
    (body : Block (declOf u) (verOf u c) true (.index ((declOf u).count t) :: Γ) Λ Λ)
    (bs : List Gabbro.Body.Stmt) (hU : UmfangB Γ fn ns)
    (hBody : ∀ σ ρ s, WGRel u σ s.world →
      PositionalLRel (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x).active 0 ρ s.local' →
      ∃ σ' ρ' s', execBlock O passes R body σ ρ = .ok σ' ρ' ∧
        (∃ A, Strecke_G u C A s s' bs) ∧ WGRel u σ' s'.world ∧
        PositionalLRel (fn.mitIndex x t.val ((declOf u).count t)) (ns.push x).active 0 ρ' s'.local') :
    ∀ (indices : List (Wert (declOf u) (.index ((declOf u).count t)))) σ ρ s,
      WGRel u σ s.world → PositionalLRel fn ns.active 0 ρ s.local' →
      ∃ σ' ρ' s' A,
        traverseLauf (l := loopMode) (fun σ ρ => execBlock O passes R body σ ρ)
          (fun σ _ => (σ, true)) indices σ ρ = .ok σ' ρ' ∧
        Strecke_G u C A s s' [.forEach (ns.fresh x) (indices.map (·.n)) bs] ∧
        WGRel u σ' s'.world ∧ PositionalLRel fn ns.active 0 ρ' s'.local'
  | [], σ, ρ, s, hW, hL =>
    ⟨σ, ρ, s, [], rfl, Strecke_G.schritt (fun _ _ => rfl) (fun _ => Int.le_refl _), hW, hL⟩
  | i :: indices, σ, ρ, s, hW, hL => by
    let entry : Gabbro.Body.State :=
      ⟨s.world, Gabbro.Body.bindLocal s.local' (ns.fresh x) (.int i.n)⟩
    have hLi := hL.pushIndex x hU.valid t.val ((declOf u).count t) i
    obtain ⟨σ₁, ρ₁, s₁, hbodyG, ⟨A₁, hStretch₁⟩, hW₁, hL₁⟩ :=
      hBody σ (.cons i ρ) entry hW hLi
    have hLouter : PositionalLRel fn ns.active 0 ρ₁.tail s₁.local' := hL₁.tailIndex
    obtain ⟨σ₂, ρ₂, s₂, A₂, hTailG, hStretch₂, hW₂, hL₂⟩ :=
      finiteWrites_sim body bs hU hBody indices σ₁ ρ₁.tail s₁ hW₁ hLouter
    have hTotal := hStretch₁.append hStretch₂
    refine ⟨σ₂, ρ₂, s₂, A₁ ++ A₂, ?_, { hTotal with lauf := ?_ }, hW₂, hL₂⟩
    · simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hbodyG]
      exact hTailG
    · intro ρB hT hF
      have hRun₁ := hStretch₁.lauf ρB (fun e he => hT e (List.mem_append_left _ he)) hF
      have hRun₂ := hStretch₂.lauf ρB (fun e he => hT e (List.mem_append_right _ he)) hF
      rw [Gabbro.Body.exec_singleton] at hRun₂ ⊢
      rw [List.map_cons, Gabbro.Body.forEach_cons_running ρB (ns.fresh x) i.n
        (indices.map (·.n)) bs s s₁ hRun₁]
      exact hRun₂

/-- The actual source traversal carries its canonical table count and index binding. -/
theorem stmtZiel_loop_G {loopMode : Bool} {P : Programm (declOf u)} (G : GesenktC u C P)
    (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn ft : UFn} {ns : BodyNames} {x : String} {t : Fin u.tabs.length} {n k : Nat}
    {ss tail : List UStmt} {bs : List Gabbro.Body.Stmt} {used : List String}
    {body : Block (declOf u) (verOf u c) true (.index ((declOf u).count t) :: Γ) Λ Λ}
    (hU : UmfangB Γ fn ns) (hV : Sicht u ft fn)
    (hx : NameFrisch (protectedNames fn.params fn.kinds) x)
    (hm : ∀ st ∈ ss, st ∈ (fnAt u c).body) (hg : loopWritesB ss = true)
    (hG : lowSeqL (l := true) u c (.index ((declOf u).count t) :: Γ)
      (fn.mitIndex x t.val ((declOf u).count t)) n Λ [] ss = .ok (⟨Λ, body⟩, .blkEnd :: tail))
    (hB : seqZ u k (ft.mitIndex x t.val ((declOf u).count t)) (ns.push x) ss =
      some (bs, .blkEnd :: tail, used))
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    StmtZiel_G u C c O passes R fn ns.active (.traverse (l := loopMode) t Expr.tru body) σ ρ s
      (.forEach (ns.fresh x) (loopIndices u t) bs) := by
  have hBody := loopWrites_sim G S c hc O passes R hRR n k ss
    (fn.mitIndex x t.val ((declOf u).count t)) (ft.mitIndex x t.val ((declOf u).count t))
    (ns.push x) body tail bs used (hU.index hx t.val ((declOf u).count t))
    (hV.index x t.val ((declOf u).count t)) hm hg hG hB
  obtain ⟨σ', ρ', s', A, hex, hStretch, hW', hL'⟩ :=
    finiteWrites_sim (loopMode := loopMode) body bs hU hBody (alleIndizes ((declOf u).count t)) σ ρ s hW hL
  have hExec : execStmt O passes R (.traverse (l := loopMode) t Expr.tru body) σ ρ = .ok σ' ρ' := by
    simpa only [execStmt, Expr.orte, lese_nil, eval, wahr?] using hex
  exact stmtZiel_ok_G hExec hStretch hW' hL'

end Gabbro.Bruecke
