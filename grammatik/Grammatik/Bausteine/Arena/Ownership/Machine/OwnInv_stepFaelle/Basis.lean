module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return

@[expose] public section


/-! **Every step of machine G keeps ownership.** One case per step rule:
the running activation's state moves by the step lemmas of this folder,
a call pushes (`ownInv_push`), a return pops (`ownInv_pop`); the one
assumption is the rely `pendWord` for the other threads. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

section Helpers

variable {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State} {σ : World D} {f : D.Fn}

/-- A running activation outside every allocator form realises its context. -/
theorem head_run {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {r : GRest D (vertragVon D f) l Γ Λ}
    (h : Head A I fr s σ f ⟨l, Γ, Λ, ρ, r⟩) (hp : pendWord A r = none) :
    ∃ k c g, k.references.length ≤ Γ.length ∧ FrameOk c g s fr ρ ∧ OR A I (I f).output k c r := by
  cases h with
  | run _ _ hk hf hr => exact ⟨_, _, _, hk, hf, hr⟩
  | list => simp only [pendWord, true_or, ↓reduceIte, reduceCtorEq] at hp
  | counter => simp only [pendWord, or_true, ↓reduceIte, reduceCtorEq] at hp
  | store => simp only [pendWord, ↓reduceIte, reduceCtorEq] at hp
  | release => simp only [pendWord, true_or, ↓reduceIte, reduceCtorEq] at hp

theorem meta_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) {σ₁ : World D}
    (h : σ₁ = σ.lese Λ os) {A : FreiForm D} : MetaSame A σ σ₁ := by
  rw [h]; exact MetaSame.reads A σ Λ os

/-- **A leaf step of the running activation**, whatever its state. -/
theorem head_leaf {O : Orakel D} {passes : Nat} (hO : GutO O) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {ρ : Env D Γ} {st : Stmt D (vertragVon D f) l Γ Λ Λ'} {rest : Block D (vertragVon D f) l Γ Λ' Λ''}
    {k : GRest D (vertragVon D f) l Γ Λ''} (h : Head A I fr s σ f ⟨l, Γ, Λ, ρ, .dann (.cons st rest) k⟩)
    (ha : s.agrees A σ) (ho : A.FreiOk σ) (hleaf : st.istBlatt = true) {σ' : World D} {ρ' : Env D Γ}
    (hstep : execStmt O passes keinRuf st σ ρ = .ok σ' ρ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ', ρ', .dann rest k⟩ :=
  match h, hstep with
  | .run _ _ hk hf hr, hstep => run_leaf hO hk hf ha ho hr hleaf hstep
  | .list x ρ0 e2 hw hL _ _ he2 hx hlt hk hf hr, hstep => list_step x ρ0 e2 hw hL he2 hx hlt hk hf hr ha ho hstep
  | .counter x ρ0 e2 hw hL _ _ he2 hx _ hk hf hr, hstep => counter_step x ρ0 e2 hw hL he2 hx hk hf hr ha ho hstep
  | .store x ρ0 t f' i ev hws hLs hn e2 hw hL b r he2 hx hlt hk hf hr, hstep =>
    store_step x ρ0 t f' i ev hws hLs hn e2 hw hL b r he2 hx hlt hk hf hr ha ho hstep
  | .release ρ0 e2 hw hL b r p o hh he2 hp ho' hg hlink hk hf hr, hstep =>
    release_step ρ0 e2 hw hL b r p o hh he2 hp ho' hg hlink hk hf hr ha ho hstep

theorem dropContextB_refs (c : Context) (owner : Bool) : (dropContextB c owner).references = c.references := by
  cases owner <;> simp only [dropContextB, Bool.false_eq_true, ↓reduceIte, Context.drop, Context.bindFresh, ne_eq, List.cons_ne_self, not_false_eq_true, List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]

/-- The caller of the running activation, suspended on it. -/
theorem caller_susp {t : Faden} {g : D.Fn} {caller : RufRahmenG D} {rst : List (RufRahmenG D)}
    {stack : List (RufRahmenG D)} (h : StackOk A I s t g stack) (hpop : stack = caller :: rst) :
    Susp A I ⟨t, rst.length⟩ s g caller.f caller.rest := by
  subst hpop; exact h.1

/-- The callee of an indirect call at its entry. -/
theorem callee_ind {c : Context} {gh : Ghost} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {n : Nat}
    {J : Modes (D.sigNr n).params} {args : Args D Γ Λ (D.sigNr n).params} {g : D.Fn} (hg : D.passt g n = true)
    (hJ : modeList (I g).parameters = modeList J) {depth : Nat → Nat} {t a : Nat}
    (hd : s.Disciplined depth) (hdepth : depth t = a) (hR : Realizes c gh A ⟨t, a⟩ s σ ρ)
    (hp : planFits c (modeList J) (originList c args) = true) (σa σb : World D) :
    FrameOk (Flow.parameterContext (I g).parameters) (calleeGhost gh (modeList J) (originList c args) s.next)
      (s.handoff ⟨t, a + 1⟩ (movedHandles gh (modeList J) (originList c args))
        (lentHandles gh (modeList J) (originList c args))) ⟨t, a + 1⟩ (umsig hg (evalArgs σa args σb ρ)) := by
  have h := Push.callee_frame J args rfl rfl hd hdepth hR hp σa σb
  have hpc := parameterContext_eq (I g).parameters J hJ
  rw [hpc]
  exact ⟨h.1, References.transport (D.passt_sig hg).params.symm (umsig_heq hg _).symm h.2.1, h.2.2.1, h.2.2.2⟩

/-- **After a plain call**, whatever the shape of the caller's state. -/
theorem resume_plainX {depth : Nat → Nat} {t a : Nat} (hd : s.Disciplined depth) (hdepth : depth t = a + 1)
    {g f : D.Fn} {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ}
    (hs : Susp A I ⟨t, a⟩ s g f x) (hw : x.2.2.2.2.wartend = false) (v : ErgVal D (D.erg g))
    (hres : (I g).output.result A ⟨t, a + 1⟩ s v) :
    Head A I ⟨t, a⟩ (s.pop ⟨t, a + 1⟩ ⟨t, a⟩) σ f x := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  exact resume_plain hd hdepth hs hw v hres

/-- The checked return value of the running activation. -/
theorem ret_result {Γ : Ctx} {Λ : List (Res D)} {c : Context} {gh : Ghost} {ρ : Env D Γ}
    {e : ErgExpr D Γ Λ (vertragVon D f).erg} (hf : FrameOk c gh s fr ρ)
    (hcheck : (I f).output.check A c e = true) (σ0 σ1 : World D) :
    (I f).output.result A fr s (evalErg σ0 e σ1 ρ) :=
  Flow.Output.check_sound A c gh fr s (I f).output e σ0 σ1 ρ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hcheck

end Helpers

/-! ## The step -/

end Gabbro.Grammatik.ArenaOwnership.Machine
