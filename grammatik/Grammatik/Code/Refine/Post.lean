import Grammatik.Code.Refine.Mono
import Grammatik.Code.Refine.Block

/-
  File:      Grammatik/Code/Refine/Post.lean
  Subject:   TRACK L, PHASE L1 -- WHAT A RUN LEAVES BEHIND, and the `return` fragment.

    * `Post` -- the relation after a normal exit: the world is in memory, the environment is in
      its cells, the memory still has its global blocks, the free registers lie above every
      variable's register;
    * `RetAt` -- the frame stands at a `ret` whose operand is the image of the returned value;
    * `lowerErg_ok` -- the `return` of an optional value;
    * `post_store` -- a store into a block that is no local keeps `Post`.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag ErgVal ErgExpr eval evalErg)

variable {D : Deklaration}

/-- The image of a returned value (`none` for a function without an answer). -/
def ergImg (lay : Layout D) : (eo : Option GTy) → ErgVal D eo → Option Val
  | none, _ => none
  | some τ, v => some (encR lay τ v)

/-- The frame stands at a `ret` terminator whose operand evaluates to `vo`. -/
def RetAt (M : Modl) (f : Frame) (vo : Option Val) : Prop :=
  ∃ blk, M.blk f.fn f.lbl = some blk ∧ blk.body.length ≤ f.pc ∧
    ((blk.term = .ret none ∧ vo = none) ∨ ∃ o v, blk.term = .ret (some o) ∧ vo = some v ∧ o.ev f.regs = some v)

/-- What holds after a normal exit. -/
def Post (lay : Layout D) (cenv : List Reg) {Γ : Ctx} (σ : World D) (ρ : Env D Γ) (m : Mem)
    (rs : Regs) (r : Nat) : Prop :=
  Rep lay σ m ∧ EnvRep lay rs m cenv ρ ∧ WfL lay m ∧ ∀ x ∈ cenv, x < r

theorem post_mono {lay : Layout D} {cenv : List Reg} {Γ : Ctx} {σ : World D} {ρ : Env D Γ} {m : Mem}
    {rs : Regs} {r r' : Nat} (h : Post lay cenv σ ρ m rs r) (hle : r ≤ r') : Post lay cenv σ ρ m rs r' :=
  ⟨h.1, h.2.1, h.2.2.1, fun x hx => Nat.lt_of_lt_of_le (h.2.2.2 x hx) hle⟩

theorem not_fresh_glob {lay : Layout D} (g : D.Glob) : ¬ Fresh lay (lay.ggblk g) :=
  fun h => h.2 g rfl

theorem not_fresh_tab {lay : Layout D} (t : D.Tab) : ¬ Fresh lay (lay.gblk t) :=
  fun h => h.1 t rfl

/-- A store into a table or a global (a block that is no local) keeps `Post`. -/
theorem post_store {lay : Layout D} {cenv : List Reg} {Γ : Ctx} {σ' : World D} {ρ : Env D Γ}
    {m m' : Mem} {rs rs2 : Regs} {r2 : Nat} (hRn : Rep lay σ' m') (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m) {b : Nat} {o : Int} {t : Ty} {v : Val} (hst : m.store b o t v = some m')
    (hb : ¬ Fresh lay b) (hag : ∀ r ∈ cenv, rs2 r = rs r) (hc : ∀ x ∈ cenv, x < r2) :
    Post lay cenv σ' ρ m' rs2 r2 :=
  ⟨hRn, envRep_load cenv ρ (fun r hr b' hb' hf o t v hl => fresh_load_store hst hb b' o t v hf hl)
    (envRep_regs cenv ρ hag hE), wfL_store hst hW, hc⟩

/-- The `return` of an optional value. -/
theorem lowerErg_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErg lay cenv e lb st = some (blks, st')) (M : Modl) (S : Sees) (fn : Nat)
    (hM : ∀ b ∈ blks, M.blk fn b.lbl = some b) (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs)
    (ks : List Frame) (dst : Option Reg) (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ)
    (hc : ∀ x ∈ cenv, x < st.r) :
    ∃ f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m f' ks) ∧ f'.fn = fn ∧ f'.dst = dst ∧
      RetAt M f' (ergImg lay eo (evalErg σ₀ e σ ρ)) ∧ Fr lay cenv st.r m rs m f'.regs := by
  cases e with
  | empty =>
      simp only [lowerErg] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hb := hM _ (List.mem_singleton_self _)
      exact ⟨⟨fn, lb, 0, rs, dst⟩, Reach.refl _, rfl, rfl, ⟨_, hb, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩⟩,
        fr_regs (fun _ _ => rfl)⟩
  | val e =>
      simp only [lowerErg] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      simp only [he] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
      obtain ⟨rs1, hs1, _, hag1, _, hev⟩ := Fe
      have hr := reach_block_end (S := S) (ks := ks) (dst := dst) hb hs1
      exact ⟨⟨fn, lb, ce.length, rs1, dst⟩, hr, rfl, rfl, ⟨_, hb, Nat.le_refl _,
        Or.inr ⟨oe, _, rfl, rfl, hev⟩⟩, fr_regs hag1⟩

end Gabbro.Code.Lower
