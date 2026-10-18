import Grammatik.Code.Refine.Struct.Mono
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

/-- The image of the answer of a function with `n` reasons (`n = 0`: the plain image of the value; else the
    answer word, `Lower/Fail.lean`). -/
def retImg (lay : Layout D) (n : Nat) (eo : Option GTy) (v : ErgVal D eo) : Option Val :=
  if n = 0 then ergImg lay eo v else some (Val.ofInt (retW n eo) (okZ n eo v))

/-- The image of the answer `why r` of a function with `n` reasons. -/
def whyImg (n : Nat) (eo : Option GTy) (r : Nat) : Option Val :=
  some (Val.ofInt (retW n eo) ((r : Int) + 1))

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
  fun h => h.2.1 g rfl

theorem not_fresh_lblk {lay : Layout D} (L : D.Lock) : ¬ Fresh lay (lay.lblk L) :=
  fun h => (h.2.2 L).1 rfl

theorem not_fresh_lsrv {lay : Layout D} (L : D.Lock) : ¬ Fresh lay (lay.lsrv L) :=
  fun h => (h.2.2 L).2 rfl

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

/-- The `return` of a function with `n` reasons or none: `lowerErg_ok`, and the answer word. -/
theorem lowerRet_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (n : Nat) {Γ : Ctx}
    {Λ : List (Res D)} {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St)
    (blks : List Block) (h : lowerRet lay cenv n e lb st = some (blks, st')) (M : Modl) (S : Sees)
    (fn : Nat) (hM : ∀ b ∈ blks, M.blk fn b.lbl = some b) (σ₀ σ : World D) (ρ : Env D Γ) (m : Mem)
    (rs : Regs) (ks : List Frame) (dst : Option Reg) (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ)
    (hc : ∀ x ∈ cenv, x < st.r) :
    ∃ f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m f' ks) ∧ f'.fn = fn ∧ f'.dst = dst ∧
      RetAt M f' (retImg lay n eo (evalErg σ₀ e σ ρ)) ∧ Fr lay cenv st.r m rs m f'.regs := by
  unfold lowerRet at h
  by_cases hn : n = 0
  · rw [if_pos hn] at h
    have := lowerErg_ok lay hL cenv e lb st st' blks h M S fn hM σ₀ σ ρ m rs ks dst hR hE hc
    unfold retImg
    rw [if_pos hn]
    exact this
  · rw [if_neg hn] at h
    unfold retImg
    rw [if_neg hn]
    cases e with
    | empty =>
        simp only [lowerErgF] at h
        split at h
        · have h' := Option.some.inj h
          simp only [Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl⟩ := h'
          have hb := hM _ (List.mem_singleton_self _)
          exact ⟨⟨fn, lb, 0, rs, dst⟩, Reach.refl _, rfl, rfl,
            ⟨_, hb, Nat.le_refl _, Or.inr ⟨_, _, rfl, rfl, rfl⟩⟩, fr_regs (fun _ _ => rfl)⟩
        · simp at h
    | @val τ e =>
        cases τ with
        | int lo hi =>
            simp only [lowerErgF] at h
            rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
            · simp [he] at h
            simp only [he] at h
            split at h
            · rename_i hf
              rcases hnc : numCode lo hi (retW n (some (.int lo hi))) (n + 1) 0 oe r1 with ⟨cn, on, r2⟩
              rw [hnc] at h
              have h' := Option.some.inj h
              simp only [Prod.mk.injEq] at h'
              obtain ⟨rfl, rfl⟩ := h'
              have hb := hM _ (List.mem_singleton_self _)
              obtain ⟨Fe, Ife⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σ₀ σ ρ m rs hR hE hc
              have hfit : Ar.Fits lo hi 128 := Ife lo hi rfl
              have Fn : Frag m rs st.r (ce ++ cn, on, r2)
                  (Val.ofInt (retW n (some (.int lo hi))) (okZ n (some (.int lo hi)) (evalErg σ₀ (.val e) σ ρ))) := by
                refine frag_two (ct := (cn, on, r2)) Fe (fun rsA hag hoe hlte => ?_)
                have F := numCode_frag (lo := lo) (hi := hi) (retW n (some (.int lo hi))) (n + 1) 0
                  (eval σ₀ e σ ρ).n hfit (eval σ₀ e σ ρ).lo_le (eval σ₀ e σ ρ).le_hi oe r1 m rsA hoe hlte
                rw [hnc] at F
                have e0 : ((0 : Nat) : Int) + ((n + 1 : Nat) : Int) * ((eval σ₀ e σ ρ).n - lo)
                    = okZ n (some (.int lo hi)) (evalErg σ₀ (.val e) σ ρ) := by
                  simp [okZ, evalErg]
                rw [e0] at F
                exact F
              obtain ⟨rs1, hs1, _, hag1, _, hev⟩ := Fn
              have hr := reach_block_end (S := S) (ks := ks) (dst := dst) hb hs1
              exact ⟨⟨fn, lb, (ce ++ cn).length, rs1, dst⟩, hr, rfl, rfl, ⟨_, hb, Nat.le_refl _,
                Or.inr ⟨on, _, rfl, rfl, hev⟩⟩, fr_regs hag1⟩
            · simp at h
        | _ => simp [lowerErgF] at h

/-- `return why r`. -/
theorem lowerWhy_ok (lay : Layout D) (cenv : List Reg) (n : Nat) (eo : Option GTy) (r : Nat) (lb : Lbl)
    (st st' : St) (blks : List Block) (h : lowerWhy n eo r lb st = some (blks, st')) (M : Modl) (S : Sees)
    (fn : Nat) (hM : ∀ b ∈ blks, M.blk fn b.lbl = some b) (m : Mem) (rs : Regs) (ks : List Frame)
    (dst : Option Reg) :
    ∃ f', Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m f' ks) ∧ f'.fn = fn ∧ f'.dst = dst ∧
      RetAt M f' (whyImg n eo r) ∧ Fr lay cenv st.r m rs m f'.regs := by
  unfold lowerWhy at h
  split at h
  · have h' := Option.some.inj h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    have hb := hM _ (List.mem_singleton_self _)
    exact ⟨⟨fn, lb, 0, rs, dst⟩, Reach.refl _, rfl, rfl,
      ⟨_, hb, Nat.le_refl _, Or.inr ⟨_, _, rfl, rfl, rfl⟩⟩, fr_regs (fun _ _ => rfl)⟩
  · simp at h

end Gabbro.Code.Lower
