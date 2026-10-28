import Grammatik.Code.Refine.Frag

/-
  File:      Grammatik/Code/Refine/Env.lean
  Subject:   TRACK L, PHASE L1 -- THE LOCALS: `EnvRep`, the relation between G's variable
             environment and the `alloc` cells the lowering gives them, and its frame lemmas.

  Variable number `i` of the context lives in the block its alloca register `cenv[i]` points to
  (`rs r = ptr b 0`); the block holds the encoding of the variable's value. A local block is
  `Fresh`: not the block of a table or a global; and different variables have different blocks.
  What changes registers that are no variable's (`envRep_regs`), or memory only at blocks that
  are no local (`envRep_load`), keeps the relation.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Env Wert Ctx Var)

variable {D : Deklaration}

/-- A block that is no table and no global. -/
def Fresh (lay : Layout D) (b : Nat) : Prop :=
  (∀ t, b ≠ lay.gblk t) ∧ (∀ g, b ≠ lay.ggblk g) ∧ (∀ L, b ≠ lay.lblk L ∧ b ≠ lay.lsrv L)

/-- The environment `ρ` lives in the cells the registers `cenv` point to. -/
def EnvRep (lay : Layout D) (rs : Regs) (m : Mem) : {Γ : Ctx} → List Reg → Env D Γ → Prop
  | _, [], .nil => True
  | _, r :: cs, .cons (τ := τ) v ρ =>
      (supp τ = true ∧ ∃ b, rs r = some (.ptr b 0) ∧ Fresh lay b ∧
        m.load b 0 (memTy τ) = some (encM lay τ v) ∧
        (∀ r' ∈ cs, ∀ b', rs r' = some (.ptr b' 0) → b' ≠ b)) ∧ EnvRep lay rs m cs ρ
  | _, _, _ => False

theorem envRep_get {lay : Layout D} {rs : Regs} {m : Mem} :
    ∀ {Γ : Ctx} {τ : GTy} (x : Var Γ τ) (cenv : List Reg) (ρ : Env D Γ),
      EnvRep lay rs m cenv ρ →
      ∃ r b, cenv[varIdx x]? = some r ∧ supp τ = true ∧ rs r = some (.ptr b 0) ∧ Fresh lay b ∧
        m.load b 0 (memTy τ) = some (encM lay τ (ρ.get x))
  | _, _, .here, [], .cons v ρ, h => absurd h (by simp only [EnvRep, not_false_eq_true])
  | _, _, .here, r :: cs, .cons v ρ, h => by
      obtain ⟨⟨hs, b, hr, hf, hl, _⟩, _⟩ := h
      exact ⟨r, b, rfl, hs, hr, hf, hl⟩
  | _, _, .there x, [], .cons w ρ, h => absurd h (by simp only [EnvRep, not_false_eq_true])
  | _, _, .there x, r :: cs, .cons w ρ, h => by
      obtain ⟨_, h2⟩ := h
      obtain ⟨r', b, h1, hs, hr, hf, hl⟩ := envRep_get x cs ρ h2
      exact ⟨r', b, by simpa [varIdx] using h1, hs, hr, hf, hl⟩

theorem envRep_regs {lay : Layout D} {rs rs' : Regs} {m : Mem} :
    ∀ {Γ : Ctx} (cenv : List Reg) (ρ : Env D Γ), (∀ r ∈ cenv, rs' r = rs r) →
      EnvRep lay rs m cenv ρ → EnvRep lay rs' m cenv ρ
  | _, [], .nil, _, _ => trivial
  | _, r :: cs, .cons v ρ, hag, h => by
      obtain ⟨⟨hs, b, hr, hf, hl, hd⟩, h2⟩ := h
      refine ⟨⟨hs, b, ?_, hf, hl, ?_⟩,
        envRep_regs cs ρ (fun r' hr' => hag r' (List.mem_cons_of_mem _ hr')) h2⟩
      · rw [hag r (List.mem_cons_self ..)]; exact hr
      · intro r' hr' b' hb'
        rw [hag r' (List.mem_cons_of_mem _ hr')] at hb'
        exact hd r' hr' b' hb'
  | _, [], .cons .., _, h => absurd h (by simp only [EnvRep, not_false_eq_true])
  | _, _ :: _, .nil, _, h => absurd h (by simp only [EnvRep, not_false_eq_true])

theorem envRep_load {lay : Layout D} {rs : Regs} {m m' : Mem} :
    ∀ {Γ : Ctx} (cenv : List Reg) (ρ : Env D Γ),
      (∀ r ∈ cenv, ∀ b, rs r = some (.ptr b 0) → Fresh lay b → ∀ o t v,
        m.load b o t = some v → m'.load b o t = some v) →
      EnvRep lay rs m cenv ρ → EnvRep lay rs m' cenv ρ
  | _, [], .nil, _, _ => trivial
  | _, r :: cs, .cons v ρ, hm, h => by
      obtain ⟨⟨hs, b, hr, hf, hl, hd⟩, h2⟩ := h
      exact ⟨⟨hs, b, hr, hf, hm r (List.mem_cons_self ..) b hr hf _ _ _ hl, hd⟩,
        envRep_load cs ρ (fun r' hr' => hm r' (List.mem_cons_of_mem _ hr')) h2⟩
  | _, [], .cons .., _, h => absurd h (by simp only [EnvRep, not_false_eq_true])
  | _, _ :: _, .nil, _, h => absurd h (by simp only [EnvRep, not_false_eq_true])

/-- The blocks of the locals exist. -/
theorem envRep_blocks_lt {lay : Layout D} {rs : Regs} {m : Mem} (hw : m.Wf) :
    ∀ {Γ : Ctx} (cenv : List Reg) (ρ : Env D Γ), EnvRep lay rs m cenv ρ →
      ∀ r ∈ cenv, ∀ b, rs r = some (.ptr b 0) → b < m.next
  | _, [], .nil, _, r, hr, b, hb => absurd hr (by simp only [List.not_mem_nil, not_false_eq_true])
  | _, c :: cs, .cons v ρ, h, r, hr, b, hb => by
      obtain ⟨⟨hs, b0, hb0, hf, hl, hd⟩, h2⟩ := h
      rcases List.mem_cons.mp hr with rfl | hr'
      · rw [hb0] at hb
        have := Option.some.inj hb
        injection this with e1 e2
        subst e1
        exact load_blk_lt hw hl
      · exact envRep_blocks_lt hw cs ρ h2 r hr' b hb
  | _, [], .cons .., h, _, _, _, _ => absurd h (by simp only [EnvRep, not_false_eq_true])
  | _, _ :: _, .nil, h, _, _, _, _ => absurd h (by simp only [EnvRep, not_false_eq_true])

/-- Storing into a local's cell sets that variable. -/
theorem envRep_set {lay : Layout D} {rs : Regs} {m m' : Mem} {b : Nat} :
    ∀ {Γ : Ctx} {τ : GTy} (x : Var Γ τ) (cenv : List Reg) (ρ : Env D Γ) (v : Wert D τ) (r : Reg),
      EnvRep lay rs m cenv ρ → cenv[varIdx x]? = some r → rs r = some (.ptr b 0) →
      m.store b 0 (memTy τ) (encM lay τ v) = some m' → EnvRep lay rs m' cenv (ρ.set x v)
  | _, _, .here, [], .cons w ρ, v, r, hE, _, _, _ => absurd hE (by simp only [EnvRep, not_false_eq_true])
  | _, _, .here, c :: cs, .cons w ρ, v, r, hE, hcen, hr, hst => by
      have hc : c = r := by simpa [varIdx] using hcen
      subst hc
      obtain ⟨⟨hs, b0, hb0, hf, hl, hd⟩, h2⟩ := hE
      rw [hb0] at hr
      have := Option.some.inj hr
      injection this with e1 e2
      subst e1
      refine ⟨⟨hs, b0, hb0, hf, load_store_of hst (dec_enc_encM lay v hs), hd⟩, ?_⟩
      refine envRep_load cs ρ (fun r' hr' b' hb' hf' o t v' hl' => ?_) h2
      rw [load_store_other hst (Or.inl (hd r' hr' b' hb'))]
      exact hl'
  | _, _, .there x, [], .cons w ρ, v, r, hE, _, _, _ => absurd hE (by simp only [EnvRep, not_false_eq_true])
  | _, _, .there x, c :: cs, .cons w ρ, v, r, hE, hcen, hr, hst => by
      obtain ⟨⟨hs, b0, hb0, hf, hl, hd⟩, h2⟩ := hE
      have hcen' : cs[varIdx x]? = some r := by simpa [varIdx] using hcen
      have hrm : r ∈ cs := List.mem_of_getElem? hcen'
      have hne : b ≠ b0 := fun e => hd r hrm b hr (by rw [e])
      refine ⟨⟨hs, b0, hb0, hf, ?_, hd⟩, envRep_set x cs ρ v r h2 hcen' hr hst⟩
      rw [load_store_other hst (Or.inl (fun e => hne e.symm))]
      exact hl

/-- A store into a table, a global or the cell of a global never touches a local. -/
theorem fresh_load_store {lay : Layout D} {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') (hb : ¬ Fresh lay b) :
    ∀ b' o' t' v', Fresh lay b' → m.load b' o' t' = some v' → m'.load b' o' t' = some v' := by
  intro b' o' t' v' hf hl
  rw [load_store_other h (Or.inl (fun e => hb (e ▸ hf)))]
  exact hl

/-- Allocation never touches an existing cell. -/
theorem alloc_load_some {m : Mem} (hw : m.Wf) (n : Nat) (z : Bool) :
    ∀ b o t v, m.load b o t = some v → (m.alloc n z).1.load b o t = some v := by
  intro b o t v hl
  have := load_blk_lt hw hl
  rw [alloc_load m n z b (by omega)]
  exact hl

/-! ## A new local -/

/-- The memory with its global blocks: every table, global and lock has a block that exists. -/
def WfL (lay : Layout D) (m : Mem) : Prop :=
  m.Wf ∧ (∀ t, lay.gblk t < m.next) ∧ (∀ g, lay.ggblk g < m.next) ∧ (∀ L, lay.lblk L < m.next ∧ lay.lsrv L < m.next)

theorem wfL_store {lay : Layout D} {m m' : Mem} {b : Nat} {o : Int} {t : Ty} {v : Val}
    (h : m.store b o t v = some m') (hw : WfL lay m) : WfL lay m' := by
  refine ⟨store_wf h hw.1, fun t' => ?_, fun g => ?_, fun L => ?_⟩
  · rw [store_next h]; exact hw.2.1 t'
  · rw [store_next h]; exact hw.2.2.1 g
  · rw [store_next h]; exact hw.2.2.2 L

theorem wfL_alloc {lay : Layout D} {m : Mem} (hw : WfL lay m) (n : Nat) (z : Bool) :
    WfL lay (m.alloc n z).1 := by
  refine ⟨alloc_wf hw.1 n z, fun t' => ?_, fun g => ?_, fun L => ?_⟩
  · have := hw.2.1 t'; simp only [Mem.alloc]; omega
  · have := hw.2.2.1 g; simp only [Mem.alloc]; omega
  · have := hw.2.2.2 L; simp only [Mem.alloc]; omega

theorem alloc_blk (m : Mem) (n : Nat) (z : Bool) :
    ∃ cells, (m.alloc n z).1.blks m.next = some ⟨n, cells⟩ := by
  exact ⟨fun k => if k < n ∧ z = true then some (.byte 0) else none, by simp only [Mem.alloc, Mem.setBlk, ↓reduceIte]⟩

theorem alloc_store_ok (m : Mem) (t : Ty) (x : Val) (hs : t.scalar = true) (hx : x.ty = t) :
    ∃ m', (m.alloc t.size false).1.store m.next 0 t x = some m' := by
  obtain ⟨cells, hb⟩ := alloc_blk m t.size false
  have hle := Ty.store_le_size t hs
  unfold Mem.store
  rw [hb]
  have hin : Mem.inside t.size 0 t := ⟨Int.le_refl _, hs, by simpa using hle, Int.zero_emod _⟩
  simp only [hin, hx, and_self, ↓reduceIte, Int.toNat_zero, Option.some.injEq, exists_eq']

end Gabbro.Code.Lower
