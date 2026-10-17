import Grammatik.Llvm.Refine.Frag

/-
  File:      Grammatik/Llvm/Refine/Env.lean
  Subject:   TRACK L, PHASE L1 -- THE LOCALS: `EnvRep`, the relation between G's variable
             environment and the `alloca` cells the lowering gives them, and its frame lemmas.

  Variable number `i` of the context lives in the block its alloca register `cenv[i]` points to
  (`rs r = ptr b 0`); the block holds the encoding of the variable's value. A local block is
  `Fresh`: not the block of a table or a global; and different variables have different blocks.
  What changes registers that are no variable's (`envRep_regs`), or memory only at blocks that
  are no local (`envRep_load`), keeps the relation.
-/

namespace Gabbro.Llvm.Lower

open Gabbro.Grammatik (Deklaration Env Wert Ctx Var)

variable {D : Deklaration}

/-- A block that is no table and no global. -/
def Fresh (lay : Layout D) (b : Nat) : Prop := (∀ t, b ≠ lay.gblk t) ∧ (∀ g, b ≠ lay.ggblk g)

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
      ∃ r b, cenv[varIdx x]? = some r ∧ supp τ = true ∧ rs r = some (.ptr b 0) ∧
        m.load b 0 (memTy τ) = some (encM lay τ (ρ.get x))
  | _, _, .here, [], .cons v ρ, h => absurd h (by simp [EnvRep])
  | _, _, .here, r :: cs, .cons v ρ, h => by
      obtain ⟨⟨hs, b, hr, _, hl, _⟩, _⟩ := h
      exact ⟨r, b, rfl, hs, hr, hl⟩
  | _, _, .there x, [], .cons w ρ, h => absurd h (by simp [EnvRep])
  | _, _, .there x, r :: cs, .cons w ρ, h => by
      obtain ⟨_, h2⟩ := h
      obtain ⟨r', b, h1, hs, hr, hl⟩ := envRep_get x cs ρ h2
      exact ⟨r', b, by simpa [varIdx] using h1, hs, hr, hl⟩

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
  | _, [], .cons .., _, h => absurd h (by simp [EnvRep])
  | _, _ :: _, .nil, _, h => absurd h (by simp [EnvRep])

theorem envRep_load {lay : Layout D} {rs : Regs} {m m' : Mem}
    (hm : ∀ b o t v, Fresh lay b → m.load b o t = some v → m'.load b o t = some v) :
    ∀ {Γ : Ctx} (cenv : List Reg) (ρ : Env D Γ), EnvRep lay rs m cenv ρ → EnvRep lay rs m' cenv ρ
  | _, [], .nil, _ => trivial
  | _, r :: cs, .cons v ρ, h => by
      obtain ⟨⟨hs, b, hr, hf, hl, hd⟩, h2⟩ := h
      exact ⟨⟨hs, b, hr, hf, hm _ _ _ _ hf hl, hd⟩, envRep_load hm cs ρ h2⟩
  | _, [], .cons .., h => absurd h (by simp [EnvRep])
  | _, _ :: _, .nil, h => absurd h (by simp [EnvRep])

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

end Gabbro.Llvm.Lower
