import Grammatik.Berechenbarkeit.Storage.GStack.Reclaim

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A binder-producing prefix of actual G code, uniform in its continuation. -/
abbrev Allocator (A : FreiForm D) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) :=
  ∀ {Λ'}, Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ' → Block D V l Γ Λ Λ'

/-- An executed allocation effect, shared by fresh and recycled storage. This is
proved from concrete G terms below; it is not an availability or callee axiom. -/
def Allocated (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (A : FreiForm D) (allocator : Allocator A V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (value : Wert D (D.typ A.tab A.feld)) (slot : Int) : Prop :=
  ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
    (∀ {Λ'} (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
      execBlock O passes R (allocator rest) σ ρ = (execBlock O passes R rest σ' (.cons k ρ)).schrumpf) ∧
    k.n = slot ∧ A.Fremd σ σ' ∧ A.FreiOk σ' ∧
    (∀ i, A.Lebt σ' i ↔ i = slot ∨ A.Lebt σ i) ∧ ¬ A.Lebt σ slot ∧
    (∀ i, σ'.slots A.tab i A.feld = if i = slot then value else σ.slots A.tab i A.feld)

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

theorem fresh_allocated (A : FreiForm D) (x : Var Γ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hf : A.FreiOk σ) (hroom : A.stand σ < D.count A.tab) :
    Allocated O passes R A (Block.arenaAlloc A.toArenaForm (.var x) hwT hLT hwU hLU failure)
      σ ρ (ρ.get x) (A.stand σ) := by
  have hk : 0 ≤ A.stand σ ∧ A.stand σ ≤ D.count A.tab - 1 := ⟨A.stand_nonneg σ, by omega⟩
  have hprefix : ∃ (σp : World D) (k : Wert D (Ty.index (D.count A.tab))),
      (∀ {Λ'} (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.arenaAlloc A.toArenaForm (.var x) hwT hLT hwU hLU failure rest) σ ρ =
          (execBlock O passes R rest σp (.cons k ρ)).schrumpf) ∧
      k.n = A.stand σ ∧ (∀ i, σp.slots A.tab i A.feld =
        if i = A.stand σ then ρ.get x else σ.slots A.tab i A.feld) := by
    refine ⟨?world, ⟨A.stand σ, hk.1, hk.2⟩, ?execution, rfl, ?payload⟩
    case execution =>
      intro Λ' rest
      rw [arenaAlloc_unter_schranke O passes R A.toArenaForm (.var x) hwT hLT hwU hLU failure rest σ ρ hroom]
      rfl
    case payload =>
      intro i
      simp only [World.lese, World.merke, World.schreibSlot, World.storeSlot, eval, List.map_cons, List.map_nil,
  List.cons_append, List.nil_append, Expr.weaken, Expr.ins, Var.ins, List.map_append, List.append_assoc,
  Block.arenaBump, Int.reduceAdd, orte_umTyp, eval_umTyp, World.slots_schreibGlob, ↓reduceDIte]; rfl
  obtain ⟨σp, k, hexec, hkn, hbytes⟩ := hprefix
  obtain ⟨σm, hm, hhead, hlinks, hcount, hframe⟩ :=
    arenaRumpf_ausfuehren O passes R A (.var x) hwT hLT hwU hLU (.nil)
      (σ.lese Λ [Sum.inr A.zaehl]) ⟨A.stand σ, hk.1, hk.2⟩ ρ
  have hworld : σm = σp := by
    have he := hexec (.nil)
    rw [arenaAlloc_unter_schranke O passes R A.toArenaForm (.var x) hwT hLT hwU hLU
      failure (.nil) σ ρ hroom, hm] at he
    change (Ausgang.ok σm ρ : Ausgang V l Γ) = .ok σp ρ at he
    cases he; rfl
  subst σm
  refine ⟨σp, k, hexec, hkn, hframe, (A.lebt_bump hf hhead hlinks hcount).1,
    fun i => A.bump_live_iff hf hhead hlinks hcount i, ?_, hbytes⟩
  intro hn
  have := hn.2.1
  omega

theorem reused_allocated (A : FreiForm D) (x : Var Γ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hf : A.FreiOk σ) (hroom : A.kopfSt σ < D.count A.tab) :
    Allocated O passes R A (Block.freiNimm A (.var x) hwT hLT hwF hLF failure)
      σ ρ (ρ.get x) (A.kopfSt σ) := by
  have hk : 0 ≤ A.kopfSt σ ∧ A.kopfSt σ ≤ D.count A.tab - 1 := ⟨A.kopfSt_nonneg σ, by omega⟩
  have hprefix : ∃ (σp : World D) (k : Wert D (Ty.index (D.count A.tab))),
      (∀ {Λ'} (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.freiNimm A (.var x) hwT hLT hwF hLF failure rest) σ ρ =
          (execBlock O passes R rest σp (.cons k ρ)).schrumpf) ∧
      k.n = A.kopfSt σ ∧ (∀ i, σp.slots A.tab i A.feld =
        if i = A.kopfSt σ then ρ.get x else σ.slots A.tab i A.feld) := by
    refine ⟨?world, ⟨A.kopfSt σ, hk.1, hk.2⟩, ?execution, rfl, ?payload⟩
    case execution =>
      intro Λ' rest
      simp only [Block.freiNimm, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
      rw [dite_eq_left (by exact hk)]
      rfl
    case payload =>
      intro i
      simp only [World.schreibSlot, World.merke, World.storeSlot, eval, World.lese, List.map_cons, List.map_nil,
  List.cons_append, List.nil_append, World.slots_schreibGlob, Expr.weaken, Expr.ins, Var.ins, List.map_append,
  List.append_assoc, ↓reduceDIte]; rfl
  obtain ⟨σp, k, hexec, hkn, hbytes⟩ := hprefix
  obtain ⟨σm, km, hm, hkm, hhead, hlinks, hcount, hframe⟩ :=
    nimmAlloc_fakten O passes R A (.var x) hwT hLT hwF hLF failure (.nil) σ ρ hroom
  have hworld : σm = σp := by
    have he := hexec (.nil)
    rw [hm] at he
    change (Ausgang.ok σm ρ : Ausgang V l Γ) = .ok σp ρ at he
    cases he; rfl
  subst σm
  refine ⟨σp, k, hexec, hkn, hframe, (A.lebt_abheb hroom hf hhead hlinks hcount).1,
    fun i => A.take_live_iff hroom hf hhead hlinks hcount i, ?_, hbytes⟩
  have honfree : A.AufListe σ (A.kopfSt σ) := by
    obtain ⟨entries, hc, _, _⟩ := hf
    generalize heq : A.kopfSt σ = root at hc hroom ⊢
    cases hc with
    | nil => exact absurd hroom (Int.lt_irrefl _)
    | cons root hlo hhi tail ht =>
      exact ⟨root :: tail, by rw [heq]; exact FreiForm.Kette.cons root hlo hhi tail ht, List.mem_cons_self⟩
  intro hn
  exact hn.2.2 honfree

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
