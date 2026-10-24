import Grammatik.Berechenbarkeit.Storage.GStack.Allocation

/-! The allocator a growing program uses: a freed cell first, a fresh one while the arena has room, and the
declared failure block when it has none. It is ordinary G code -- an `ite` on the free-list head choosing between
`Block.freiNimm` and `Block.arenaAlloc` -- and both branches carry the same continuation. Three execution
theorems cover its three outcomes: reuse, bump, and the failure block, which is reached ONLY when the free list is
empty and the counter stands at the count. -/

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The free list is empty: its head holds the end marker `count`. -/
def freeEmpty (A : FreiForm D) (hLK : gdarf D A.kopf Λ) : Expr D Γ Λ .bool :=
  .eq (Expr.umTyp A.hkopf (.glob A.kopf hLK)) (.lit (D.count A.tab))

theorem freeEmpty_eval (A : FreiForm D) (hLK : gdarf D A.kopf Λ) (σ : World D) (ρ : Env D Γ) :
    eval σ (freeEmpty (Γ := Γ) A hLK) σ ρ = decide (A.kopfSt σ = D.count A.tab) := by
  simp only [freeEmpty, eval, eval_umTyp]
  rfl

namespace Block

/-- `let i = alloc A (v) else voll;` with reuse: the head of the free list when there is one, else the counter. -/
def takeOrBump (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) : Allocator A V l Γ Λ :=
  fun rest => .cons (.ite (freeEmpty A hLK)
      (Gabbro.Grammatik.Block.arenaAlloc A.toArenaForm v hwT hLT hwU hLU voll rest)
      (Gabbro.Grammatik.Block.freiNimm A v hwT hLT hwK hLK voll rest)) .nil

end Block

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- A one-statement block runs as its statement. -/
theorem execBlock_single {Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.cons s .nil) σ ρ = execStmt O passes R s σ ρ := by
  simp only [execBlock]
  split <;> simp_all

theorem takeOrBump_reused (A : FreiForm D) (x : Var Γ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hf : A.FreiOk σ) (hroom : A.kopfSt σ < D.count A.tab) :
    Allocated O passes R A (Block.takeOrBump A (.var x) hwT hLT hwK hLK hwU hLU voll)
      σ ρ (ρ.get x) (A.kopfSt σ) := by
  let σl := σ.lese Λ (freeEmpty (Γ := Γ) A hLK).orte
  obtain ⟨σ', k, hexec, hkn, hframe, hf', hlive, hold, hbytes⟩ :=
    reused_allocated O passes R A x hwT hLT hwK hLK voll σl ρ (A.freiOk_gleich (σ := σ) (σ' := σl) rfl (fun _ => rfl) rfl hf) hroom
  refine ⟨σ', k, ?_, hkn, hframe, hf', fun i => (hlive i).trans (or_congr Iff.rfl (A.lebt_gleich (σ := σ) (σ' := σl) rfl (fun _ => rfl) rfl i)),
    fun h => hold ((A.lebt_gleich (σ := σ) (σ' := σl) rfl (fun _ => rfl) rfl _).mpr h), hbytes⟩
  intro Λ' rest
  dsimp only [Block.takeOrBump]
  rw [execBlock_single]
  simp only [execStmt]
  have hne : A.kopfSt σl ≠ D.count A.tab := by show A.kopfSt σ ≠ _; omega
  simp only [freeEmpty_eval, wahr?]
  rw [if_neg (by simp only [decide_eq_true_eq]; exact hne)]
  exact hexec rest

theorem takeOrBump_fresh (A : FreiForm D) (x : Var Γ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hf : A.FreiOk σ) (hnone : A.kopfSt σ = D.count A.tab) (hroom : A.stand σ < D.count A.tab) :
    Allocated O passes R A (Block.takeOrBump A (.var x) hwT hLT hwK hLK hwU hLU voll)
      σ ρ (ρ.get x) (A.stand σ) := by
  let σl := σ.lese Λ (freeEmpty (Γ := Γ) A hLK).orte
  obtain ⟨σ', k, hexec, hkn, hframe, hf', hlive, hold, hbytes⟩ :=
    fresh_allocated O passes R A x hwT hLT hwU hLU voll σl ρ (A.freiOk_gleich (σ := σ) (σ' := σl) rfl (fun _ => rfl) rfl hf) hroom
  refine ⟨σ', k, ?_, hkn, hframe, hf', fun i => (hlive i).trans (or_congr Iff.rfl (A.lebt_gleich (σ := σ) (σ' := σl) rfl (fun _ => rfl) rfl i)),
    fun h => hold ((A.lebt_gleich (σ := σ) (σ' := σl) rfl (fun _ => rfl) rfl _).mpr h), hbytes⟩
  intro Λ' rest
  dsimp only [Block.takeOrBump]
  rw [execBlock_single]
  simp only [execStmt]
  have heq : A.kopfSt σl = D.count A.tab := hnone
  simp only [freeEmpty_eval, wahr?]
  rw [if_pos (by simp only [decide_eq_true_eq]; exact heq)]
  exact hexec rest

/-- **Out of memory is the failure block, never a value**: with the free list empty and the counter at the
count, the allocation runs `voll`. -/
theorem takeOrBump_full (A : FreiForm D) (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) {Λ'} (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hnone : A.kopfSt σ = D.count A.tab) (hfull : A.stand σ = D.count A.tab) :
    execBlock O passes R (Block.takeOrBump A v hwT hLT hwK hLK hwU hLU voll rest) σ ρ =
      (execEnd O passes R voll ((σ.lese Λ (freeEmpty (Γ := Γ) A hLK).orte).lese Λ [Sum.inr A.zaehl]) ρ).zuAusgang := by
  dsimp only [Block.takeOrBump]
  rw [execBlock_single]
  simp only [execStmt]
  simp only [freeEmpty_eval, FreiForm.kopfSt_lese, hnone, decide_true, wahr?, ite_true]
  exact arenaAlloc_an_schranke O passes R A.toArenaForm v hwT hLT hwU hLU voll rest _ ρ hfull

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
