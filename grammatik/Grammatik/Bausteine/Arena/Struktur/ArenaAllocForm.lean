/-
  File:      Grammatik/ArenaAllocForm.lean
  Subject:   THE ALLOCATOR MOVES FOR ANY CONTINUATION (PLAN-DYNAMISCH.md section 8a.1, step (3), forms half).

  `ArenaFrei.lean` proves what `free`, `alloc` from the free list and `alloc` from the counter leave, but with the
  empty continuation and, for `free`, only for the NEWEST bound index. The recognizer (`ArenaErkenner.lean`) runs
  them in the middle of a body, so this file states the same facts for every continuation `rest`:

    * `Block.freiVar A x … rest`      -- `nxt[x] = kopf;  kopf = x;  rest`, for ANY bound index `x` of the context;
    * `frischAlloc_ausfuehren`        -- `arenaAlloc` under `stand < count`: the binder holds the counter, the run
                                         continues in the world the bump leaves, and `FreiOk`/liveness are kept;
    * `nimmAlloc_ausfuehren`          -- `freiNimm` under a non-empty free list, likewise;
    * `nimmAlloc_voll`                -- `freiNimm` on an empty free list takes its `else`;
    * `freiVar_ausfuehren`            -- `free` of a live slot: the slot dies, every other live slot stays live.
-/
import Grammatik.Bausteine.Arena.Struktur.ArenaFremd

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn

variable {D : Deklaration}

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The index variable `x`, at the free-list head's declared type. -/
def freiKopfNeuX (A : FreiForm D) (x : Var Γ (Ty.index (D.count A.tab))) : Expr D Γ Λ (D.gtyp A.kopf) :=
  Expr.umTyp A.hkopf.symm
    (Expr.widen (lo := 0) (hi := D.count A.tab - 1) (lo' := 0) (hi' := D.count A.tab)
      (by omega) (by omega) (Expr.var x))

/-- **`free A[x]; rest`** for ANY bound index `x`: the link of `x` takes the old head, the head becomes `x`. -/
def freiVar (A : FreiForm D) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .cons (.assignSlot A.tab A.nxt (Expr.var x) (freiKopfAlt A hLK) hwT hLT)
    (.cons (.assignGlob A.kopf (freiKopfNeuX A x) hwK hLK) rest)

end Block

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (A : FreiForm D)

/-- **`free A[x]` leaves, for every continuation:** the head is `x`, its link the old head, every other link and the
    counter as before; only the head, the free link and the recorded accesses moved. -/
theorem freiVar_ausfuehren (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.freiVar A x hwT hLT hwK hLK rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      A.kopfSt σ' = (ρ.get x).n ∧ A.naechst σ' (ρ.get x).n = A.kopfSt σ ∧
      (∀ j, j ≠ (ρ.get x).n → A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ ∧ A.Fremd σ σ' := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eval, Block.freiKopfNeuX, Block.freiKopfAlt, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      FreiForm.kopfSt_schreibGlob_kopf, FreiForm.kopfSt_schreibSlot, FreiForm.kopfSt_lese]
    exact umTyp_rund_n A.hkopf _
  · simp only [eval, Block.freiKopfNeuX, Block.freiKopfAlt, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot, FreiForm.naechst_lese, FreiForm.kopfSt_lese,
      if_true]
    exact umTyp_trans_n _ _ _
  · intro j hj
    simp only [eval, Block.freiKopfNeuX, Block.freiKopfAlt, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot, FreiForm.naechst_lese, if_neg hj]
  · simp only [eval, Block.freiKopfNeuX, Block.freiKopfAlt, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      ArenaForm.stand_lese, FreiForm.stand_schreibGlob_kopf, ArenaForm.stand_schreibSlot]
  · refine ⟨fun g _ hk _ => ?_, fun k f hf hn => ?_⟩
    · simp [eval, hk]
    · simp [eval, World.slots_schreibSlot_ne, hn]

/-- **`free` of a live slot, for every continuation:** the free list stays well formed, every other live slot stays
    live, the released slot is dead, and only the allocator's places moved. -/
theorem freiVar_lebt (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hlebt : A.Lebt σ (ρ.get x).n) (hok : A.FreiOk σ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.freiVar A x hwT hLT hwK hLK rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧ A.Fremd σ σ' ∧
      A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → j ≠ (ρ.get x).n → A.Lebt σ' j) ∧ ¬ A.Lebt σ' (ρ.get x).n := by
  obtain ⟨σ', he, h1, h2, h3, h4, hf⟩ := freiVar_ausfuehren O passes R A x hwT hLT hwK hLK rest σ ρ
  obtain ⟨hok', hmono, hdead⟩ := A.lebt_frei _ hlebt hok h1 h2 h3 h4
  exact ⟨σ', he, hf, hok', hmono, hdead⟩

/-- **The body of an allocation from the counter, for every continuation:** the store and the bump; head, links and
    the rest of the free list stay, the counter becomes `k + 1`. -/
theorem arenaRumpf_ausfuehren (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (k : Wert D (Ty.index (D.count A.tab))) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.arenaRumpf A.toArenaForm v hwT hLT hwG hLG rest) σ (.cons k ρ)
          = execBlock (V := V) O passes R rest σ' (.cons k ρ) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = k.n + 1 ∧ A.Fremd σ σ' := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [eval, Block.arenaBump, eval_umTyp, orte_umTyp, Expr.orte, List.nil_append,
      FreiForm.kopfSt_schreibGlob_zaehl, FreiForm.kopfSt_schreibSlot_feld, FreiForm.kopfSt_lese]
  · intro j
    simp only [eval, Block.arenaBump, eval_umTyp, orte_umTyp, Expr.orte, List.nil_append,
      FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot_feld, FreiForm.naechst_lese]
  · simp only [eval, Block.arenaBump, eval_umTyp, orte_umTyp, Expr.orte, List.nil_append,
      ArenaForm.stand_lese, ArenaForm.stand_schreibGlob]
    exact umTyp_trans_n _ _ _
  · refine ⟨fun g hz _ _ => ?_, fun k' f hf hn => ?_⟩
    · simp [eval, Block.arenaBump, hz]
    · simp [eval, Block.arenaBump, World.slots_schreibSlot_ne, hf]

/-- **`let i = alloc A (v) else voll; rest` from the counter, executed in the middle of a body:** under `stand < count`
    the binder holds the counter, the run continues in the world the allocation leaves; `FreiOk` and every liveness
    are kept and the new slot is live. -/
theorem frischAlloc_ausfuehren (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < D.count A.tab) (hok : A.FreiOk σ) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = A.stand σ ∧ A.Fremd σ σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → A.Lebt σ' j) ∧ A.Lebt σ' k.n := by
  rw [arenaAlloc_unter_schranke O passes R A.toArenaForm v hwT hLT hwG hLG voll rest σ ρ h]
  obtain ⟨σ', he, h1, h2, h3, hf⟩ := arenaRumpf_ausfuehren O passes R A v hwT hLT hwG hLG rest
    (σ.lese Λ [Sum.inr A.zaehl]) ⟨A.stand σ, A.stand_nonneg σ, by omega⟩ ρ
  obtain ⟨hok', hmono, hnew⟩ := A.lebt_bump (σ := σ) (σ' := σ') hok h1 h2 h3
  exact ⟨σ', ⟨A.stand σ, A.stand_nonneg σ, by omega⟩, by rw [he], rfl, hf, hok', hmono, hnew⟩

/-- **`alloc` from the counter on a full arena takes its `else`.** -/
theorem frischAlloc_voll (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : ¬ A.stand σ < D.count A.tab) :
    execBlock (V := V) O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.zaehl]) ρ).zuAusgang :=
  arenaAlloc_an_schranke O passes R A.toArenaForm v hwT hLT hwG hLG voll rest σ ρ
    (Int.le_antisymm (A.stand_le σ) (Int.not_lt.mp h))

/-- **What `alloc` from the free list leaves, for every continuation:** under a non-empty free list the binder holds the
    old head, the head becomes its link, no link moves and the counter stays. -/
theorem nimmAlloc_fakten (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hne : A.kopfSt σ < D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.freiNimm A v hwT hLT hwK hLK voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = A.kopfSt σ ∧ A.kopfSt σ' = A.naechst σ (A.kopfSt σ) ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧
      A.stand σ' = A.stand σ ∧ A.Fremd σ σ' := by
  have hk : (0 : Int) ≤ A.kopfSt σ ∧ A.kopfSt σ ≤ D.count A.tab - 1 :=
    ⟨A.kopfSt_nonneg σ, by omega⟩
  simp only [Block.freiNimm, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  refine ⟨?s, ?k, ?e, ?n, ?r1, ?r2, ?r3, ?r4⟩
  case e => rfl
  case n => rfl
  case r1 =>
    simp only [eval, Block.freiKopfWeiter, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      List.cons_append, List.append_nil, FreiForm.kopfSt_schreibGlob_kopf, FreiForm.kopfSt_schreibSlot_feld,
      FreiForm.naechst_lese, FreiForm.kopfSt_lese]
    exact umTyp_trans_n _ _ _
  case r2 =>
    intro j
    simp only [eval, Block.freiKopfWeiter, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      List.cons_append, List.append_nil, FreiForm.naechst_schreibGlob, FreiForm.naechst_schreibSlot_feld,
      FreiForm.naechst_lese]
  case r3 =>
    simp only [eval, Block.freiKopfWeiter, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
      List.cons_append, List.append_nil, ArenaForm.stand_lese, FreiForm.stand_schreibGlob_kopf,
      ArenaForm.stand_schreibSlot]
  case r4 =>
    refine ⟨fun g _ hk _ => ?_, fun k' f hf hn => ?_⟩
    · simp [eval, hk]
    · simp [eval, World.slots_schreibSlot_ne, hf]

/-- **`let i = alloc A (v) else voll; rest` from the free list, executed in the middle of a body:** `FreiOk` and every
    liveness are kept, the slot handed out is live and WAS on the free list. -/
theorem nimmAlloc_ausfuehren (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.freiNimm A v hwT hLT hwK hLK voll rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      k.n = A.kopfSt σ ∧ A.Fremd σ σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ j → A.Lebt σ' j) ∧ A.Lebt σ' k.n ∧
      A.AufListe σ k.n := by
  obtain ⟨σ', k, he, hkn, h1, h2, h3, hf⟩ := nimmAlloc_fakten O passes R A v hwT hLT hwK hLK voll rest σ ρ hne
  obtain ⟨hok', hmono, hnew⟩ := A.lebt_abheb hne hok h1 h2 h3
  have hauf : A.AufListe σ (A.kopfSt σ) := by
    obtain ⟨L0, hk0, _, _⟩ := hok
    generalize hg : A.kopfSt σ = kk at hk0 hne ⊢
    cases hk0 with
    | nil => exact absurd hne (Int.lt_irrefl _)
    | cons k h0 hk1 L1 h1 =>
      refine ⟨kk :: L1, ?_, List.mem_cons_self⟩
      rw [hg]; exact FreiForm.Kette.cons kk h0 hk1 L1 h1
  exact ⟨σ', k, he, hkn, hf, hok', hmono, hkn ▸ hnew, hkn ▸ hauf⟩

/-- **`alloc` from the free list on an empty free list takes its `else`.** -/
theorem nimmAlloc_voll (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hn : ¬ A.kopfSt σ < D.count A.tab) :
    execBlock (V := V) O passes R (Block.freiNimm A v hwT hLT hwK hLK voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.kopf]) ρ).zuAusgang := by
  have hn' : ¬ ((0 : Int) ≤ A.kopfSt σ ∧ A.kopfSt σ ≤ D.count A.tab - 1) := by
    intro h; exact hn (by omega)
  simp only [Block.freiNimm, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_neg (by exact hn')]

end Bedeutung

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.freiVar_lebt
#print axioms Gabbro.Grammatik.frischAlloc_ausfuehren
#print axioms Gabbro.Grammatik.nimmAlloc_ausfuehren
