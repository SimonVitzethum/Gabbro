import Grammatik.Bausteine.Arena.Ownership.State
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaAllocForm

/-! Exact liveness changes of the existing executed allocator forms, and their
refinement by the ownership ledger. These theorems refer to G's actual world,
`execBlock` and `freiVar`; successful allocation and release are not axioms. -/

namespace Gabbro.Grammatik

variable {D : Deklaration}

namespace FreiForm

theorem aufListe_iff_mem {A : FreiForm D} {σ : World D} {k : Int} {L : List Int}
    (hc : A.Kette σ k L) (hk : A.kopfSt σ = k) (j : Int) :
    A.AufListe σ j ↔ j ∈ L := by
  constructor
  · rintro ⟨L', hL', hj⟩
    rw [hk] at hL'
    exact (Kette.eindeutig hL' hc) ▸ hj
  · intro hj
    exact ⟨L, hk ▸ hc, hj⟩

/-- Release adds exactly one index to the free list. -/
theorem release_live_iff (A : FreiForm D) {σ σ' : World D} (i : Int)
    (hi : A.Lebt σ i) (hok : A.FreiOk σ)
    (hk : A.kopfSt σ' = i) (hn : A.naechst σ' i = A.kopfSt σ)
    (ho : ∀ j, j ≠ i → A.naechst σ' j = A.naechst σ j)
    (hc : A.stand σ' = A.stand σ) (j : Int) :
    A.Lebt σ' j ↔ A.Lebt σ j ∧ j ≠ i := by
  obtain ⟨L, hL, _, _⟩ := hok
  have hiL : i ∉ L := fun h => hi.2.2 ⟨L, hL, h⟩
  have hcount : i < D.count A.tab := by
    have hlt := hi.2.1
    have hle := A.stand_le σ
    omega
  have hnew : A.Kette σ' i (i :: L) := by
    refine Kette.cons i hi.1 hcount L ?_
    rw [hn]
    exact Kette.uebertragen hL (fun k hkm => ho k (fun he => hiL (he ▸ hkm)))
  have h_old := aufListe_iff_mem hL rfl j
  have h_new := aufListe_iff_mem hnew hk j
  unfold Lebt
  rw [hc, h_old, h_new, List.mem_cons]
  constructor
  · rintro ⟨h0, hlt, hnot⟩
    exact ⟨⟨h0, hlt, fun hj => hnot (Or.inr hj)⟩, fun he => hnot (Or.inl he)⟩
  · rintro ⟨⟨h0, hlt, hnot⟩, hne⟩
    exact ⟨h0, hlt, fun hj => hj.elim hne hnot⟩

/-- Bumping the high-water mark makes exactly its old boundary live. -/
theorem bump_live_iff (A : FreiForm D) {σ σ' : World D} (hok : A.FreiOk σ)
    (hk : A.kopfSt σ' = A.kopfSt σ) (hn : ∀ j, A.naechst σ' j = A.naechst σ j)
    (hc : A.stand σ' = A.stand σ + 1) (j : Int) :
    A.Lebt σ' j ↔ j = A.stand σ ∨ A.Lebt σ j := by
  have he := A.aufListe_gleich hk hn j
  have hnew := (A.lebt_bump hok hk hn hc).2.2
  constructor
  · intro hl
    by_cases hj : j = A.stand σ
    · exact Or.inl hj
    · exact Or.inr ⟨hl.1, by have := hl.2.1; omega, fun hm => hl.2.2 (he.mpr hm)⟩
  · intro h
    rcases h with rfl | h
    · exact hnew
    · exact (A.lebt_bump hok hk hn hc).2.1 j h

/-- Taking the free-list head makes exactly that slot live. -/
theorem take_live_iff (A : FreiForm D) {σ σ' : World D}
    (hne : A.kopfSt σ < D.count A.tab) (hok : A.FreiOk σ)
    (hk : A.kopfSt σ' = A.naechst σ (A.kopfSt σ))
    (hn : ∀ j, A.naechst σ' j = A.naechst σ j)
    (hc : A.stand σ' = A.stand σ) (j : Int) :
    A.Lebt σ' j ↔ j = A.kopfSt σ ∨ A.Lebt σ j := by
  have hr := A.lebt_abheb hne hok hk hn hc
  obtain ⟨L, hL, _, _⟩ := hok
  generalize heq : A.kopfSt σ = k at hL hne hk hr ⊢
  cases hL with
  | nil => exact absurd hne (Int.lt_irrefl _)
  | cons k h0 hlt tail ht =>
    have hnew : A.Kette σ' (A.kopfSt σ') tail := by
      rw [hk]
      exact Kette.uebertragen ht (fun i _ => hn i)
    have hold : A.Kette σ (A.kopfSt σ) (k :: tail) := by
      rw [heq]; exact Kette.cons k h0 hlt tail ht
    have ho := aufListe_iff_mem hold rfl j
    have hp := aufListe_iff_mem hnew rfl j
    constructor
    · intro hl
      by_cases hj : j = k
      · exact Or.inl hj
      · refine Or.inr ⟨hl.1, hc ▸ hl.2.1, ?_⟩
        intro hm
        rcases List.mem_cons.mp (ho.mp hm) with he | hm
        · exact hj he
        · exact hl.2.2 (hp.mpr hm)
    · intro hh
      rcases hh with rfl | hh
      · exact hr.2.2
      · exact hr.2.1 j hh

end FreiForm

namespace ArenaOwnership

theorem State.agrees_reads {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    s.agrees A (σ.lese Λ os) :=
  ⟨ha.1, fun i => (A.lebt_gleich (σ := σ) (σ' := σ.lese Λ os) rfl (fun _ => rfl) rfl i).trans (ha.2 i)⟩

theorem State.move_agrees {s s' : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) (f g : Frame) (h h' : Handle)
    (he : s.move f g h = some (s', h')) : s'.agrees A σ := by
  refine ⟨(State.move_valid ha.1 f g h he).1, ?_⟩
  intro i
  unfold State.move at he
  split at he
  · rename_i hown
    cases he
    by_cases hi : i = h.slot
    · subst i
      constructor
      · intro _; exact ⟨_, State.put_at _ _ _⟩
      · intro _; exact State.owned_live ha hown.1
    · simpa [State.put, hi] using ha.2 i
  · cases he

theorem State.lend_agrees {s s' : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) (f g : Frame) (h : Handle)
    (he : s.lend f g h = some s') : s'.agrees A σ := by
  refine ⟨(State.lend_valid ha.1 f g h he).1, ?_⟩
  unfold State.lend at he
  split at he
  · cases he
  · rename_i c hc
    split at he
    · cases he
      intro i
      by_cases hi : i = h.slot
      · subst i
        have hlive := (ha.2 h.slot).mpr ⟨c, hc⟩
        simp only [hlive, put, ↓reduceIte, Option.some.injEq, exists_eq']
      · simpa [State.put, hi] using ha.2 i
    · cases he

theorem State.endLoan_agrees {s s' : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) (f : Frame) (h : Handle)
    (he : s.endLoan f h = some s') : s'.agrees A σ := by
  refine ⟨State.endLoan_valid ha.1 f h he, ?_⟩
  unfold State.endLoan at he
  split at he
  · cases he
  · rename_i c hc
    split at he
    · cases he
    · split at he
      · cases he
        intro i
        by_cases hi : i = h.slot
        · subst i
          have hlive := (ha.2 h.slot).mpr ⟨c, hc⟩
          simp only [hlive, put, ↓reduceIte, Option.some.injEq, exists_eq']
        · simpa [State.put, hi] using ha.2 i
      · cases he

theorem State.release_agrees {s s' : State} {A : FreiForm D} {σ σ' : World D}
    (ha : s.agrees A σ) (f : Frame) (h : Handle)
    (he : s.release f h = some s')
    (hl : ∀ i, A.Lebt σ' i ↔ A.Lebt σ i ∧ i ≠ h.slot) : s'.agrees A σ' := by
  refine ⟨(State.release_valid ha.1 f h he).1, ?_⟩
  unfold State.release at he
  split at he
  · cases he
    intro i
    rw [hl]
    by_cases hi : i = h.slot
    · subst i; simp only [ne_eq, not_true_eq_false, and_false, put, ↓reduceIte, reduceCtorEq, exists_false]
    · simpa [State.put, hi] using ha.2 i
  · cases he

theorem State.allocate_agrees {s s' : State} {A : FreiForm D} {σ σ' : World D}
    (ha : s.agrees A σ) (f : Frame) (i : Int) (h : Handle)
    (he : s.allocate f i = some (s', h))
    (hl : ∀ j, A.Lebt σ' j ↔ j = i ∨ A.Lebt σ j) : s'.agrees A σ' := by
  refine ⟨(State.allocate_valid ha.1 f i he).1, ?_⟩
  unfold State.allocate at he
  split at he
  · cases he
  · cases he
    intro j
    rw [hl]
    by_cases hj : j = i
    · subst j; simp only [true_or, put, ↓reduceIte, Option.some.injEq, exists_eq']
    · simpa [State.put, hj] using ha.2 j

theorem State.allocate_exists {s : State} {A : FreiForm D} {σ : World D}
    (ha : s.agrees A σ) (f : Frame) (i : Int) (hn : ¬ A.Lebt σ i) :
    ∃ s' h, s.allocate f i = some (s', h) := by
  have hc : s.cells i = none := by
    cases he : s.cells i with
    | none => rfl
    | some c => exact False.elim (hn ((ha.2 i).mpr ⟨c, he⟩))
  simp only [allocate, hc, Option.some.injEq, Prod.mk.injEq, exists_and_left, exists_eq', and_true]

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- The actual release block, for any variable and any continuation, consumes
the right and refines exactly the live cells in G's memory. -/
theorem release_execution (A : FreiForm D) (s : State) (f : Frame) (h : Handle)
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (rest : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (ha : s.agrees A σ) (hf : A.FreiOk σ) (ho : s.owns f h) (hx : (ρ.get x).n = h.slot) :
    ∃ s' σ', s.release f h = some s' ∧
      execBlock O passes R (Block.freiVar A x hwT hLT hwK hLK rest) σ ρ =
        execBlock O passes R rest σ' ρ ∧
      s'.agrees A σ' ∧ A.FreiOk σ' ∧ A.Fremd σ σ' ∧ (∀ g, ¬ s'.access g h) := by
  have hlive := State.owned_live ha ho
  rw [← hx] at hlive
  obtain ⟨σ', he, hk, hn, hother, hc, hframe⟩ :=
    freiVar_ausfuehren O passes R A x hwT hLT hwK hLK rest σ ρ
  have hfree := (A.lebt_frei _ hlive hf hk hn hother hc).1
  have hrelease : s.release f h = some (s.put h.slot none) := by
    simp only [State.release, ho, ↓reduceIte]
  refine ⟨s.put h.slot none, σ', hrelease, he, ?_, hfree, hframe,
    (State.release_valid ha.1 f h hrelease).2⟩
  apply State.release_agrees ha f h hrelease
  intro i
  simpa [hx] using A.release_live_iff (ρ.get x).n hlive hf hk hn hother hc i

/-- Allocation from the used counter creates exactly one fresh ownership
grant, on the world produced by the actual allocation statements. -/
theorem allocate_fresh_execution (A : FreiForm D) (s : State) (f : Frame)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (hroom : A.stand σ < D.count A.tab) :
    ∃ (s' : State) (h : Handle) (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) σ ρ =
        (execBlock O passes R rest σ' (.cons k ρ)).schrumpf ∧
      s.allocate f k.n = some (s', h) ∧ h.slot = k.n ∧
      s'.agrees A σ' ∧ s'.owns f h ∧ A.FreiOk σ' ∧ A.Fremd σ σ' := by
  let k : Wert D (Ty.index (D.count A.tab)) :=
    ⟨A.stand σ, A.stand_nonneg σ, by omega⟩
  obtain ⟨σ', he, hk, hn, hc, hframe⟩ := arenaRumpf_ausfuehren O passes R A v hwT hLT hwG hLG rest
    (σ.lese Λ [Sum.inr A.zaehl]) k ρ
  have hcounter : A.stand σ' = A.stand σ + 1 := hc
  have hhead : A.kopfSt σ' = A.kopfSt σ := hk
  have hlinks : ∀ j, A.naechst σ' j = A.naechst σ j := hn
  have hnot : ¬ A.Lebt σ k.n := by intro hl; have hh := hl.2.1; change A.stand σ < A.stand σ at hh; omega
  obtain ⟨s', h, hs⟩ := State.allocate_exists ha f k.n hnot
  have hslot : h.slot = k.n := by
    unfold State.allocate at hs
    split at hs
    · cases hs
    · cases hs; rfl
  refine ⟨s', h, σ', k, ?_, hs, hslot, ?_, (State.allocate_valid ha.1 f k.n hs).2,
    (A.lebt_bump hf hhead hlinks hcounter).1, hframe⟩
  · rw [arenaAlloc_unter_schranke O passes R A.toArenaForm v hwT hLT hwG hLG voll rest σ ρ hroom]
    rw [he]
  · apply State.allocate_agrees ha f k.n h hs
    intro j
    exact A.bump_live_iff hf hhead hlinks hcounter j

/-- Reusing a free-list slot creates a new incarnation even when its numeric
index is identical to an earlier allocation's index. -/
theorem allocate_reuse_execution (A : FreiForm D) (s : State) (f : Frame)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ)
    (voll : Endblock D V l Γ Λ) (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (hroom : A.kopfSt σ < D.count A.tab) :
    ∃ (s' : State) (h : Handle) (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock O passes R (Block.freiNimm A v hwT hLT hwK hLK voll rest) σ ρ =
        (execBlock O passes R rest σ' (.cons k ρ)).schrumpf ∧
      s.allocate f k.n = some (s', h) ∧ h.slot = k.n ∧
      s'.agrees A σ' ∧ s'.owns f h ∧ A.FreiOk σ' ∧ A.Fremd σ σ' := by
  obtain ⟨σ', k, he, hkn, hk, hn, hc, hframe⟩ :=
    nimmAlloc_fakten O passes R A v hwT hLT hwK hLK voll rest σ ρ hroom
  have hlisted : A.AufListe σ (A.kopfSt σ) := by
    obtain ⟨L, hL, _, _⟩ := hf
    generalize heq : A.kopfSt σ = i at hL hroom ⊢
    cases hL with
    | nil => exact absurd hroom (Int.lt_irrefl _)
    | cons i hi hlt tail ht =>
      exact ⟨i :: tail, by rw [heq]; exact FreiForm.Kette.cons i hi hlt tail ht, List.mem_cons_self⟩
  have hnot : ¬ A.Lebt σ k.n := by
    intro hl
    exact hl.2.2 (hkn ▸ hlisted)
  obtain ⟨s', h, hs⟩ := State.allocate_exists ha f k.n hnot
  have hslot : h.slot = k.n := by
    unfold State.allocate at hs
    split at hs
    · cases hs
    · cases hs; rfl
  refine ⟨s', h, σ', k, he, hs, hslot, ?_, (State.allocate_valid ha.1 f k.n hs).2,
    (A.lebt_abheb hroom hf hk hn hc).1, hframe⟩
  apply State.allocate_agrees ha f k.n h hs
  intro j
  simpa [hkn] using A.take_live_iff hroom hf hk hn hc j

end Execution

#print axioms release_execution
#print axioms allocate_fresh_execution
#print axioms allocate_reuse_execution

end ArenaOwnership
end Gabbro.Grammatik
