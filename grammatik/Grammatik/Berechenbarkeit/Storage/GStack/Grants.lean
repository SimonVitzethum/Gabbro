import Grammatik.Berechenbarkeit.Storage.GStack.Push

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaOwnership

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {l : Bool}
variable {Γ : Ctx} {Λ : List (Res D)}

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- The actual push prefix issues exactly one fresh incarnation/grant using
the existing ownership ledger. Linking allocates no further rights. -/
theorem push_owned (allocator : Allocator A V l Γ Λ) (L : LinkFeld A) (G : LinkKopf A)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ) (σ : World D) (ρ : Env D Γ)
    (value : Wert D (D.typ A.tab A.feld)) (values : List (Wert D (D.typ A.tab A.feld))) (slot : Int)
    (s : State) (frame : Frame) (ha : s.agrees A σ)
    (hr : Represents L G σ values) (halloc : Allocated O passes R A allocator σ ρ value slot) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))) (s' : State) (h : Handle),
      (∀ {Λ'} (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.pushAllocated allocator L G hwT hLT hwH hLH rest) σ ρ =
          (execBlock O passes R rest σ' (.cons k ρ)).schrumpf) ∧
      k.n = slot ∧ h.slot = slot ∧ s.allocate frame slot = some (s', h) ∧
      s'.agrees A σ' ∧ s'.owns frame h ∧ G.st σ' = slot ∧
      Represents L G σ' (value :: values) ∧ A.FreiOk σ' := by
  obtain ⟨σout, kout, hpush, hslot, hhead, hrep, hfree⟩ :=
    push_values O passes R allocator L G hwT hLT hwH hLH σ ρ value values slot hr halloc
  obtain ⟨σ1, k, hp, hk, hframe, hf, hlive, hnot, hbytes⟩ := halloc
  obtain ⟨s', h, hs⟩ := State.allocate_exists ha frame slot hnot
  have hhandle : h.slot = slot := by
    unfold State.allocate at hs
    split at hs
    · cases hs
    · cases hs; rfl
  have hag : s'.agrees A σ1 := State.allocate_agrees ha frame slot h hs hlive
  obtain ⟨σ2, hlink, _, _, _, _, hfreeLink, hnext, hcount⟩ :=
    linkPush_ausfuehren O passes R (l := l) L G .here hwT hLT hwH hLH .nil σ1 (.cons k ρ)
  have hworld : σ2 = σout := by
    have he := hpush .nil
    unfold Block.pushAllocated at he
    rw [hp, hlink] at he
    change (Ausgang.ok σ2 ρ : Ausgang V l Γ) = .ok σout ρ at he
    cases he; rfl
  subst σ2
  exact ⟨σout, kout, s', h, hpush, hslot, hhandle, hs,
    linkPush_grants hag (A.lebt_gleich hfreeLink hnext hcount),
    (State.allocate_valid ha.1 frame slot hs).2, hhead, hrep, hfree⟩

/-- Pop saves the payload, releases the current owning grant, and invalidates
every alias of that slot. Unrelated cells retain their ledger entries. -/
theorem pop_owned (L : LinkFeld A) (G : LinkKopf A)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (empty : Endblock D V l Γ Λ) {Λ'}
    (rest : Gabbro.Grammatik.Block D V l (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (value : Wert D (D.typ A.tab A.feld)) (values : List (Wert D (D.typ A.tab A.feld)))
    (s : State) (frame : Frame) (h : Handle) (ha : s.agrees A σ) (ho : s.owns frame h)
    (hh : h.slot = G.st σ) (hr : Represents L G σ (value :: values)) (hf : A.FreiOk σ) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))) (s' : State),
      execBlock O passes R (Block.popAndRelease L G hwH hLH hwT hLT hwF hLF empty rest) σ ρ =
        (execBlock O passes R rest σ' (.cons value (.cons k ρ))).schrumpf.schrumpf ∧
      k.n = h.slot ∧ s.release frame h = some s' ∧ s'.agrees A σ' ∧
      Represents L G σ' values ∧ A.FreiOk σ' ∧
      (∀ old : Handle, old.slot = h.slot → ∀ f, ¬ s'.access f old) ∧
      (∀ i, i ≠ h.slot → s'.cells i = s.cells i) := by
  obtain ⟨σ', k, he, hk, hr', hf', hdead, hlive⟩ :=
    popAndRelease_values O passes R L G hwH hLH hwT hLT hwF hLF empty rest σ ρ value values hr hf
  have hrelease : s.release frame h = some (s.put h.slot none) := by simp only [State.release, ho, ↓reduceIte]
  have hslot : k.n = h.slot := hk.trans hh.symm
  refine ⟨σ', k, s.put h.slot none, he, hslot, hrelease, ?_, hr', hf', ?_, ?_⟩
  · apply State.release_agrees ha frame h hrelease
    intro i
    simpa only [hslot] using hlive i
  · intro old hold f
    exact State.release_excludes_slot hrelease hold f
  · intro i hi
    exact State.release_other hrelease i hi

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
