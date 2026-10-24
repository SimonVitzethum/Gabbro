import Grammatik.Berechenbarkeit.Storage.GStack.Allocation

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.GStack

open ArenaKette

variable {D : Deklaration} {A : FreiForm D}

namespace Block

/-- Fresh and recycled allocation share this continuation: link the new cell at
the head before the caller continues. This introduces no recursive service. -/
def pushAllocated {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (allocator : Allocator A V l Γ Λ) (L : LinkFeld A) (G : LinkKopf A)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Gabbro.Grammatik.Block D V l Γ Λ Λ' :=
  allocator (.linkPush L G .here hwT hLT hwH hLH rest)

/-- Provider refusal remains explicit even when the next cell could be reused. -/
def tryPush {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (available : Expr D Γ Λ .bool) (failure : Endblock D V l Γ Λ)
    (allocator : Allocator A V l Γ Λ) (L : LinkFeld A) (G : LinkKopf A)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Gabbro.Grammatik.Block D V l Γ Λ Λ' :=
  .allocationAttempt available failure (pushAllocated allocator L G hwT hLT hwH hLH rest)

end Block

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A payload-sensitive G push, composed from the executed allocator and the
executed link stores. Its single proof covers fresh allocation and slot reuse. -/
theorem push_values (allocator : Allocator A V l Γ Λ) (L : LinkFeld A) (G : LinkKopf A)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ) (σ : World D) (ρ : Env D Γ)
    (value : Wert D (D.typ A.tab A.feld)) (values : List (Wert D (D.typ A.tab A.feld))) (slot : Int)
    (hr : Represents L G σ values) (ha : Allocated O passes R A allocator σ ρ value slot) :
    ∃ σ' k,
      (∀ {Λ'} (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.pushAllocated allocator L G hwT hLT hwH hLH rest) σ ρ =
          (execBlock O passes R rest σ' (.cons k ρ)).schrumpf) ∧
      k.n = slot ∧ G.st σ' = slot ∧ Represents L G σ' (value :: values) ∧ A.FreiOk σ' := by
  obtain ⟨σ1, k, halloc, hkn, hframe, hf, hlive, hold, hbytes⟩ := ha
  have hrep : Represents L G σ1 values := hr.frame (G.st_fremd hframe) (L.wert_fremd hframe)
    (fun i hi => (hlive i).mpr (.inr (hr.list_ok.lebt_auf hi))) (by
      intro i hi
      have hne : i ≠ slot := fun he => hold (he ▸ hr.list_ok.lebt_auf hi)
      simpa [hne] using hbytes i)
  have hnot : ¬ Auf (D.count A.tab) (L.wert σ1) (G.st σ1) slot := by
    intro hi
    rw [L.wert_fremd' hframe, G.st_fremd hframe] at hi
    exact hold (hr.list_ok.lebt_auf hi)
  obtain ⟨σ2, hlink, hr2, hf2, hhead, _⟩ :=
    linkPush_values O passes R (l := l) L G .here hwT hLT hwH hLH σ1 (.cons k ρ) values hrep hf
      (by simpa only [Env.get_cons_here, hkn] using (hlive slot).mpr (.inl rfl))
      (by simpa only [Env.get_cons_here, hkn] using hnot)
  have hstored : σ1.slots A.tab k.n A.feld = value := by simpa [hkn] using hbytes slot
  refine ⟨σ2, k, ?_, hkn, ?_, ?_, hf2⟩
  · intro Λ' rest
    unfold Block.pushAllocated
    rw [halloc, hlink]
  · simpa only [Env.get_cons_here, hkn] using hhead
  · simpa only [Env.get_cons_here, hstored] using hr2

theorem tryPush_refused (available : Expr D Γ Λ .bool) (failure : Endblock D V l Γ Λ)
    (allocator : Allocator A V l Γ Λ) (L : LinkFeld A) (G : LinkKopf A)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ)
    {Λ'} (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (he : eval (σ.lese Λ available.orte) available (σ.lese Λ available.orte) ρ = false) :
    execBlock O passes R (Block.tryPush available failure allocator L G hwT hLT hwH hLH rest) σ ρ =
      (execEnd O passes R failure (σ.lese Λ available.orte) ρ).zuAusgang :=
  allocationAttempt_refused O passes R available failure _ σ ρ he

theorem tryPush_values (available : Expr D Γ Λ .bool) (failure : Endblock D V l Γ Λ)
    (allocator : Allocator A V l Γ Λ) (L : LinkFeld A) (G : LinkKopf A)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwH : V.gschreibt G.g = true) (hLH : gdarf D G.g Λ) (σ : World D) (ρ : Env D Γ)
    (value : Wert D (D.typ A.tab A.feld)) (values : List (Wert D (D.typ A.tab A.feld))) (slot : Int)
    (hr : Represents L G σ values)
    (he : eval (σ.lese Λ available.orte) available (σ.lese Λ available.orte) ρ = true)
    (ha : Allocated O passes R A allocator (σ.lese Λ available.orte) ρ value slot) :
    ∃ σ' k,
      (∀ {Λ'} (rest : Gabbro.Grammatik.Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ'),
        execBlock O passes R (Block.tryPush available failure allocator L G hwT hLT hwH hLH rest) σ ρ =
          (execBlock O passes R rest σ' (.cons k ρ)).schrumpf) ∧
      k.n = slot ∧ G.st σ' = slot ∧ Represents L G σ' (value :: values) ∧ A.FreiOk σ' := by
  obtain ⟨σ', k, hpush, hslot, hhead, hrep, hfree⟩ := push_values O passes R allocator L G hwT hLT hwH hLH
    (σ.lese Λ available.orte) ρ value values slot (hr.reads _ _) ha
  refine ⟨σ', k, ?_, hslot, hhead, hrep, hfree⟩
  intro Λ' rest
  unfold Block.tryPush
  rw [allocationAttempt_available O passes R available failure _ σ ρ he, hpush]

end Execution

end Gabbro.Grammatik.Berechenbarkeit.Storage.GStack
