import Grammatik.Bausteine.Arena.Ownership.Body.Steps

/-! The executed allocator forms inside the body judgment: allocation from
the free list or the counter binds a new owning origin (or takes its `else`
on a full arena), release consumes one. The world facts are the existing
execution theorems of `World.lean`; nothing about the allocator is assumed. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration} {A : FreiForm D} {fr : Frame} {s0 : State}

/-- A successful allocation binds a new owning origin. -/
theorem Holds.allocate {c : Context} {σ σ' : World D} {Γ : Ctx} {ρ : Env D Γ} {s s' : State} {g : Ghost}
    (hR : Realizes c g A fr s σ ρ) (hc : Complete c g s fr) (hl : s0.local s fr) (hp : s0.progress s)
    (k : Wert D (Ty.index (D.count A.tab))) {h : Handle}
    (hs : s.allocate fr k.n = some (s', h)) (hslot : h.slot = k.n) (ha' : s'.agrees A σ') (hf' : A.FreiOk σ') :
    Holds A fr s0 c.bindFresh σ' (.cons k ρ) :=
  ⟨g.set c.next h, s', allocation_context A c g fr s s' σ σ' ρ k h hR ha' hf' hs hslot,
    Complete.allocate hR.2.2.1 hc hR.1.1 hs hslot, State.local_trans hl (State.allocate_local hs),
    State.progress_trans hp (State.allocate_progress hs)⟩

section Forms

variable {V : Vertrag D} {out : Flow.Output A V.erg} (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **`alloc` from the free list.** -/
theorem allocList_post {k c c1 : Context} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (v : Expr D Γ Λ (D.typ A.tab A.feld)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hk : k.references.length ≤ Γ.length)
    {σ : World D} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (hvoll : ∀ σ', Holds A fr s0 c σ' ρ → EPost A fr s0 out k (execEnd O passes R voll σ' ρ))
    (hrest : ∀ σ' ρ', Holds A fr s0 c.bindFresh σ' ρ' → BPost A fr s0 out k c1 (execBlock O passes R rest σ' ρ')) :
    BPost A fr s0 out k c1.drop (execBlock O passes R (Block.freiNimm A v hwT hLT hwK hLK voll rest) σ ρ) := by
  by_cases hroom : A.kopfSt σ < D.count A.tab
  · obtain ⟨g, s, hR, hc, hl, hp⟩ := h
    obtain ⟨s', hh, σ', kv, he, hs, hslot, ha', _, hf', _⟩ :=
      allocate_reuse_execution O passes R A s fr v hwT hLT hwK hLK voll rest σ ρ hR.1 hR.2.1 hroom
    rw [he]
    exact BPost.schrumpf hk _ (hrest σ' _ (Holds.allocate hR hc hl hp kv hs hslot ha' hf'))
  · rw [nimmAlloc_voll O passes R A v hwT hLT hwK hLK voll rest σ ρ hroom]
    exact EPost.toB _ (hvoll _ (h.reads _ _))

/-- **`alloc` from the used counter.** -/
theorem allocCounter_post {k c c1 : Context} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (v : Expr D Γ Λ (D.typ A.tab A.feld)) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') (hk : k.references.length ≤ Γ.length)
    {σ : World D} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (hvoll : ∀ σ', Holds A fr s0 c σ' ρ → EPost A fr s0 out k (execEnd O passes R voll σ' ρ))
    (hrest : ∀ σ' ρ', Holds A fr s0 c.bindFresh σ' ρ' → BPost A fr s0 out k c1 (execBlock O passes R rest σ' ρ')) :
    BPost A fr s0 out k c1.drop
      (execBlock O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest) σ ρ) := by
  by_cases hroom : A.stand σ < D.count A.tab
  · obtain ⟨g, s, hR, hc, hl, hp⟩ := h
    obtain ⟨s', hh, σ', kv, he, hs, hslot, ha', _, hf', _⟩ :=
      allocate_fresh_execution O passes R A s fr v hwT hLT hwG hLG voll rest σ ρ hR.1 hR.2.1 hroom
    rw [he]
    exact BPost.schrumpf hk _ (hrest σ' _ (Holds.allocate hR hc hl hp kv hs hslot ha' hf'))
  · rw [frischAlloc_voll O passes R A v hwT hLT hwG hLG voll rest σ ρ hroom]
    exact EPost.toB _ (hvoll _ (h.reads _ _))

/-- **`free A[x];`** consumes the owning origin of `x`. -/
theorem release_post {k c c2 c1 : Context} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {i : Nat}
    (x : Var Γ (Ty.index (D.count A.tab))) (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwK : V.gschreibt A.kopf = true) (hLK : gdarf D A.kopf Λ) (rest : Block D V l Γ Λ Λ')
    (hcons : consume c (.var (Λ := Λ) x) = some (c2, i))
    {σ : World D} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (hrest : ∀ σ' ρ', Holds A fr s0 c2 σ' ρ' → BPost A fr s0 out k c1 (execBlock O passes R rest σ' ρ')) :
    BPost A fr s0 out k c1 (execBlock O passes R (Block.freiVar A x hwT hLT hwK hLK rest) σ ρ) := by
  obtain ⟨g, s, ⟨ha, hf, hb, href, hrights⟩, hc, hl, hp⟩ := h
  obtain ⟨hsource, howned, hctx⟩ := consume_facts hcons
  obtain ⟨hh, hg, hown⟩ := hrights.1 i .owned howned
  obtain ⟨other, hg', hvalue⟩ := origin_sound c g ρ href (.var (Λ := Λ) x) i hsource σ σ
  rw [hg] at hg'
  cases hg'
  have hx : (ρ.get x).n = hh.slot := Option.some.inj hvalue
  obtain ⟨s', σ', hrel, he, ha', hf', _, _⟩ := release_execution O passes R A s fr hh x
    hwT hLT hwK hLK rest σ ρ ha hf hown hx
  rw [he]
  apply hrest
  subst hctx
  exact ⟨g, s', ⟨ha', hf', Context.kill_bounded hb i, Context.kill_references href i,
      rights_after_consumption hrights howned hg (fun j hj => State.release_other hrel j hj)⟩,
    Complete.release hc hg hrel, State.local_trans hl (State.release_local hrel),
    State.progress_trans hp (State.release_progress hrel)⟩

end Forms

#print axioms allocList_post
#print axioms release_post

end Gabbro.Grammatik.ArenaOwnership.Body
