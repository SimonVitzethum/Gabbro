import Grammatik.Bausteine.Arena.Ownership.Body.Steps

/-! The executed allocator forms inside the body judgment, recognised on the
actual statements: allocation from the free list or the counter binds a new
owning origin (or takes its `else` on a full arena), release consumes one.
The world facts come from what the recognised expressions evaluate to;
nothing about the allocator is assumed. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration} {A : FreiForm D} {fr : Frame} {s0 : State}

/-- A new owning binder of any integer type naming the granted slot. -/
theorem owning_binder (c : Context) (g : Ghost) {Γ : Ctx} (s' : State) (σ' : World D) (ρ : Env D Γ)
    {τ : Ty} (k : Wert D τ) (fresh : Handle)
    (hb : c.bounded) (href : References c g ρ) (ha' : s'.agrees A σ') (hf' : A.FreiOk σ')
    (hr : Rights c.bindFresh (g.set c.next fresh) s' fr) (hslot : intVon τ k = some fresh.slot) :
    Realizes c.bindFresh (g.set c.next fresh) A fr s' σ' (.cons k ρ) := by
  refine ⟨ha', hf', Context.bindFresh_bounded hb, ?_, hr⟩
  have href' := References.setFresh hb href fresh
  change References (c.bind (some c.next)) (g.set c.next fresh) (.cons k ρ)
  apply References.bind href' k (some c.next)
  intro i hi
  cases hi
  exact ⟨fresh, Ghost.set_at g c.next fresh, hslot⟩

/-- **A successful allocation at a world that keeps every right binds a new owning origin.** `σm` is the world
    the ledger agreed with before the slot became live. -/
theorem Holds.allocateAt {c : Context} {σm σ' : World D} {Γ : Ctx} {ρ : Env D Γ} {s s' : State} {g : Ghost}
    (hR : Realizes c g A fr s σm ρ) (hc : Complete c g s fr) (hl : s0.local s fr) (hp : s0.progress s)
    {τ : Ty} (k : Wert D τ) (slot : Int) {h : Handle}
    (hs : s.allocate fr slot = some (s', h)) (hslot : h.slot = slot) (hk : intVon τ k = some slot)
    (ha' : s'.agrees A σ') (hf' : A.FreiOk σ') :
    Holds A fr s0 c.bindFresh σ' (.cons k ρ) :=
  ⟨g.set c.next h, s',
    owning_binder c g s' σ' ρ k h hR.2.2.1 hR.2.2.2.1 ha' hf' (allocation_rights hR.1 hR.2.2.2.2 hs hslot)
      (hslot ▸ hk),
    Complete.allocate hR.2.2.1 hc hR.1.1 hs hslot, State.local_trans hl (State.allocate_local hs),
    State.progress_trans hp (State.allocate_progress hs)⟩

theorem allocate_slot {s s' : State} {i : Int} {h : Handle} (hs : s.allocate fr i = some (s', h)) :
    h.slot = i := by
  unfold State.allocate at hs
  split at hs
  · cases hs
  · cases hs; rfl

theorem unten_head {Γ : Ctx} {τ : Ty} (v : Wert D τ) (ρ : Env D Γ) :
    (Env.cons v ρ).unten Γ.length = intVon τ v := by
  simp only [Env.unten, ↓reduceIte]

theorem intVon_int {lo hi : Int} (z : Wert D (.int lo hi)) : intVon (.int lo hi) z = some z.n := rfl

section Forms

variable {V : Vertrag D} {out : Flow.Output A V.erg} (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **`alloc` from the used counter, as executed.** -/
theorem allocCounter_post {k c c1 : Context} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (voll : Endblock D V l Γ Λ)
    (t : D.Tab) (f : D.Feld t) (i : Expr D (.int lo' hi' :: Γ) Λ (.index (D.count t)))
    (ev : Expr D (.int lo' hi' :: Γ) Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (g : D.Glob) (e2 : Expr D (.int lo' hi' :: Γ) Λ (D.gtyp g)) (hwG : V.gschreibt g = true) (hLG : gdarf D g Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (he : exprGlob e = some A.zaehl) (hhi : hi' < D.count A.tab) (hn : NotLink A t f) (hg : g = A.zaehl)
    (he2 : exprSucc e2 = some Γ.length) (hk : k.references.length ≤ Γ.length)
    {σ : World D} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (hvoll : ∀ σ', Holds A fr s0 c σ' ρ → EPost A fr s0 out k (execEnd O passes R voll σ' ρ))
    (hrest : ∀ σ' ρ', Holds A fr s0 c.bindFresh σ' ρ' → BPost A fr s0 out k c1 (execBlock O passes R rest σ' ρ')) :
    BPost A fr s0 out k c1.drop (execBlock O passes R
      (.narrow e lo' hi' voll (.cons (.assignSlot t f i ev hw hL) (.cons (.assignGlob g e2 hwG hLG) rest))) σ ρ) := by
  subst hg
  simp only [execBlock]
  split
  · rename_i hrange
    simp only [execBlock, execStmt]
    apply BPost.schrumpf hk
    apply hrest
    obtain ⟨gh, s, hR, hc, hl, hp⟩ := h
    -- the binder is the counter
    have hv := exprGlob_eval e he (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ
    rw [intVon_umTyp A.hz, intVon_int, Option.some.injEq] at hv
    change _ = A.stand (σ.lese Λ e.orte) at hv
    rw [ArenaForm.stand_lese] at hv
    generalize hkv : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hrange.1, hrange.2⟩ :
      Wert D (.int lo' hi')) = kv
    have hkn : kv.n = A.stand σ := by rw [← hkv]; exact hv
    -- the store keeps liveness; the bump makes exactly the counter live
    generalize hσ2 : ((σ.lese Λ e.orte).lese Λ (i.orte ++ ev.orte)).schreibSlot t Λ
      (eval ((σ.lese Λ e.orte).lese Λ (i.orte ++ ev.orte)) i ((σ.lese Λ e.orte).lese Λ (i.orte ++ ev.orte))
        (.cons kv ρ)).n f
      (eval ((σ.lese Λ e.orte).lese Λ (i.orte ++ ev.orte)) ev ((σ.lese Λ e.orte).lese Λ (i.orte ++ ev.orte))
        (.cons kv ρ)) = σ2
    have hm2 : MetaSame A σ σ2 := by
      rw [← hσ2]
      exact ((MetaSame.reads A σ Λ _).trans (MetaSame.reads A _ Λ _)).trans (MetaSame.writeSlot A _ t Λ _ f _ hn)
    have hsucc := exprSucc_eval e2 he2 (σ2.lese Λ e2.orte) (σ2.lese Λ e2.orte) (.cons kv ρ) kv.n
      (by simp only [Env.unten, ↓reduceIte, intVon])
    rw [intVon_umTyp A.hz, Option.some.injEq] at hsucc
    have hstand : A.stand ((σ2.lese Λ e2.orte).schreibGlob A.zaehl Λ
        (eval (σ2.lese Λ e2.orte) e2 (σ2.lese Λ e2.orte) (.cons kv ρ))) = A.stand σ2 + 1 := by
      rw [ArenaForm.stand_schreibGlob, hsucc, hkn, hm2.2.2]
    have hkopf : A.kopfSt ((σ2.lese Λ e2.orte).schreibGlob A.zaehl Λ
        (eval (σ2.lese Λ e2.orte) e2 (σ2.lese Λ e2.orte) (.cons kv ρ))) = A.kopfSt σ2 := by
      rw [FreiForm.kopfSt_schreibGlob_zaehl]; rfl
    have hlinks : ∀ j, A.naechst ((σ2.lese Λ e2.orte).schreibGlob A.zaehl Λ
        (eval (σ2.lese Λ e2.orte) e2 (σ2.lese Λ e2.orte) (.cons kv ρ))) j = A.naechst σ2 j := by
      intro j; rw [FreiForm.naechst_schreibGlob]; rfl
    have hf2 := freiOk_meta hR.2.1 hm2
    have ha2 := State.agrees_meta hR.1 hm2
    have hnot : ¬ A.Lebt σ2 kv.n := by
      intro hl'; have := hl'.2.1; rw [hm2.2.2, hkn] at this; omega
    obtain ⟨s', hh, hs⟩ := State.allocate_exists ha2 fr kv.n hnot
    have hbump := A.lebt_bump hf2 hkopf hlinks hstand
    refine Holds.allocateAt (σm := σ) (τ := .int lo' hi') hR hc hl hp kv kv.n hs (allocate_slot hs) (intVon_int kv) ?_ hbump.1
    apply State.allocate_agrees ha2 fr kv.n hh hs
    intro j
    rw [A.bump_live_iff hf2 hkopf hlinks hstand j, hm2.2.2, ← hkn]
  · exact EPost.toB _ (hvoll _ (h.reads _ _))

/-- **`alloc` from the free list, as executed.** -/
theorem allocList_post {k c c1 : Context} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (voll : Endblock D V l Γ Λ)
    (g : D.Glob) (e2 : Expr D (.int lo' hi' :: Γ) Λ (D.gtyp g)) (hwK : V.gschreibt g = true) (hLK : gdarf D g Λ)
    (t : D.Tab) (f : D.Feld t) (i : Expr D (.int lo' hi' :: Γ) Λ (.index (D.count t)))
    (ev : Expr D (.int lo' hi' :: Γ) Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (he : exprGlob e = some A.kopf) (hhi : hi' < D.count A.tab) (hg : g = A.kopf)
    (he2 : exprSlotRead e2 = some ⟨A.tab, A.nxt, Γ.length⟩) (hn : NotLink A t f)
    (hk : k.references.length ≤ Γ.length)
    {σ : World D} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (hvoll : ∀ σ', Holds A fr s0 c σ' ρ → EPost A fr s0 out k (execEnd O passes R voll σ' ρ))
    (hrest : ∀ σ' ρ', Holds A fr s0 c.bindFresh σ' ρ' → BPost A fr s0 out k c1 (execBlock O passes R rest σ' ρ')) :
    BPost A fr s0 out k c1.drop (execBlock O passes R
      (.narrow e lo' hi' voll (.cons (.assignGlob g e2 hwK hLK) (.cons (.assignSlot t f i ev hw hL) rest))) σ ρ) := by
  subst hg
  simp only [execBlock]
  split
  · rename_i hrange
    simp only [execBlock, execStmt]
    apply BPost.schrumpf hk
    apply hrest
    obtain ⟨gh, s, hR, hc, hl, hp⟩ := h
    have hv := exprGlob_eval e he (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ
    rw [intVon_umTyp A.hkopf, intVon_int, Option.some.injEq] at hv
    change _ = A.kopfSt (σ.lese Λ e.orte) at hv
    rw [FreiForm.kopfSt_lese] at hv
    generalize hkv : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hrange.1, hrange.2⟩ :
      Wert D (.int lo' hi')) = kv
    have hkn : kv.n = A.kopfSt σ := by rw [← hkv]; exact hv
    have hne : A.kopfSt σ < D.count A.tab := by
      have := hrange.2; rw [hv] at this; omega
    -- the head takes the link of the binder
    have hlink := exprSlotRead_eval e2 he2 ((σ.lese Λ e.orte).lese Λ e2.orte) ((σ.lese Λ e.orte).lese Λ e2.orte)
      (.cons kv ρ) kv.n (by simp only [Env.unten, ↓reduceIte, intVon])
    rw [intVon_umTyp A.hkopf, intVon_umTyp A.hnxt, Option.some.injEq] at hlink
    generalize hσ2 : ((σ.lese Λ e.orte).lese Λ e2.orte).schreibGlob A.kopf Λ
      (eval ((σ.lese Λ e.orte).lese Λ e2.orte) e2 ((σ.lese Λ e.orte).lese Λ e2.orte) (.cons kv ρ)) = σ2
    have hk2 : A.kopfSt σ2 = A.naechst σ (A.kopfSt σ) := by
      rw [← hσ2, FreiForm.kopfSt_schreibGlob_kopf, hlink, ← hkn]; rfl
    have hn2 : ∀ j, A.naechst σ2 j = A.naechst σ j := by
      intro j; rw [← hσ2, FreiForm.naechst_schreibGlob]; rfl
    have hs2 : A.stand σ2 = A.stand σ := by
      rw [← hσ2, FreiForm.stand_schreibGlob_kopf]; rfl
    -- then a store that is no link
    have hm3 : MetaSame A σ2 ((σ2.lese Λ (i.orte ++ ev.orte)).schreibSlot t Λ
        (eval (σ2.lese Λ (i.orte ++ ev.orte)) i (σ2.lese Λ (i.orte ++ ev.orte)) (.cons kv ρ)).n f
        (eval (σ2.lese Λ (i.orte ++ ev.orte)) ev (σ2.lese Λ (i.orte ++ ev.orte)) (.cons kv ρ))) :=
      (MetaSame.reads A σ2 Λ _).trans (MetaSame.writeSlot A _ t Λ _ f _ hn)
    have hnot : ¬ A.Lebt σ kv.n := by
      intro hl'
      apply hl'.2.2
      obtain ⟨L, hL', _, _⟩ := hR.2.1
      generalize hkk : A.kopfSt σ = kk at hL' hne
      cases hL' with
      | nil => exact absurd hne (Int.lt_irrefl _)
      | cons k0 h0 hk1 L1 h1 =>
        refine ⟨kk :: L1, ?_, ?_⟩
        · rw [hkk]; exact FreiForm.Kette.cons kk h0 hk1 L1 h1
        · rw [hkn, hkk]; exact List.mem_cons_self
    obtain ⟨s', hh, hs⟩ := State.allocate_exists hR.1 fr kv.n hnot
    have htake := A.lebt_abheb hne hR.2.1 hk2 hn2 hs2
    refine Holds.allocateAt (σm := σ) (τ := .int lo' hi') hR hc hl hp kv kv.n hs (allocate_slot hs) (intVon_int kv) ?_
      (freiOk_meta htake.1 hm3)
    apply State.agrees_meta _ hm3
    apply State.allocate_agrees hR.1 fr kv.n hh hs
    intro j
    rw [A.take_live_iff hne hR.2.1 hk2 hn2 hs2 j, ← hkn]
  · exact EPost.toB _ (hvoll _ (h.reads _ _))

/-- **`free A[x];` as executed** consumes the owning origin of `x`. -/
theorem release_post {k c c2 c1 : Context} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {o p : Nat}
    (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g)) (hwK : V.gschreibt g = true) (hLK : gdarf D g Λ)
    (rest : Block D V l Γ Λ Λ')
    (ht : t = A.tab) (hf : ht ▸ f = A.nxt) (hip : exprVarPos i = some p) (he : exprGlob e = some A.kopf)
    (hg : g = A.kopf) (he2 : exprVarPos e2 = some p) (hcons : consume c i = some (c2, o))
    {σ : World D} {ρ : Env D Γ} (h : Holds A fr s0 c σ ρ)
    (hrest : ∀ σ' ρ', Holds A fr s0 c2 σ' ρ' → BPost A fr s0 out k c1 (execBlock O passes R rest σ' ρ')) :
    BPost A fr s0 out k c1
      (execBlock O passes R (.cons (.assignSlot t f i e hw hL) (.cons (.assignGlob g e2 hwK hLK) rest)) σ ρ) := by
  subst ht hg
  cases hf
  simp only [execBlock, execStmt]
  apply hrest
  obtain ⟨gh, s, ⟨ha, hfo, hb, hrefs, hrights⟩, hc, hl, hp⟩ := h
  obtain ⟨hsource, howned, hctx⟩ := consume_facts hcons
  obtain ⟨hh, hgh, hown⟩ := hrights.1 o .owned howned
  -- the value of `x` is the owned slot
  have hx : ∀ σa σb, intVon _ (eval σa i σb ρ) = some hh.slot := by
    intro σa σb
    obtain ⟨other, hg', hvalue⟩ := origin_sound c gh ρ hrefs i o hsource σa σb
    rw [hgh] at hg'; cases hg'; exact hvalue
  have hpx : ρ.unten p = some hh.slot := by rw [← exprVarPos_eval i hip σ σ ρ]; exact hx σ σ
  -- the link of `x` takes the head
  generalize hσ1 : σ.lese Λ (i.orte ++ e.orte) = σ1
  have hi1 : (eval σ1 i σ1 ρ).n = hh.slot := by
    have := hx σ1 σ1; simp only [intVon, Option.some.injEq] at this; exact this
  have hlink : (Wert.umTyp A.hnxt (eval σ1 e σ1 ρ)).n = A.kopfSt σ := by
    have := exprGlob_eval e he σ1 σ1 ρ
    rw [intVon_umTyp A.hnxt, intVon_umTyp A.hkopf, Option.some.injEq] at this
    rw [this, ← hσ1]; rfl
  generalize hσ2 : σ1.schreibSlot A.tab Λ (eval σ1 i σ1 ρ).n A.nxt (eval σ1 e σ1 ρ) = σ2
  have hk2 : A.kopfSt σ2 = A.kopfSt σ := by rw [← hσ2, FreiForm.kopfSt_schreibSlot, ← hσ1]; rfl
  have hs2 : A.stand σ2 = A.stand σ := by rw [← hσ2, ArenaForm.stand_schreibSlot, ← hσ1]; rfl
  have hn2 : ∀ j, A.naechst σ2 j = if j = hh.slot then A.kopfSt σ else A.naechst σ j := by
    intro j; rw [← hσ2, FreiForm.naechst_schreibSlot, hi1, hlink, ← hσ1]; rfl
  -- the head becomes `x`
  have hhead : (Wert.umTyp A.hkopf (eval (σ2.lese Λ e2.orte) e2 (σ2.lese Λ e2.orte) ρ)).n = hh.slot := by
    have := exprVarPos_eval e2 he2 (σ2.lese Λ e2.orte) (σ2.lese Λ e2.orte) ρ
    rw [intVon_umTyp A.hkopf, hpx, Option.some.injEq] at this
    exact this
  generalize hσ3 : (σ2.lese Λ e2.orte).schreibGlob A.kopf Λ (eval (σ2.lese Λ e2.orte) e2 (σ2.lese Λ e2.orte) ρ) = σ3
  have hk3 : A.kopfSt σ3 = hh.slot := by rw [← hσ3, FreiForm.kopfSt_schreibGlob_kopf, hhead]
  have hn3 : ∀ j, A.naechst σ3 j = A.naechst σ2 j := by intro j; rw [← hσ3, FreiForm.naechst_schreibGlob]; rfl
  have hs3 : A.stand σ3 = A.stand σ := by rw [← hσ3, FreiForm.stand_schreibGlob_kopf, ← hs2]; rfl
  have hlive : A.Lebt σ hh.slot := State.owned_live ha hown
  have hfree := A.lebt_frei hh.slot hlive hfo hk3 (by rw [hn3, hn2]; simp only [↓reduceIte])
    (fun j hj => by rw [hn3, hn2]; simp only [hj, ↓reduceIte]) hs3
  have hown' : s.owns fr hh := hown
  have hrel : s.release fr hh = some (s.put hh.slot none) := by simp only [State.release, hown', ↓reduceIte]
  subst hctx
  refine ⟨gh, s.put hh.slot none, ⟨?_, hfree.1, Context.kill_bounded hb o, Context.kill_references hrefs o,
      rights_after_consumption hrights howned hgh (fun j hj => State.release_other hrel j hj)⟩,
    Complete.release hc hgh hrel, State.local_trans hl (State.release_local hrel),
    State.progress_trans hp (State.release_progress hrel)⟩
  apply State.release_agrees ha fr hh hrel
  intro j
  exact A.release_live_iff hh.slot hlive hfo hk3 (by rw [hn3, hn2]; simp only [↓reduceIte])
    (fun j' hj => by rw [hn3, hn2]; simp only [hj, ↓reduceIte]) hs3 j

end Forms

#print axioms allocCounter_post
#print axioms allocList_post
#print axioms release_post

end Gabbro.Grammatik.ArenaOwnership.Body
