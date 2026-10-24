import Grammatik.Bausteine.Arena.Ownership.Machine.Block

/-! **The allocator forms, one machine step at a time.** Machine G runs the
executed form of `alloc` as a narrowing bind followed by two leaf stores,
and `free` as two leaf stores. The ledger grants a slot exactly at the step
that makes it live (the head taking its link, the counter rising) and
retires it exactly at the step that puts it on the list (the head taking
the slot), so ledger and world agree after every step. Between the steps of
a form the running activation is in a `Head` state that records the
allocator word it relies on. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

section Inv

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- **A narrowing bind is judged** as a plain narrowing, or as the executed `alloc` from the list or the counter. -/
theorem ob_narrow_inv : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c cout : Context}
    {b : Block D V l Γ Λ Λ'}, OB A I out k c b cout →
    ∀ {lo hi lo' hi' : Int} {e : Expr D Γ Λ (.int lo hi)} {sonst : Endblock D V l Γ Λ}
      {rest : Block D V l (.int lo' hi' :: Γ) Λ Λ'}, b = .narrow e lo' hi' sonst rest →
    OE A I out k c sonst ∧
    ((∃ c1, OB A I out k (c.bind (origin c e)) rest c1 ∧ DropW cout c1) ∨
     (∃ (e2 : Expr D (.int lo' hi' :: Γ) Λ (D.gtyp A.kopf)) (hwK : V.gschreibt A.kopf = true)
        (hLK : gdarf D A.kopf Λ) (t : D.Tab) (f : D.Feld t) (i : Expr D (.int lo' hi' :: Γ) Λ (.index (D.count t)))
        (ev : Expr D (.int lo' hi' :: Γ) Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
        (rest' : Block D V l (.int lo' hi' :: Γ) Λ Λ') (c1 : Context),
        rest = .cons (.assignGlob A.kopf e2 hwK hLK) (.cons (.assignSlot t f i ev hw hL) rest') ∧
        exprGlob e = some A.kopf ∧ hi' < D.count A.tab ∧ exprSlotRead e2 = some ⟨A.tab, A.nxt, Γ.length⟩ ∧
        NotLink A t f ∧ checkExpression A c.bindFresh i = true ∧ checkExpression A c.bindFresh ev = true ∧
        storeCheck A c.bindFresh t i = true ∧ OB A I out k c.bindFresh rest' c1 ∧ DropW cout c1) ∨
     (∃ (t : D.Tab) (f : D.Feld t) (i : Expr D (.int lo' hi' :: Γ) Λ (.index (D.count t)))
        (ev : Expr D (.int lo' hi' :: Γ) Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
        (e2 : Expr D (.int lo' hi' :: Γ) Λ (D.gtyp A.zaehl)) (hwG : V.gschreibt A.zaehl = true)
        (hLG : gdarf D A.zaehl Λ) (rest' : Block D V l (.int lo' hi' :: Γ) Λ Λ') (c1 : Context),
        rest = .cons (.assignSlot t f i ev hw hL) (.cons (.assignGlob A.zaehl e2 hwG hLG) rest') ∧
        exprGlob e = some A.zaehl ∧ hi' < D.count A.tab ∧ NotLink A t f ∧ exprSucc e2 = some Γ.length ∧
        checkExpression A c.bindFresh i = true ∧ checkExpression A c.bindFresh ev = true ∧
        storeCheck A c.bindFresh t i = true ∧ OB A I out k c.bindFresh rest' c1 ∧ DropW cout c1))
  | _, _, _, _, _, _, _, _, .narrow e lo' hi' sonst rest he hs hrest => by
    intro heq; cases heq
    exact ⟨hs, Or.inl ⟨_, hrest, Or.inl rfl⟩⟩
  | _, _, _, _, _, _, _, _, .allocList e lo' hi' voll g e2 hwK hLK t f i ev hw hL rest he hhi hg he2 hn hi hev hs
      hvoll hrest => by
    intro heq; cases heq; subst hg
    exact ⟨hvoll, Or.inr (Or.inl ⟨e2, hwK, hLK, t, f, i, ev, hw, hL, rest, _, rfl, he, hhi, he2, hn, hi, hev, hs,
      hrest, Or.inl rfl⟩)⟩
  | _, _, _, _, _, _, _, _, .allocCounter e lo' hi' voll t f i ev hw hL g e2 hwG hLG rest he hhi hn hg he2 hi hev
      hs hvoll hrest => by
    intro heq; cases heq; subst hg
    exact ⟨hvoll, Or.inr (Or.inr ⟨t, f, i, ev, hw, hL, e2, hwG, hLG, rest, _, rfl, he, hhi, hn, he2, hi, hev, hs,
      hrest, Or.inl rfl⟩)⟩
  | _, _, _, _, _, _, _, _, .weaken b hb hw => by
    intro heq
    obtain ⟨hs, alt⟩ := ob_narrow_inv hb heq
    refine ⟨hs, ?_⟩
    rcases alt with ⟨c1, hr, hd⟩ | ⟨e2, hwK, hLK, t, f, i, ev, hw', hL, rest', c1, hreq, he, hhi, he2, hn, hi, hev,
      hst, hr, hd⟩ | ⟨t, f, i, ev, hw', hL, e2, hwG, hLG, rest', c1, hreq, he, hhi, hn, he2, hi, hev, hst, hr, hd⟩
    · exact Or.inl ⟨c1, hr, hd.weaken hw⟩
    · exact Or.inr (Or.inl ⟨e2, hwK, hLK, t, f, i, ev, hw', hL, rest', c1, hreq, he, hhi, he2, hn, hi, hev, hst, hr,
        hd.weaken hw⟩)
    · exact Or.inr (Or.inr ⟨t, f, i, ev, hw', hL, e2, hwG, hLG, rest', c1, hreq, he, hhi, hn, he2, hi, hev, hst, hr,
        hd.weaken hw⟩)
  | _, _, _, _, _, _, _, _, .nil => by intro he; cases he
  | _, _, _, _, _, _, _, _, .cons .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .dead .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .release .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .bind .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .bindCall .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .bindCallInd .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .bindCallElse .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .bindAxiom .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .bindAxiomElse .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .regRead .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .regReadElse .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .awaits .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .exchange .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .check .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .float .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .floatLit .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .floatOf .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .floatNarrow .. => by intro he; cases he

end Inv

section Step

variable {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State}

theorem agrees_reads {σ : World D} (ha : s.agrees A σ) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    s.agrees A (σ.lese Λ os) := State.agrees_meta ha (MetaSame.reads A σ Λ os)

theorem freiOk_reads {σ : World D} (ho : A.FreiOk σ) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    A.FreiOk (σ.lese Λ os) := freiOk_meta ho (MetaSame.reads A σ Λ os)

/-- **A narrowing bind that holds**: a plain binder, or the binder of an executed `alloc` not yet granted. -/
theorem run_narrow {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int} {k c : Context}
    {g : Ghost} {σ : World D} {ρ : Env D Γ} {e : Expr D Γ Λ (.int lo hi)}
    {sonst : Endblock D (vertragVon D f) l Γ Λ} {rest : Block D (vertragVon D f) l (.int lo' hi' :: Γ) Λ Λ'}
    {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.narrow e lo' hi' sonst rest) r))
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    Next A I fr s (σ.lese Λ e.orte) f ⟨l, .int lo' hi' :: Γ, Λ,
      .cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, alt⟩ := ob_narrow_inv hb rfl
  have ha1 := agrees_reads ha Λ e.orte
  have ho1 := freiOk_reads ho Λ e.orte
  have hk1 : k.references.length ≤ (Ty.int lo' hi' :: Γ).length := Nat.le_succ_of_le hk
  rcases alt with ⟨c1, hrest, hd⟩ | ⟨e2, hwK, hLK, t, f', i, ev, hw, hL, rest', c1, hreq, he, hhi, he2, hn, hi, hev,
    hst, hrest, hd⟩ | ⟨t, f', i, ev, hw, hL, e2, hwG, hLG, rest', c1, hreq, he, hhi, hn, he2, hi, hev, hst, hrest, hd⟩
  · exact Next.of_holds (Holds.bindNarrow (hf.holds ha1 ho1) e _ _ lo' hi' h) hk1 (OR.binder hrest hd hk hc)
  · subst hreq
    have hv := exprGlob_eval e he (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ
    rw [intVon_umTyp A.hkopf, intVon_int, Option.some.injEq] at hv
    change _ = A.kopfSt (σ.lese Λ e.orte) at hv
    refine Next.same ha1 ho1 (.list _ ρ e2 hwK hLK _ _ he2 hv ?_ hk hf ?_)
    · have := h.2; rw [hv] at this; omega
    · exact OR.binder (.cons _ _ (.assignSlot t f' i ev hw hL hn hi hev hst) hrest) hd hk hc
  · subst hreq
    have hv := exprGlob_eval e he (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ
    rw [intVon_umTyp A.hz, intVon_int, Option.some.injEq] at hv
    change _ = A.stand (σ.lese Λ e.orte) at hv
    refine Next.same ha1 ho1 (.store _ ρ t f' i ev hw hL hn e2 hwG hLG _ _ he2 hv ?_ hk hf ?_)
    · have := h.2; rw [hv] at this; omega
    · exact OR.binder hrest hd hk hc

/-- **A narrowing bind that fails** runs its `else` branch in front of the continuation. -/
theorem run_narrowElse {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi lo' hi' : Int} {k c : Context}
    {g : Ghost} {σ : World D} {ρ : Env D Γ} {e : Expr D Γ Λ (.int lo hi)}
    {sonst : Endblock D (vertragVon D f) l Γ Λ} {rest : Block D (vertragVon D f) l (.int lo' hi' :: Γ) Λ Λ'}
    {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.narrow e lo' hi' sonst rest) r)) :
    Next A I fr s (σ.lese Λ e.orte) f ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨hs, _⟩ := ob_narrow_inv hb rfl
  exact Next.same (agrees_reads ha Λ e.orte) (freiOk_reads ho Λ e.orte) (.run ρ _ hk hf (OR.sonst hs hc.exits))

end Step

/-! ## Inside the forms -/

section Inside

variable {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat} {fr : Frame} {s : State}

theorem realizes_of {c : Context} {g : Ghost} {σ : World D} {Γ : Ctx} {ρ : Env D Γ} (hf : FrameOk c g s fr ρ)
    (ha : s.agrees A σ) (ho : A.FreiOk σ) : Realizes c g A fr s σ ρ :=
  ⟨ha, ho, hf.1, hf.2.1, hf.2.2.1⟩

/-- **The head takes the link of the binder**: the binder's slot turns live and is granted. -/
theorem list_step {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {lo hi : Int} {k c : Context} {g : Ghost}
    {σ : World D} (x : Wert D (.int lo hi)) (ρ : Env D Γ) (e2 : Expr D (.int lo hi :: Γ) Λ (D.gtyp A.kopf))
    (hw : (vertragVon D f).gschreibt A.kopf = true) (hL : gdarf D A.kopf Λ)
    {b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ1} {r : GRest D (vertragVon D f) l (.int lo hi :: Γ) Λ1}
    (he2 : exprSlotRead e2 = some ⟨A.tab, A.nxt, Γ.length⟩) (hx : x.n = A.kopfSt σ)
    (hlt : A.kopfSt σ < D.count A.tab) (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
    (hr : OR A I (I f).output k c.bindFresh (.dann b r)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    {σ' : World D} {ρ' : Env D (.int lo hi :: Γ)}
    (hstep : execStmt O passes keinRuf (.assignGlob A.kopf e2 hw hL : Stmt D (vertragVon D f) l _ Λ Λ) σ (.cons x ρ) =
      .ok σ' ρ') :
    Next A I fr s σ' f ⟨l, .int lo hi :: Γ, Λ, ρ', .dann b r⟩ := by
  simp only [execStmt] at hstep
  injection hstep with hσ hρ
  subst σ' ρ'
  have hlink := exprSlotRead_eval e2 he2 (σ.lese Λ e2.orte) (σ.lese Λ e2.orte) (.cons x ρ) x.n
    (by simp [Env.unten, intVon])
  rw [intVon_umTyp A.hkopf, intVon_umTyp A.hnxt, Option.some.injEq] at hlink
  generalize hσ2 : (σ.lese Λ e2.orte).schreibGlob A.kopf Λ
    (eval (σ.lese Λ e2.orte) e2 (σ.lese Λ e2.orte) (.cons x ρ)) = σ2
  have hk2 : A.kopfSt σ2 = A.naechst σ (A.kopfSt σ) := by
    rw [← hσ2, FreiForm.kopfSt_schreibGlob_kopf, hlink, ← hx]; rfl
  have hn2 : ∀ j, A.naechst σ2 j = A.naechst σ j := by
    intro j; rw [← hσ2, FreiForm.naechst_schreibGlob]; rfl
  have hs2 : A.stand σ2 = A.stand σ := by
    rw [← hσ2, FreiForm.stand_schreibGlob_kopf]; rfl
  have hnot : ¬ A.Lebt σ x.n := by
    intro hl'
    apply hl'.2.2
    obtain ⟨L, hL', _, _⟩ := ho
    generalize hkk : A.kopfSt σ = kk at hL' hlt
    cases hL' with
    | nil => exact absurd hlt (Int.lt_irrefl _)
    | cons k0 h0 hk1 L1 h1 =>
      refine ⟨kk :: L1, ?_, ?_⟩
      · rw [hkk]; exact FreiForm.Kette.cons kk h0 hk1 L1 h1
      · rw [hx, hkk]; exact List.mem_cons_self
  obtain ⟨s', hh, hs⟩ := State.allocate_exists ha fr x.n hnot
  have htake := A.lebt_abheb hlt ho hk2 hn2 hs2
  have hagree : s'.agrees A σ2 := by
    apply State.allocate_agrees ha fr x.n hh hs
    intro j
    rw [A.take_live_iff hlt ho hk2 hn2 hs2 j, ← hx]
  exact Next.of_holds (Holds.allocateAt (σm := σ) (τ := .int lo hi) (realizes_of hf ha ho) hf.2.2.2
    (State.local_refl s fr) (State.progress_refl s) x x.n hs (allocate_slot hs) (intVon_int x) hagree htake.1)
    (Nat.le_succ_of_le hk) hr

/-- **The counter rises past the binder**: the binder's slot turns live and is granted. -/
theorem counter_step {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {lo hi : Int} {k c : Context}
    {g : Ghost} {σ : World D} (x : Wert D (.int lo hi)) (ρ : Env D Γ)
    (e2 : Expr D (.int lo hi :: Γ) Λ (D.gtyp A.zaehl))
    (hw : (vertragVon D f).gschreibt A.zaehl = true) (hL : gdarf D A.zaehl Λ)
    {b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ1} {r : GRest D (vertragVon D f) l (.int lo hi :: Γ) Λ1}
    (he2 : exprSucc e2 = some Γ.length) (hx : x.n = A.stand σ)
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
    (hr : OR A I (I f).output k c.bindFresh (.dann b r)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    {σ' : World D} {ρ' : Env D (.int lo hi :: Γ)}
    (hstep : execStmt O passes keinRuf (.assignGlob A.zaehl e2 hw hL : Stmt D (vertragVon D f) l _ Λ Λ) σ
      (.cons x ρ) = .ok σ' ρ') :
    Next A I fr s σ' f ⟨l, .int lo hi :: Γ, Λ, ρ', .dann b r⟩ := by
  simp only [execStmt] at hstep
  injection hstep with hσ hρ
  subst σ' ρ'
  have hsucc := exprSucc_eval e2 he2 (σ.lese Λ e2.orte) (σ.lese Λ e2.orte) (.cons x ρ) x.n
    (by simp [Env.unten, intVon])
  rw [intVon_umTyp A.hz, Option.some.injEq] at hsucc
  generalize hσ2 : (σ.lese Λ e2.orte).schreibGlob A.zaehl Λ
    (eval (σ.lese Λ e2.orte) e2 (σ.lese Λ e2.orte) (.cons x ρ)) = σ2
  have hstand : A.stand σ2 = A.stand σ + 1 := by
    rw [← hσ2, ArenaForm.stand_schreibGlob, hsucc, hx]
  have hkopf : A.kopfSt σ2 = A.kopfSt σ := by
    rw [← hσ2, FreiForm.kopfSt_schreibGlob_zaehl]; rfl
  have hlinks : ∀ j, A.naechst σ2 j = A.naechst σ j := by
    intro j; rw [← hσ2, FreiForm.naechst_schreibGlob]; rfl
  have hnot : ¬ A.Lebt σ x.n := by
    intro hl'; have := hl'.2.1; rw [hx] at this; omega
  obtain ⟨s', hh, hs⟩ := State.allocate_exists ha fr x.n hnot
  have hbump := A.lebt_bump ho hkopf hlinks hstand
  have hagree : s'.agrees A σ2 := by
    apply State.allocate_agrees ha fr x.n hh hs
    intro j
    rw [A.bump_live_iff ho hkopf hlinks hstand j, ← hx]
  exact Next.of_holds (Holds.allocateAt (σm := σ) (τ := .int lo hi) (realizes_of hf ha ho) hf.2.2.2
    (State.local_refl s fr) (State.progress_refl s) x x.n hs (allocate_slot hs) (intVon_int x) hagree hbump.1)
    (Nat.le_succ_of_le hk) hr

/-- **The payload store before the counter rises** keeps the allocator words. -/
theorem store_step {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {lo hi : Int} {k c : Context}
    {g : Ghost} {σ : World D} (x : Wert D (.int lo hi)) (ρ : Env D Γ)
    (t : D.Tab) (f' : D.Feld t) (i : Expr D (.int lo hi :: Γ) Λ (.index (D.count t)))
    (ev : Expr D (.int lo hi :: Γ) Λ (D.typ t f')) (hws : (vertragVon D f).schreibt t = true)
    (hLs : darf D t Λ) (hn : NotLink A t f')
    (e2 : Expr D (.int lo hi :: Γ) Λ (D.gtyp A.zaehl)) (hw : (vertragVon D f).gschreibt A.zaehl = true)
    (hL : gdarf D A.zaehl Λ) (b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ1)
    (r : GRest D (vertragVon D f) l (.int lo hi :: Γ) Λ1)
    (he2 : exprSucc e2 = some Γ.length) (hx : x.n = A.stand σ)
    (hlt : A.stand σ < D.count A.tab) (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
    (hr : OR A I (I f).output k c.bindFresh (.dann b r)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    {σ' : World D} {ρ' : Env D (.int lo hi :: Γ)}
    (hstep : execStmt O passes keinRuf (.assignSlot t f' i ev hws hLs : Stmt D (vertragVon D f) l _ Λ Λ) σ
      (.cons x ρ) = .ok σ' ρ') :
    Next A I fr s σ' f ⟨l, .int lo hi :: Γ, Λ, ρ', .dann (.cons (.assignGlob A.zaehl e2 hw hL) b) r⟩ := by
  simp only [execStmt] at hstep
  injection hstep with hσ hρ
  subst σ' ρ'
  have hm := (MetaSame.reads A σ Λ (i.orte ++ ev.orte)).trans
    (MetaSame.writeSlot A (σ.lese Λ (i.orte ++ ev.orte)) t Λ
      (eval (σ.lese Λ (i.orte ++ ev.orte)) i (σ.lese Λ (i.orte ++ ev.orte)) (.cons x ρ)).n f'
      (eval (σ.lese Λ (i.orte ++ ev.orte)) ev (σ.lese Λ (i.orte ++ ev.orte)) (.cons x ρ)) hn)
  exact Next.same (State.agrees_meta ha hm) (freiOk_meta ho hm)
    (.counter x ρ e2 hw hL b r he2 (by rw [hm.2.2]; exact hx) (by rw [hm.2.2]; exact hlt) hk hf hr)

/-- **The head takes the slot of `free`**: the slot goes on the list and its grant is retired. -/
theorem release_step {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {k c : Context} {g : Ghost}
    {σ : World D} (ρ : Env D Γ) (e2 : Expr D Γ Λ (D.gtyp A.kopf))
    (hw : (vertragVon D f).gschreibt A.kopf = true) (hL : gdarf D A.kopf Λ)
    (b : Block D (vertragVon D f) l Γ Λ Λ1) (r : GRest D (vertragVon D f) l Γ Λ1) (p o : Nat) (h : Handle)
    (he2 : exprVarPos e2 = some p) (hp : ρ.unten p = some h.slot) (hown : c.rights o = some .owned)
    (hg : g o = some h) (hlink : A.naechst σ h.slot = A.kopfSt σ)
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
    (hr : OR A I (I f).output k (c.kill o) (.dann b r)) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    {σ' : World D} {ρ' : Env D Γ}
    (hstep : execStmt O passes keinRuf (.assignGlob A.kopf e2 hw hL : Stmt D (vertragVon D f) l _ Λ Λ) σ ρ =
      .ok σ' ρ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ', .dann b r⟩ := by
  simp only [execStmt] at hstep
  injection hstep with hσ hρ
  subst σ' ρ'
  have hhead : (Wert.umTyp A.hkopf (eval (σ.lese Λ e2.orte) e2 (σ.lese Λ e2.orte) ρ)).n = h.slot := by
    have := exprVarPos_eval e2 he2 (σ.lese Λ e2.orte) (σ.lese Λ e2.orte) ρ
    rw [intVon_umTyp A.hkopf, hp, Option.some.injEq] at this
    exact this
  generalize hσ3 : (σ.lese Λ e2.orte).schreibGlob A.kopf Λ (eval (σ.lese Λ e2.orte) e2 (σ.lese Λ e2.orte) ρ) = σ3
  have hk3 : A.kopfSt σ3 = h.slot := by rw [← hσ3, FreiForm.kopfSt_schreibGlob_kopf, hhead]
  have hn3 : ∀ j, A.naechst σ3 j = A.naechst σ j := by intro j; rw [← hσ3, FreiForm.naechst_schreibGlob]; rfl
  have hs3 : A.stand σ3 = A.stand σ := by rw [← hσ3, FreiForm.stand_schreibGlob_kopf]; rfl
  obtain ⟨h', hg', howns⟩ := hf.2.2.1.1 o .owned hown
  rw [hg] at hg'; cases hg'
  have hlive : A.Lebt σ h.slot := State.owned_live ha howns
  have hl3 : A.naechst σ3 h.slot = A.kopfSt σ := by rw [hn3, hlink]
  have hfree := A.lebt_frei h.slot hlive ho hk3 hl3 (fun j _ => hn3 j) hs3
  have howns' : s.owns fr h := howns
  have hrel : s.release fr h = some (s.put h.slot none) := by simp [State.release, howns']
  refine ⟨s.put h.slot none, State.release_local hrel, State.release_progress hrel, ?_, hfree.1, ?_⟩
  · exact State.release_agrees ha fr h hrel
      (fun j => A.release_live_iff h.slot hlive ho hk3 hl3 (fun j' _ => hn3 j') hs3 j)
  · exact .run ρ _ hk ⟨Context.kill_bounded hf.1 o, Context.kill_references hf.2.1 o,
      rights_after_consumption hf.2.2.1 hown hg (fun j hj => State.release_other hrel j hj),
      Complete.release hf.2.2.2 hg hrel⟩ hr

end Inside

end Gabbro.Grammatik.ArenaOwnership.Machine
