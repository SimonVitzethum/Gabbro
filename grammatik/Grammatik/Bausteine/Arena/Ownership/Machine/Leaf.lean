module
public import Grammatik.Bausteine.Arena.Ownership.Machine.LeafBasis
public import Grammatik.Bausteine.Arena.Ownership.Machine.Head
public import Grammatik.Bausteine.Arena.Ownership.Body.Sound
@[expose] public section


/-! **A leaf step of the running activation.** Machine G executes a leaf
statement at the head of the running residue in one step, through the same
evaluator as the body judgment (`execStmt`, with no call handler). The
judgment's soundness, started at the current ledger, gives the next ledger:
it keeps every cell the activation does not own and manufactures no grant.
The link store of `free` is the one leaf that leaves the activation inside
an allocator form (`Head.release`). -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}
/-! ## A leaf keeps the allocator words -/

section Meta

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg} {O : Orakel D}
  {passes : Nat}

/-- **A judged leaf keeps the free-list head, every link and the counter.** -/
theorem os_meta (hO : GutO O) : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c2 : Context}
    {st : Stmt D V l Γ Λ Λ'}, OS A I out k c st c2 → st.istBlatt = true →
    ∀ (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ),
      execStmt O passes keinRuf st σ ρ = .ok σ' ρ' → MetaSame A σ σ'
  | _, _, _, _, _, _, _, _, .assignSlot t f _ _ _ _ hn _ _ _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact (MetaSame.reads A σ _ _).trans (MetaSame.writeSlot A _ t _ _ f _ hn)
  | _, _, _, _, _, _, _, _, .assignThru _ t _ f _ _ _ _ hn _ _ _ _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact (MetaSame.reads A σ _ _).trans (MetaSame.writeSlot A _ t _ _ f _ hn)
  | _, _, _, _, _, _, _, _, .assignGlob g _ _ _ hg _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact (MetaSame.reads A σ _ _).trans (MetaSame.writeGlob A _ g _ _ hg)
  | _, _, _, _, _, _, _, _, .putBytes t f hf _ _ _ _ _ _ _ ht _ _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact (MetaSame.reads A σ _ _).trans (MetaSame.writeBytes A t f hf _ (fun he => absurd he.symm ht) _ _ _)
  | _, _, _, _, _, _, _, _, .assignSlotRef _ t _ _ f _ _ _ htA _ _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact (MetaSame.reads A σ _ _).trans (MetaSame.writeSlot A _ t _ _ f _ (fun he => absurd he.symm htA))
  | _, _, _, _, _, _, _, _, .assignVar .. => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact MetaSame.reads A σ _ _
  | _, _, _, _, _, _, _, _, .shift t f _ _ _ _ _ _ _ _ hl _ _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    split at h
    · injection h with h1 _
      subst σ'
      exact (MetaSame.reads A σ _ _).trans (MetaSame.writeSlot A _ t _ _ f _ hl)
    · cases h
  | _, _, _, _, _, _, _, _, .axiomCall a _ _ _ _ _ _ hfree _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    split at h
    · rename_i σ2 v heq
      injection h with h1 _
      subst σ'
      have hσ : σ2 = (axiomAntwort O a _ _).1 := (congrArg Prod.fst heq).symm
      rw [axiomAntwort_fst] at hσ
      rw [hσ]
      exact ((MetaSame.reads A σ _ _).trans (MetaSame.fragt A _ _)).trans (MetaSame.axiom hO hfree _ _)
    · cases h
  | _, _, _, _, _, _, _, _, .regWrite .. => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact MetaSame.reads A σ _ _
  | _, _, _, _, _, _, _, _, .transition .. => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact MetaSame.refl A σ
  | _, _, _, _, _, _, _, _, .publish g _ _ _ _ _ hg _ => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact (MetaSame.reads A σ _ _).trans (MetaSame.writeGlob A _ g _ _ hg)
  | _, _, _, _, _, _, _, _, .advances .. => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact MetaSame.refl A σ
  | _, _, _, _, _, _, _, _, .retires .. => by
    intro _ σ ρ σ' ρ' h
    simp only [execStmt] at h
    injection h with h1 _
    subst σ'
    exact MetaSame.refl A σ
  | _, _, _, _, _, _, _, _, .ret .. => by intro _ σ ρ σ' ρ' h; simp only [execStmt, reduceCtorEq] at h
  | _, _, _, _, _, _, _, _, .retWhy .. => by intro _ σ ρ σ' ρ' h; simp only [execStmt, reduceCtorEq] at h
  | _, _, _, _, _, _, _, _, .retScoped .. => by intro _ σ ρ σ' ρ' h; simp only [execStmt, reduceCtorEq] at h
  | _, _, _, _, _, _, _, _, .retWhyScoped .. => by intro _ σ ρ σ' ρ' h; simp only [execStmt, reduceCtorEq] at h
  | _, _, _, _, _, _, _, _, .leave .. => by intro _ σ ρ σ' ρ' h; simp only [execStmt, reduceCtorEq] at h
  | _, _, _, _, _, _, _, _, .next .. => by intro _ σ ρ σ' ρ' h; simp only [execStmt, reduceCtorEq] at h
  | _, _, _, _, _, _, _, _, .ite .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .onOption .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .onTag .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .onWhy .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .call .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .callInd .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .callIndElse .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .locks .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .breaking .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .traverse .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .consumeTraverse .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .retry .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl
  | _, _, _, _, _, _, _, _, .forever .. => by intro hl; simp only [Stmt.istBlatt, Bool.false_eq_true] at hl

end Meta

/-! ## The leaf step -/

section Step

variable {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat} {fr : Frame} {s : State}

/-- **What a step of the running activation leaves**: a next ledger that keeps every cell the activation does not
    own and manufactures no grant, agreeing with the next world, and the next state of the activation. -/
def Next (A : FreiForm D) (I : Interfaces A) (fr : Frame) (s : State) (σ σ' : World D) (f : D.Fn)
    (x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ) : Prop :=
  ∃ s', s.local s' fr ∧ s.progress s' ∧ s'.agrees A σ' ∧ A.FreiOk σ' ∧
    (∀ j, (∀ cell, s.cells j = some cell → cell.owner ≠ fr) → A.naechst σ' j = A.naechst σ j) ∧
    Head A I fr s' σ' f x

theorem Next.same {σ : World D} {f : D.Fn} {x} (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (h : Head A I fr s σ f x) : Next A I fr s σ σ f x :=
  ⟨s, State.local_refl s fr, State.progress_refl s, ha, ho, fun _ _ => rfl, h⟩

theorem Next.meta {σ σ' : World D} {f : D.Fn} {x} (ha : s.agrees A σ) (ho : A.FreiOk σ) (hm : MetaSame A σ σ')
    (h : Head A I fr s σ' f x) : Next A I fr s σ σ' f x :=
  ⟨s, State.local_refl s fr, State.progress_refl s, State.agrees_meta ha hm, freiOk_meta ho hm,
    fun j _ => hm.2.1 j, h⟩

theorem Next.of_holds {σ σ' : World D} {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context}
    {ρ : Env D Γ} {r : GRest D (vertragVon D f) l Γ Λ} (h : Holds A fr s c σ' ρ)
    (hk : k.references.length ≤ Γ.length) (hr : OR A I (I f).output k c r)
    (hl : ∀ j, A.naechst σ' j = A.naechst σ j := by intro _; rfl) :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  obtain ⟨g, s', hf, ha, ho, hlo, hp⟩ := FrameOk.of_holds h
  exact ⟨s', hlo, hp, ha, ho, fun j _ => hl j, .run ρ r hk hf hr⟩

/-- A step into a context no environment realises does not happen. -/
theorem holds_bad {σ' : World D} {Γ : Ctx} {ρ : Env D Γ} (h : Holds A fr s (badContext Γ) σ' ρ) : False := by
  obtain ⟨_, _, hf, _⟩ := FrameOk.of_holds h
  exact badContext_length Γ hf.length

/-- **A leaf statement in block position.** -/
theorem run_leaf (hO : GutO O) {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)} {k c : Context}
    {g : Ghost} {σ : World D} {ρ : Env D Γ} {st : Stmt D (vertragVon D f) l Γ Λ Λ1}
    {rest : Block D (vertragVon D f) l Γ Λ1 Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons st rest) r)) (hleaf : st.istBlatt = true)
    {σ' : World D} {ρ' : Env D Γ} (hstep : execStmt O passes keinRuf st σ ρ = .ok σ' ρ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ1, ρ', .dann rest r⟩ := by
  obtain ⟨c1, hb, hc⟩ := hr.dann_inv
  have hH := hf.holds ha ho
  rcases ob_cons_inv hb rfl with ⟨c2, hs, hrest⟩ | hd | ⟨t, f', i, e, hw, hL, g', e2, hwK, hLK, rest', c2, o, p,
    heq, ⟨ht, hfl⟩, hip, he, hg, he2, hcons, hrest⟩
  · have hp := os_sound (respects_keinRuf A I.contracts) hO hs σ ρ hk hH (passes := passes)
    rw [hstep] at hp
    exact Next.of_holds hp hk (OR.of_cont hrest hc) (os_meta hO hs hleaf σ ρ σ' ρ' hstep).2.1
  · have hp := os_sound (respects_keinRuf A I.contracts) hO (hd _ (badContext_bounded Γ)) σ ρ hk hH
      (passes := passes)
    rw [hstep] at hp
    exact (holds_bad hp).elim
  · cases heq
    subst ht hg
    cases hfl
    simp only [execStmt] at hstep
    injection hstep with hσ hρ
    subst σ' ρ'
    obtain ⟨hsource, howned, hctx⟩ := consume_facts hcons
    subst hctx
    obtain ⟨hh, hgh, hown⟩ := hf.2.2.1.1 o .owned howned
    have hx : ∀ σa σb, intVon _ (eval σa i σb ρ) = some hh.slot := by
      intro σa σb
      obtain ⟨other, hg', hvalue⟩ := origin_sound c g ρ hf.2.1 i o hsource σa σb
      rw [hgh] at hg'; cases hg'; exact hvalue
    have hpx : ρ.unten p = some hh.slot := by rw [← exprVarPos_eval i hip σ σ ρ]; exact hx σ σ
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
    have hlive : A.Lebt σ hh.slot := State.owned_live ha hown
    obtain ⟨ho2, hl2⟩ := link_live A hlive ho hk2 hs2 (fun j hj => by rw [hn2]; simp only [hj, ↓reduceIte])
    refine ⟨s, State.local_refl s fr, State.progress_refl s, ⟨ha.1, fun j => (hl2 j).trans (ha.2 j)⟩, ho2, ?_, ?_⟩
    · intro j hj
      rw [hn2]
      by_cases hjs : j = hh.slot
      · subst hjs
        obtain ⟨cell, hcell⟩ := State.own_cell hown
        exact absurd (State.owned_cell hown hcell).2.1 (hj _ hcell)
      · simp only [hjs, ↓reduceIte]
    exact .release ρ e2 hwK hLK rest' r p o hh he2 hpx howned hgh (by rw [hn2, hk2]; simp only [↓reduceIte]) hk hf
      (OR.of_cont hrest hc)

/-- **A leaf statement in end-block position.** -/
theorem run_leaf_ende (hO : GutO O) {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {k c : Context}
    {g : Ghost} {σ : World D} {ρ : Env D Γ} {st : Stmt D (vertragVon D f) l Γ Λ Λ1}
    {rest : Endblock D (vertragVon D f) l Γ Λ1}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.cons st rest))) (hleaf : st.istBlatt = true)
    {σ' : World D} {ρ' : Env D Γ} (hstep : execStmt O passes keinRuf st σ ρ = .ok σ' ρ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ1, ρ', .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    have hH := hf.holds ha ho
    rcases oe_cons_inv he rfl with ⟨c2, hs, hrest⟩ | hd
    · have hp := os_sound (respects_keinRuf A I.contracts) hO hs σ ρ hk hH (passes := passes)
      rw [hstep] at hp
      exact Next.of_holds hp hk (.ende rest hrest) (os_meta hO hs hleaf σ ρ σ' ρ' hstep).2.1
    · have hp := os_sound (respects_keinRuf A I.contracts) hO (hd _ (badContext_bounded Γ)) σ ρ hk hH
        (passes := passes)
      rw [hstep] at hp
      exact (holds_bad hp).elim

end Step

end Gabbro.Grammatik.ArenaOwnership.Machine
