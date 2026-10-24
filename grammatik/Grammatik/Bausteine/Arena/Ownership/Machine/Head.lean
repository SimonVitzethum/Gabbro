import Grammatik.Bausteine.Arena.Ownership.Machine.View
import Grammatik.Bausteine.Arena.Ownership.Machine.Residue
import Grammatik.Bausteine.Arena.Ownership.Body.Shapes

/-! **The running activation of a thread.** Between two steps of machine G
the running activation is in one of five states. Ordinarily it realises a
source context over its environment and its residue is judged from that
context (`run`). Inside an executed allocator form a statement or two of the
form are still to run: the binder of `alloc` is bound but not yet granted
(`list`: the head still to take the link; `counter`: the counter still to
rise; `store`: the payload store still before it), or `free` has written the
link and the head is still to take the slot (`release`). The allocator words
such a state relies on are recorded against the actual world. -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- **The source side of one activation** over the ledger it sees. -/
def FrameOk (c : Context) (g : Ghost) (s : State) (fr : Frame) {Γ : Ctx} (ρ : Env D Γ) : Prop :=
  c.bounded ∧ References c g ρ ∧ Rights c g s fr ∧ Complete c g s fr

section Frame

variable {A : FreiForm D} {fr : Frame} {s : State} {σ : World D} {c : Context} {g : Ghost} {Γ : Ctx}
  {ρ : Env D Γ}

theorem FrameOk.holds (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ) :
    Holds A fr s c σ ρ :=
  ⟨g, s, ⟨ha, ho, hf.1, hf.2.1, hf.2.2.1⟩, hf.2.2.2, State.local_refl s fr, State.progress_refl s⟩

theorem FrameOk.of_holds (h : Holds A fr s c σ ρ) :
    ∃ g s', FrameOk c g s' fr ρ ∧ s'.agrees A σ ∧ A.FreiOk σ ∧ s.local s' fr ∧ s.progress s' := by
  obtain ⟨g, s', ⟨ha, ho, hb, hr, hri⟩, hc, hl, hp⟩ := h
  exact ⟨g, s', ⟨hb, hr, hri, hc⟩, ha, ho, hl, hp⟩

theorem FrameOk.length (hf : FrameOk c g s fr ρ) : c.references.length = Γ.length := hf.2.1.1

end Frame

/-- **The running activation `fr` of function `f`**, over the ledger `s` and the world `σ`. -/
inductive Head (A : FreiForm D) (I : Interfaces A) (fr : Frame) (s : State) (σ : World D) (f : D.Fn) :
    (Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ) → Prop where
  | run {l Γ Λ k c g} (ρ : Env D Γ) (r : GRest D (vertragVon D f) l Γ Λ)
      (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
      (hr : OR A I (I f).output k c r) : Head A I fr s σ f ⟨l, Γ, Λ, ρ, r⟩
  /-- `alloc` from the free list: the binder holds the head, which is still to take its link. -/
  | list {l Γ Λ Λ1 lo hi k c g} (x : Wert D (.int lo hi)) (ρ : Env D Γ)
      (e2 : Expr D (.int lo hi :: Γ) Λ (D.gtyp A.kopf)) (hw : (vertragVon D f).gschreibt A.kopf = true)
      (hL : gdarf D A.kopf Λ) (b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ1)
      (r : GRest D (vertragVon D f) l (.int lo hi :: Γ) Λ1)
      (he2 : exprSlotRead e2 = some ⟨A.tab, A.nxt, Γ.length⟩) (hx : x.n = A.kopfSt σ)
      (hlt : A.kopfSt σ < D.count A.tab) (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
      (hr : OR A I (I f).output k c.bindFresh (.dann b r)) :
      Head A I fr s σ f ⟨l, .int lo hi :: Γ, Λ, .cons x ρ, .dann (.cons (.assignGlob A.kopf e2 hw hL) b) r⟩
  /-- `alloc` from the counter: the binder holds the counter, which is still to rise. -/
  | counter {l Γ Λ Λ1 lo hi k c g} (x : Wert D (.int lo hi)) (ρ : Env D Γ)
      (e2 : Expr D (.int lo hi :: Γ) Λ (D.gtyp A.zaehl)) (hw : (vertragVon D f).gschreibt A.zaehl = true)
      (hL : gdarf D A.zaehl Λ) (b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ1)
      (r : GRest D (vertragVon D f) l (.int lo hi :: Γ) Λ1)
      (he2 : exprSucc e2 = some Γ.length) (hx : x.n = A.stand σ)
      (hlt : A.stand σ < D.count A.tab) (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
      (hr : OR A I (I f).output k c.bindFresh (.dann b r)) :
      Head A I fr s σ f ⟨l, .int lo hi :: Γ, Λ, .cons x ρ, .dann (.cons (.assignGlob A.zaehl e2 hw hL) b) r⟩
  /-- `alloc` from the counter, its payload store still before the counter rises. -/
  | store {l Γ Λ Λ1 lo hi k c g} (x : Wert D (.int lo hi)) (ρ : Env D Γ)
      (t : D.Tab) (f' : D.Feld t) (i : Expr D (.int lo hi :: Γ) Λ (.index (D.count t)))
      (ev : Expr D (.int lo hi :: Γ) Λ (D.typ t f')) (hws : (vertragVon D f).schreibt t = true)
      (hLs : darf D t Λ) (hn : NotLink A t f')
      (e2 : Expr D (.int lo hi :: Γ) Λ (D.gtyp A.zaehl)) (hw : (vertragVon D f).gschreibt A.zaehl = true)
      (hL : gdarf D A.zaehl Λ) (b : Block D (vertragVon D f) l (.int lo hi :: Γ) Λ Λ1)
      (r : GRest D (vertragVon D f) l (.int lo hi :: Γ) Λ1)
      (he2 : exprSucc e2 = some Γ.length) (hx : x.n = A.stand σ)
      (hlt : A.stand σ < D.count A.tab) (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
      (hr : OR A I (I f).output k c.bindFresh (.dann b r)) :
      Head A I fr s σ f ⟨l, .int lo hi :: Γ, Λ, .cons x ρ,
        .dann (.cons (.assignSlot t f' i ev hws hLs) (.cons (.assignGlob A.zaehl e2 hw hL) b)) r⟩
  /-- `free`: the link of the owned slot holds the head, which is still to take the slot. -/
  | release {l Γ Λ Λ1 k c g} (ρ : Env D Γ) (e2 : Expr D Γ Λ (D.gtyp A.kopf))
      (hw : (vertragVon D f).gschreibt A.kopf = true) (hL : gdarf D A.kopf Λ)
      (b : Block D (vertragVon D f) l Γ Λ Λ1) (r : GRest D (vertragVon D f) l Γ Λ1) (p o : Nat) (h : Handle)
      (he2 : exprVarPos e2 = some p) (hp : ρ.unten p = some h.slot) (ho : c.rights o = some .owned)
      (hg : g o = some h) (hlink : A.naechst σ h.slot = A.kopfSt σ)
      (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ)
      (hr : OR A I (I f).output k (c.kill o) (.dann b r)) :
      Head A I fr s σ f ⟨l, Γ, Λ, ρ, .dann (.cons (.assignGlob A.kopf e2 hw hL) b) r⟩

/-- Only the allocator words are read off the world. -/
theorem Head.meta {A : FreiForm D} {I : Interfaces A} {fr : Frame} {s : State} {σ σ' : World D} {f : D.Fn}
    {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ}
    (h : Head A I fr s σ f x) (hm : MetaSame A σ σ') : Head A I fr s σ' f x := by
  cases h with
  | run ρ r hk hf hr => exact .run ρ r hk hf hr
  | list x ρ e2 hw hL b r he2 hx hlt hk hf hr =>
    exact .list x ρ e2 hw hL b r he2 (by rw [hm.1]; exact hx) (by rw [hm.1]; exact hlt) hk hf hr
  | counter x ρ e2 hw hL b r he2 hx hlt hk hf hr =>
    exact .counter x ρ e2 hw hL b r he2 (by rw [hm.2.2]; exact hx) (by rw [hm.2.2]; exact hlt) hk hf hr
  | store x ρ t f' i ev hws hLs hn e2 hw hL b r he2 hx hlt hk hf hr =>
    exact .store x ρ t f' i ev hws hLs hn e2 hw hL b r he2 (by rw [hm.2.2]; exact hx)
      (by rw [hm.2.2]; exact hlt) hk hf hr
  | release ρ e2 hw hL b r p o h he2 hp ho hg hlink hk hf hr =>
    exact .release ρ e2 hw hL b r p o h he2 hp ho hg (by rw [hm.2.1, hm.1]; exact hlink) hk hf hr

end Gabbro.Grammatik.ArenaOwnership.Machine
