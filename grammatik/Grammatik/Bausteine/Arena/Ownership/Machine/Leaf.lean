import Grammatik.Bausteine.Arena.Ownership.Machine.Head
import Grammatik.Bausteine.Arena.Ownership.Body.Sound

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

/-- Leaf statements never call: the empty handler respects every contract. -/
theorem respects_keinRuf (A : FreiForm D) (C : ∀ f, Contract D f) : Respects A C (keinRuf (D := D)) :=
  fun _ _ _ _ _ _ _ _ => ⟨fun _ _ h => by simp [keinRuf] at h, fun _ _ h => by simp [keinRuf] at h⟩

/-- A context that no environment over `Γ` realises. -/
def badContext (Γ : Ctx) : Context := ⟨List.replicate (Γ.length + 1) none, fun _ => none, 0⟩

theorem badContext_bounded (Γ : Ctx) : (badContext Γ).bounded :=
  ⟨fun _ _ => rfl, fun ref hm i hi => by
    simp only [badContext] at hm
    rw [List.eq_of_mem_replicate hm] at hi
    cases hi⟩

theorem badContext_length (Γ : Ctx) : (badContext Γ).references.length ≠ Γ.length := by
  simp [badContext]

section Cont

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- What a residue needs behind a block that ends in `c1`. -/
def Cont (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (k c1 : Context) (r : GRest D V l Γ Λ) : Prop :=
  OR A I out k c1 r ∨ (c1.references.length ≠ Γ.length ∧ OX A I out k r)

theorem OR.of_cont {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c1 : Context}
    {b : Block D V l Γ Λ Λ'} {r : GRest D V l Γ Λ'} (hb : OB A I out k c b c1) (hc : Cont A I out k c1 r) :
    OR A I out k c (.dann b r) := by
  rcases hc with h | ⟨hu, hx⟩
  · exact .dann b r hb h
  · exact .dannDead b r hb hu hx

theorem OR.dann_inv {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c : Context}
    {b : Block D V l Γ Λ Λ'} {r : GRest D V l Γ Λ'} (h : OR A I out k c (.dann b r)) :
    ∃ c1, OB A I out k c b c1 ∧ Cont A I out k c1 r := by
  cases h with
  | dann _ _ hb hr => exact ⟨_, hb, Or.inl hr⟩
  | dannDead _ _ hb hu hx => exact ⟨_, hb, Or.inr ⟨hu, hx⟩⟩

theorem Cont.exits {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c1 : Context} {r : GRest D V l Γ Λ}
    (h : Cont A I out k c1 r) : OX A I out k r := by
  rcases h with h | ⟨_, hx⟩
  · exact h.exits
  · exact hx

/-- A block that never falls through: any end context, the exit half behind it. -/
theorem OR.of_dead {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c : Context}
    {b : Block D V l Γ Λ Λ'} {r : GRest D V l Γ Λ'} (hb : OB A I out k c b (badContext Γ))
    (hx : OX A I out k r) : OR A I out k c (.dann b r) :=
  .dannDead b r hb (badContext_length Γ) hx

end Cont

/-! ## Inverting a block that starts with a statement -/

section Inv

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- **A block `s; rest` is judged** through its statement, as dead behind a statement that never falls through,
    or as an executed `free`. -/
theorem ob_cons_inv : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c1 : Context} {b : Block D V l Γ Λ Λ'},
    OB A I out k c b c1 →
    ∀ {Λ1 : List (Res D)} {st : Stmt D V l Γ Λ Λ1} {rest : Block D V l Γ Λ1 Λ'}, b = .cons st rest →
    (∃ c2, OS A I out k c st c2 ∧ OB A I out k c2 rest c1) ∨ (∀ c2, c2.bounded → OS A I out k c st c2) ∨
    (∃ (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
        (hw : V.schreibt t = true) (hL : darf D t Λ) (g : D.Glob) (e2 : Expr D Γ Λ (D.gtyp g))
        (hwK : V.gschreibt g = true) (hLK : gdarf D g Λ) (rest' : Block D V l Γ Λ Λ') (c2 : Context) (o p : Nat),
      (Block.cons st rest : Block D V l Γ Λ Λ') =
          .cons (.assignSlot t f i e hw hL) (.cons (.assignGlob g e2 hwK hLK) rest') ∧
        (∃ ht : t = A.tab, ht ▸ f = A.nxt) ∧ exprVarPos i = some p ∧ exprGlob e = some A.kopf ∧ g = A.kopf ∧
        exprVarPos e2 = some p ∧ consume c i = some (c2, o) ∧ OB A I out k c2 rest' c1)
  | _, _, _, _, _, _, _, _, .cons s rest hs hr => by
    intro he
    cases he
    exact Or.inl ⟨_, hs, hr⟩
  | _, _, _, _, _, _, _, _, .dead s rest hs => by
    intro he
    cases he
    exact Or.inr (Or.inl hs)
  | _, _, _, _, _, _, _, _, .weaken b hb hw => by
    intro he
    rcases ob_cons_inv hb he with ⟨c2, hs, hr⟩ | hd | ⟨t, f, i, e, hw', hL, g, e2, hwK, hLK, rest', c2, o, p, he',
      hf, hi, hk, hg, he2, hc, hr⟩
    · exact Or.inl ⟨c2, hs, .weaken _ hr hw⟩
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr ⟨t, f, i, e, hw', hL, g, e2, hwK, hLK, rest', c2, o, p, he', hf, hi, hk, hg, he2, hc,
        .weaken _ hr hw⟩)
  | _, _, _, _, _, _, _, _, .release t f i e hw hL g e2 hwK hLK rest ht hf hip he hg he2 hc hrest => by
    intro heq
    exact Or.inr (Or.inr ⟨t, f, i, e, hw, hL, g, e2, hwK, hLK, rest, _, _, _, heq.symm, ⟨ht, hf⟩, hip, he, hg, he2,
      hc, hrest⟩)
  | _, _, _, _, _, _, _, _, .nil => by intro he; cases he
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
  | _, _, _, _, _, _, _, _, .narrow .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .check .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .float .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .floatLit .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .floatOf .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .floatNarrow .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .allocList .. => by intro he; cases he
  | _, _, _, _, _, _, _, _, .allocCounter .. => by intro he; cases he

/-- **An end block `s; rest` is judged** through its statement, or as dead behind it. -/
theorem oe_cons_inv {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {e : Endblock D V l Γ Λ}
    (h : OE A I out k c e) :
    ∀ {Λ1 : List (Res D)} {st : Stmt D V l Γ Λ Λ1} {rest : Endblock D V l Γ Λ1}, e = .cons st rest →
    (∃ c2, OS A I out k c st c2 ∧ OE A I out k c2 rest) ∨ (∀ c2, c2.bounded → OS A I out k c st c2) := by
  cases h with
  | cons s rest hs hr => intro _ st rest' he; cases he; exact Or.inl ⟨_, hs, hr⟩
  | dead s rest hs => intro _ st rest' he; cases he; exact Or.inr hs
  | _ => intro _ _ _ he; cases he

end Inv

/-! ## The link store of `free` -/

/-- **Storing the link of a live slot** leaves the list and every liveness alone. -/
theorem link_live (A : FreiForm D) {σ σ2 : World D} {i : Int} (hi : A.Lebt σ i) (hok : A.FreiOk σ)
    (hk : A.kopfSt σ2 = A.kopfSt σ) (hs : A.stand σ2 = A.stand σ)
    (ho : ∀ j, j ≠ i → A.naechst σ2 j = A.naechst σ j) :
    A.FreiOk σ2 ∧ ∀ j, A.Lebt σ2 j ↔ A.Lebt σ j := by
  obtain ⟨L, hL, hnd, hlt⟩ := hok
  have hiL : i ∉ L := fun hm => hi.2.2 ⟨L, hL, hm⟩
  have hL2 : FreiForm.Kette A σ2 (A.kopfSt σ2) L := by
    rw [hk]
    exact FreiForm.Kette.uebertragen hL (fun j hj => ho j (fun he => hiL (he ▸ hj)))
  refine ⟨⟨L, hL2, hnd, fun j hj => by rw [hs]; exact hlt j hj⟩, fun j => ?_⟩
  have hauf : A.AufListe σ2 j ↔ A.AufListe σ j := by
    constructor
    · rintro ⟨L', hL', hm⟩
      rw [FreiForm.Kette.eindeutig hL' hL2] at hm
      exact ⟨L, hL, hm⟩
    · rintro ⟨L', hL', hm⟩
      rw [FreiForm.Kette.eindeutig hL' hL] at hm
      exact ⟨L, hL2, hm⟩
  unfold FreiForm.Lebt
  rw [hs, hauf]

/-! ## The leaf step -/

section Step

variable {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat} {fr : Frame} {s : State}

/-- **What a step of the running activation leaves**: a next ledger that keeps every cell the activation does not
    own and manufactures no grant, agreeing with the next world, and the next state of the activation. -/
def Next (A : FreiForm D) (I : Interfaces A) (fr : Frame) (s : State) (σ' : World D) (f : D.Fn)
    (x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D f) l Γ Λ) : Prop :=
  ∃ s', s.local s' fr ∧ s.progress s' ∧ s'.agrees A σ' ∧ A.FreiOk σ' ∧ Head A I fr s' σ' f x

theorem Next.same {σ' : World D} {f : D.Fn} {x} (ha : s.agrees A σ') (ho : A.FreiOk σ')
    (h : Head A I fr s σ' f x) : Next A I fr s σ' f x :=
  ⟨s, State.local_refl s fr, State.progress_refl s, ha, ho, h⟩

theorem Next.of_holds {σ' : World D} {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context}
    {ρ : Env D Γ} {r : GRest D (vertragVon D f) l Γ Λ} (h : Holds A fr s c σ' ρ)
    (hk : k.references.length ≤ Γ.length) (hr : OR A I (I f).output k c r) :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, r⟩ := by
  obtain ⟨g, s', hf, ha, ho, hl, hp⟩ := FrameOk.of_holds h
  exact ⟨s', hl, hp, ha, ho, .run ρ r hk hf hr⟩

/-- A step into a context no environment realises does not happen. -/
theorem holds_bad {σ' : World D} {Γ : Ctx} {ρ : Env D Γ} (h : Holds A fr s (badContext Γ) σ' ρ) : False := by
  obtain ⟨_, _, hf, _⟩ := FrameOk.of_holds h
  exact badContext_length Γ hf.length

/-- **A leaf statement in block position.** -/
theorem run_leaf (hO : GutO O) {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 Λ' : List (Res D)} {k c : Context}
    {g : Ghost} {σ : World D} {ρ : Env D Γ} {st : Stmt D (vertragVon D f) l Γ Λ Λ1}
    {rest : Block D (vertragVon D f) l Γ Λ1 Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.cons st rest) r))
    {σ' : World D} {ρ' : Env D Γ} (hstep : execStmt O passes keinRuf st σ ρ = .ok σ' ρ') :
    Next A I fr s σ' f ⟨l, Γ, Λ1, ρ', .dann rest r⟩ := by
  obtain ⟨c1, hb, hc⟩ := hr.dann_inv
  have hH := hf.holds ha ho
  rcases ob_cons_inv hb rfl with ⟨c2, hs, hrest⟩ | hd | ⟨t, f', i, e, hw, hL, g', e2, hwK, hLK, rest', c2, o, p,
    heq, ⟨ht, hfl⟩, hip, he, hg, he2, hcons, hrest⟩
  · have hp := os_sound (respects_keinRuf A I.contracts) hO hs σ ρ hk hH (passes := passes)
    rw [hstep] at hp
    exact Next.of_holds hp hk (OR.of_cont hrest hc)
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
    obtain ⟨ho2, hl2⟩ := link_live A hlive ho hk2 hs2 (fun j hj => by rw [hn2]; simp [hj])
    refine Next.same ⟨ha.1, fun j => (hl2 j).trans (ha.2 j)⟩ ho2 ?_
    exact .release ρ e2 hwK hLK rest' r p o hh he2 hpx howned hgh (by rw [hn2, hk2]; simp) hk hf
      (OR.of_cont hrest hc)

/-- **A leaf statement in end-block position.** -/
theorem run_leaf_ende (hO : GutO O) {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {k c : Context}
    {g : Ghost} {σ : World D} {ρ : Env D Γ} {st : Stmt D (vertragVon D f) l Γ Λ Λ1}
    {rest : Endblock D (vertragVon D f) l Γ Λ1}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.cons st rest)))
    {σ' : World D} {ρ' : Env D Γ} (hstep : execStmt O passes keinRuf st σ ρ = .ok σ' ρ') :
    Next A I fr s σ' f ⟨l, Γ, Λ1, ρ', .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    have hH := hf.holds ha ho
    rcases oe_cons_inv he rfl with ⟨c2, hs, hrest⟩ | hd
    · have hp := os_sound (respects_keinRuf A I.contracts) hO hs σ ρ hk hH (passes := passes)
      rw [hstep] at hp
      exact Next.of_holds hp hk (.ende rest hrest)
    · have hp := os_sound (respects_keinRuf A I.contracts) hO (hd _ (badContext_bounded Γ)) σ ρ hk hH
        (passes := passes)
      rw [hstep] at hp
      exact (holds_bad hp).elim

end Step

end Gabbro.Grammatik.ArenaOwnership.Machine
