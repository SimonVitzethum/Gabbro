import Grammatik.Bausteine.Arena.Ownership.Machine.Unfold

/-! **The binding steps of the running activation**: `let`, a register read,
`awaits`, `exchange`, the float forms and the foreign calls bind a value in
front of the rest. A copied variable keeps its origin; every other bound
value carries no grant. The world changes by reads, by a store into a word
that is no allocator word, or by a foreign body that writes no arena
(`AxiomFree`, framed by the hardware assumption `GutO`). -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

theorem meta_axiom {A : FreiForm D} {O : Orakel D} (hO : GutO O) {a : D.Ax} (hfree : AxiomFree A a)
    {σ σ' : World D} {ρ : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a))}
    (hax : axiomAntwort O a σ ρ = (σ', x)) : MetaSame A σ σ' := by
  have h := congrArg Prod.fst hax
  simp only [axiomAntwort_fst] at h
  rw [← h]
  exact MetaSame.axiom hO hfree σ ρ

theorem meta_axiomSonst {A : FreiForm D} {O : Orakel D} (hO : GutO O) {a : D.Ax} (hfree : AxiomFree A a)
    {σ σ' : World D} {ρ : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hax : axiomAntwortSonst O a σ ρ = (σ', x)) : MetaSame A σ σ' := by
  have h := congrArg Prod.fst hax
  simp only [axiomAntwortSonst_fst, axiomAntwort_fst] at h
  rw [← h]
  exact MetaSame.axiom hO hfree σ ρ

section Step

variable {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {fr : Frame} {s : State}
  {f : D.Fn} {l : Bool} {Γ : Ctx} {k c : Context} {g : Ghost} {σ σ' : World D} {ρ : Env D Γ}

/-- A binder without provenance in front of the rest. -/
theorem Next.bindNone {Λ Λ' : List (Res D)} {τ : Ty} {c1 cout : Context}
    {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hm : MetaSame A σ σ') (hrest : OB A I (I f).output k (c.bind none) rest c1) (hd : DropW cout c1)
    (hc : Cont A I (I f).output k cout r) (v : Wert D τ) :
    Next A I fr s σ' f ⟨l, τ :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ :=
  Next.holdsMeta hf ha ho hm (fun h => h.bindNone v) (Nat.le_succ_of_le hk) (OR.binder hrest hd hk hc)

/-- `let x = e;` -/
theorem run_bind {Λ Λ' : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.bind e rest) r)) :
    Next A I fr s (σ.lese Λ e.orte) f
      ⟨l, τ :: Γ, Λ, .cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, c1, hrest, hd⟩ := ob_top hb
  exact Next.holdsMeta hf ha ho (MetaSame.reads A σ Λ e.orte) (fun h => h.bindExpr e _ _)
    (Nat.le_succ_of_le hk) (OR.binder hrest hd hk hc)

/-- `let x = e;` at the top level of a body. -/
theorem run_bindEnde {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.bind e rest))) :
    Next A I fr s (σ.lese Λ e.orte) f
      ⟨l, τ :: Γ, Λ, .cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ, .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    cases he with
    | bind _ _ _ hrest =>
      exact Next.holdsMeta hf ha ho (MetaSame.reads A σ Λ e.orte) (fun h => h.bindExpr e _ _)
        (Nat.le_succ_of_le hk) (.ende rest hrest)

/-- A register read. -/
theorem run_regRead {Λ Λ' : List (Res D)} {re : D.Reg} {hkl : (D.rklasse re).lesbar = true}
    {rest : Block D (vertragVon D f) l (D.rtyp re :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.regRead re hkl rest) r)) (v : Wert D (D.rtyp re)) :
    Next A I fr s σ f ⟨l, D.rtyp re :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho (MetaSame.refl A σ) hrest hd hc v

/-- A register read whose promise holds. -/
theorem run_regReadElse {Λ Λ' : List (Res D)} {re : D.Reg} {hkl : (D.rklasse re).lesbar = true}
    {z : Expr D (D.rtyp re :: Γ) Λ .bool} {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l (D.rtyp re :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.regReadElse re hkl z sonst rest) r)) (hm : MetaSame A σ σ')
    (v : Wert D (D.rtyp re)) :
    Next A I fr s σ' f ⟨l, D.rtyp re :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, _, c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho hm hrest hd hc v

/-- A register read whose promise fails runs its `else` branch. -/
theorem run_regReadSonst {Λ Λ' : List (Res D)} {re : D.Reg} {hkl : (D.rklasse re).lesbar = true}
    {z : Expr D (D.rtyp re :: Γ) Λ .bool} {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l (D.rtyp re :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.regReadElse re hkl z sonst rest) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, hs, _⟩ := ob_top hb
  exact Next.meta ha ho hm (.run ρ _ hk hf (OR.sonst hs hc.exits))

/-- `awaits`. -/
theorem run_awaits {Λ Λ' : List (Res D)} {gl : D.Glob} {pl : List D.Glob} {hp : pl = D.nutzlast gl}
    {hL : gdarf D gl Λ} {hat : D.atomar gl = true}
    {rest : Block D (vertragVon D f) l (D.gtyp gl :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.awaits gl pl hp hL hat rest) r)) (hm : MetaSame A σ σ')
    (v : Wert D (D.gtyp gl)) :
    Next A I fr s σ' f ⟨l, D.gtyp gl :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho hm hrest hd hc v

/-- `exchange`: the store goes to a word that is no allocator word. -/
theorem run_exchange {Λ Λ' : List (Res D)} {gl : D.Glob} {neu : Expr D (D.gtyp gl :: Γ) Λ (D.gtyp gl)}
    {hw : (vertragVon D f).gschreibt gl = true} {hL : gdarf D gl Λ}
    {rest : Block D (vertragVon D f) l (D.gtyp gl :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.exchange gl neu hw hL rest) r)) (σ₁ : World D)
    (hm₁ : MetaSame A σ σ₁) (x : Wert D (D.gtyp gl)) (v : Wert D (D.gtyp gl)) :
    Next A I fr s (σ₁.schreibGlob gl Λ x) f ⟨l, D.gtyp gl :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨hg, _, c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho (hm₁.trans (MetaSame.writeGlob A σ₁ gl Λ x hg)) hrest hd hc v

/-- The float forms. -/
theorem run_float {Λ Λ' : List (Res D)} {op : GleitOp} {l1 h1 l2 h2 lo hi : Int × Int}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    {rest : Block D (vertragVon D f) l (.fl lo hi :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.float op a b lo hi rest) r)) (hm : MetaSame A σ σ')
    (v : Wert D (.fl lo hi)) :
    Next A I fr s σ' f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, _, c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho hm hrest hd hc v

theorem run_floatLit {Λ Λ' : List (Res D)} {q lo hi : Int × Int}
    {rest : Block D (vertragVon D f) l (.fl lo hi :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.floatLit q lo hi rest) r)) (v : Wert D (.fl lo hi)) :
    Next A I fr s σ f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho (MetaSame.refl A σ) hrest hd hc v

theorem run_floatOf {Λ Λ' : List (Res D)} {l1 h1 : Int} {lo hi : Int × Int} {e : Expr D Γ Λ (.int l1 h1)}
    {rest : Block D (vertragVon D f) l (.fl lo hi :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.floatOf e lo hi rest) r)) (hm : MetaSame A σ σ')
    (v : Wert D (.fl lo hi)) :
    Next A I fr s σ' f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho hm hrest hd hc v

theorem run_floatNarrow {Λ Λ' : List (Res D)} {l1 h1 lo hi : Int × Int} {e : Expr D Γ Λ (.fl l1 h1)}
    {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l (.fl lo hi :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.floatNarrow e lo hi sonst rest) r)) (hm : MetaSame A σ σ')
    (v : Wert D (.fl lo hi)) :
    Next A I fr s σ' f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, _, c1, hrest, hd⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho hm hrest hd hc v

theorem run_floatNarrowSonst {Λ Λ' : List (Res D)} {l1 h1 lo hi : Int × Int} {e : Expr D Γ Λ (.fl l1 h1)}
    {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l (.fl lo hi :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.floatNarrow e lo hi sonst rest) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, hs, _⟩ := ob_top hb
  exact Next.meta ha ho hm (.run ρ _ hk hf (OR.sonst hs hc.exits))

/-- `check` that holds runs the rest. -/
theorem run_check {Λ Λ' : List (Res D)} {cond : Expr D Γ Λ .bool} {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l Γ Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.check cond sonst rest) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann rest r⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, _, c1, hrest, hw⟩ := ob_top hb
  exact Next.meta ha ho hm (.run ρ _ hk hf (OR.weakened hrest hw hc))

/-- `check` that fails runs its `else` branch. -/
theorem run_checkSonst {Λ Λ' : List (Res D)} {cond : Expr D Γ Λ .bool} {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l Γ Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.check cond sonst rest) r)) (hm : MetaSame A σ σ') :
    Next A I fr s σ' f ⟨l, Γ, Λ, ρ, .dann sonst.alsBlock.2 (.abbruch r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨_, hs, _⟩ := ob_top hb
  exact Next.meta ha ho hm (.run ρ _ hk hf (OR.sonst hs hc.exits))

/-! ## Foreign calls -/

/-- `let x = a(…);` of a foreign body. -/
theorem run_bindAxiom (hO : GutO O) {Λ Λ' : List (Res D)} {τ : Ty} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)}
    {he : D.aerg a = some τ} {hw : ∀ t, D.aschreibt a t = true → (vertragVon D f).schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → (vertragVon D f).gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ} {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.bindAxiom a args he hw hg hd hgd rest) r))
    {σ₂ : World D} {ρa : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a))}
    (hax : axiomAntwort O a (σ.lese Λ args.orte) ρa = (σ₂, x)) (v : Wert D τ) :
    Next A I fr s σ₂ f ⟨l, τ :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨hfree, _, c1, hrest, hd'⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho ((MetaSame.reads A σ Λ args.orte).trans (meta_axiom hO hfree hax))
    hrest hd' hc v

/-- `let x = a(…) else { … };` of a foreign body that answers a value. -/
theorem run_bindAxiomElse (hO : GutO O) {Λ Λ' : List (Res D)} {τ : Ty} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ} {hr0 : 0 < D.agruende a}
    {hw : ∀ t, D.aschreibt a t = true → (vertragVon D f).schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → (vertragVon D f).gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ} {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {err : Endblock D (vertragVon D f) l (.why (D.agruende a) :: Γ) Λ}
    {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.bindAxiomElse a args he hr0 hw hg hd hgd err rest) r))
    {σ₂ : World D} {ρa : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hax : axiomAntwortSonst O a (σ.lese Λ args.orte) ρa = (σ₂, x)) (v : Wert D τ) :
    Next A I fr s σ₂ f ⟨l, τ :: Γ, Λ, .cons v ρ, .dann rest (.schrumpf r)⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨hfree, _, _, c1, hrest, hd'⟩ := ob_top hb
  exact Next.bindNone hk hf ha ho ((MetaSame.reads A σ Λ args.orte).trans (meta_axiomSonst hO hfree hax))
    hrest hd' hc v

/-- … that answers a reason: the `else` block runs with it bound. -/
theorem run_bindAxiomGrund (hO : GutO O) {Λ Λ' : List (Res D)} {τ : Ty} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ} {hr0 : 0 < D.agruende a}
    {hw : ∀ t, D.aschreibt a t = true → (vertragVon D f).schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → (vertragVon D f).gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ} {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {err : Endblock D (vertragVon D f) l (.why (D.agruende a) :: Γ) Λ}
    {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} {r : GRest D (vertragVon D f) l Γ Λ'}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.dann (.bindAxiomElse a args he hr0 hw hg hd hgd err rest) r))
    {σ₂ : World D} {ρa : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hax : axiomAntwortSonst O a (σ.lese Λ args.orte) ρa = (σ₂, x)) (rg : Fin (D.agruende a)) :
    Next A I fr s σ₂ f ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) rg ρ),
      .dann err.alsBlock.2 (.abbruch (.schrumpf r))⟩ := by
  obtain ⟨cout, hb, hc⟩ := hr.dann_inv
  obtain ⟨hfree, _, herr, _⟩ := ob_top hb
  exact Next.holdsMeta hf ha ho ((MetaSame.reads A σ Λ args.orte).trans (meta_axiomSonst hO hfree hax))
    (fun h => h.bindNone (τ := .why (D.agruende a)) rg) (Nat.le_succ_of_le hk)
    (OR.sonst herr (.schrumpf r hk hc.exits))

/-- Foreign calls at the top level of a body. -/
theorem run_bindAxiomEnde (hO : GutO O) {Λ : List (Res D)} {τ : Ty} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)}
    {he : D.aerg a = some τ} {hw : ∀ t, D.aschreibt a t = true → (vertragVon D f).schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → (vertragVon D f).gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ} {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.bindAxiom a args he hw hg hd hgd rest)))
    {σ₂ : World D} {ρa : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a))}
    (hax : axiomAntwort O a (σ.lese Λ args.orte) ρa = (σ₂, x)) (v : Wert D τ) :
    Next A I fr s σ₂ f ⟨l, τ :: Γ, Λ, .cons v ρ, .ende rest⟩ := by
  cases hr with
  | ende _ he' =>
    cases he' with
    | bindAxiom _ _ _ _ _ _ _ _ hfree _ hrest =>
      exact Next.holdsMeta hf ha ho ((MetaSame.reads A σ Λ args.orte).trans (meta_axiom hO hfree hax))
        (fun h => h.bindNone v) (Nat.le_succ_of_le hk) (.ende rest hrest)

theorem run_bindAxiomElseEnde (hO : GutO O) {Λ : List (Res D)} {τ : Ty} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ} {hr0 : 0 < D.agruende a}
    {hw : ∀ t, D.aschreibt a t = true → (vertragVon D f).schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → (vertragVon D f).gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ} {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {err : Endblock D (vertragVon D f) l (.why (D.agruende a) :: Γ) Λ}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.bindAxiomElse a args he hr0 hw hg hd hgd err rest)))
    {σ₂ : World D} {ρa : Env D (D.aparams a)} {x : Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hax : axiomAntwortSonst O a (σ.lese Λ args.orte) ρa = (σ₂, x)) :
    (∀ v : Wert D τ, Next A I fr s σ₂ f ⟨l, τ :: Γ, Λ, .cons v ρ, .ende rest⟩) ∧
    (∀ rg : Fin (D.agruende a), Next A I fr s σ₂ f
      ⟨l, .why (D.agruende a) :: Γ, Λ, (Env.cons (τ := .why (D.agruende a)) rg ρ), .ende err⟩) := by
  cases hr with
  | ende _ he' =>
    cases he' with
    | bindAxiomElse _ _ _ _ _ _ _ _ _ _ hfree _ herr hrest =>
      have hm := (MetaSame.reads A σ Λ args.orte).trans (meta_axiomSonst hO hfree hax)
      exact ⟨fun v => Next.holdsMeta hf ha ho hm (fun h => h.bindNone v) (Nat.le_succ_of_le hk) (.ende rest hrest),
        fun rg => Next.holdsMeta hf ha ho hm (fun h => h.bindNone (τ := .why (D.agruende a)) rg)
          (Nat.le_succ_of_le hk) (.ende err herr)⟩

end Step

end Gabbro.Grammatik.ArenaOwnership.Machine
