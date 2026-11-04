module
public import Grammatik.Bausteine.Arena.Ownership.Machine.Bind
public import Grammatik.Bausteine.Arena.Ownership.Machine.Unfold
@[expose] public section


/-! **The binding steps of the running activation**: `let`, a register read,
`awaits`, `exchange`, the float forms and the foreign calls bind a value in
front of the rest. A copied variable keeps its origin; every other bound
value carries no grant. The world changes by reads, by a store into a word
that is no allocator word, or by a foreign body that writes no arena
(`AxiomFree`, framed by the hardware assumption `GutO`). -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

section Step

variable {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {fr : Frame} {s : State}
  {f : D.Fn} {l : Bool} {Γ : Ctx} {k c : Context} {g : Ghost} {σ σ' : World D} {ρ : Env D Γ}

theorem run_floatEnde {Λ : List (Res D)} {op : GleitOp} {l1 h1 l2 h2 lo hi : Int × Int}
    {a : Expr D Γ Λ (.fl l1 h1)} {b : Expr D Γ Λ (.fl l2 h2)}
    {rest : Endblock D (vertragVon D f) l (.fl lo hi :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.float op a b lo hi rest))) (hm : MetaSame A σ σ')
    (v : Wert D (.fl lo hi)) :
    Next A I fr s σ σ' f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    cases he with
    | float _ _ _ _ _ _ _ _ hrest =>
      exact Next.holdsMeta hf ha ho hm (fun h => h.bindNone v)
        (Nat.le_succ_of_le hk) (.ende rest hrest)

theorem run_floatLitEnde {Λ : List (Res D)} {q lo hi : Int × Int}
    {rest : Endblock D (vertragVon D f) l (.fl lo hi :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.floatLit q lo hi rest))) (v : Wert D (.fl lo hi)) :
    Next A I fr s σ σ f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    cases he with
    | floatLit _ _ _ _ hrest =>
      exact Next.holdsMeta hf ha ho (MetaSame.refl A σ) (fun h => h.bindNone v)
        (Nat.le_succ_of_le hk) (.ende rest hrest)

theorem run_floatOfEnde {Λ : List (Res D)} {l1 h1 : Int} {lo hi : Int × Int} {e : Expr D Γ Λ (.int l1 h1)}
    {rest : Endblock D (vertragVon D f) l (.fl lo hi :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.floatOf e lo hi rest))) (hm : MetaSame A σ σ')
    (v : Wert D (.fl lo hi)) :
    Next A I fr s σ σ' f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    cases he with
    | floatOf _ _ _ _ _ hrest =>
      exact Next.holdsMeta hf ha ho hm (fun h => h.bindNone v)
        (Nat.le_succ_of_le hk) (.ende rest hrest)

theorem run_floatNarrowEnde {Λ : List (Res D)} {l1 h1 lo hi : Int × Int} {e : Expr D Γ Λ (.fl l1 h1)}
    {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Endblock D (vertragVon D f) l (.fl lo hi :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.floatNarrow e lo hi sonst rest))) (hm : MetaSame A σ σ')
    (v : Wert D (.fl lo hi)) :
    Next A I fr s σ σ' f ⟨l, .fl lo hi :: Γ, Λ, .cons v ρ, .ende rest⟩ := by
  cases hr with
  | ende _ he =>
    cases he with
    | floatNarrow _ _ _ _ _ _ hs hrest =>
      exact Next.holdsMeta hf ha ho hm (fun h => h.bindNone v)
        (Nat.le_succ_of_le hk) (.ende rest hrest)

theorem run_floatNarrowSonstEnde {Λ : List (Res D)} {l1 h1 lo hi : Int × Int} {e : Expr D Γ Λ (.fl l1 h1)}
    {sonst : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Endblock D (vertragVon D f) l (.fl lo hi :: Γ) Λ}
    (hk : k.references.length ≤ Γ.length) (hf : FrameOk c g s fr ρ) (ha : s.agrees A σ) (ho : A.FreiOk σ)
    (hr : OR A I (I f).output k c (.ende (.floatNarrow e lo hi sonst rest))) (hm : MetaSame A σ σ') :
    Next A I fr s σ σ' f ⟨l, Γ, Λ, ρ, .ende sonst⟩ := by
  cases hr with
  | ende _ he =>
    cases he with
    | floatNarrow _ _ _ _ _ _ hs hrest =>
      exact Next.meta ha ho hm (.run ρ _ hk hf (.ende sonst hs))

end Step
end Gabbro.Grammatik.ArenaOwnership.Machine
