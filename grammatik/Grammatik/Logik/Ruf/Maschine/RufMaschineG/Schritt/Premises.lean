module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

-- These abbreviations keep the constructor premises definitionally identical.
@[reducible] def RufDannHeadG (M : RufMaschineG D) (f : Faden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (M.faeden f).kopf.f) l Γ Λ') (ρ : Env D Γ) : Prop :=
  (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .dann b k⟩

@[reducible] def RufEndHeadG (M : RufMaschineG D) (f : Faden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D (vertragVon D (M.faeden f).kopf.f) l Γ Λ) (ρ : Env D Γ) : Prop :=
  (M.faeden f).kopf.rest = ⟨l, Γ, Λ, ρ, .ende b⟩

@[reducible] def RufBlattG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (f : Faden)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ')
    (ρ : Env D Γ) (out : Ausgang (vertragVon D (M.faeden f).kopf.f) l Γ) : Prop :=
  execStmt O passes keinRuf s (M.weltVon f) ρ = out

@[reducible] def RufWartetHeadG (caller : RufRahmenG D)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (rest : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
    (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρ : Env D Γ) : Prop :=
  caller.rest = ⟨l, Γ, Λ, ρ, .wartet rest k⟩ ∨
    ∃ (n : Nat) (err : Endblock D (vertragVon D caller.f) l (.why n :: Γ) Λ),
      caller.rest = ⟨l, Γ, Λ, ρ, .wartetSonst n err rest k⟩

-- A block premise uses the current head's contract, exactly as in the rules.
@[reducible] def RufBlockG (M : RufMaschineG D) (f : Faden)
    (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) : Type :=
  Block D (vertragVon D (M.faeden f).kopf.f) l Γ Λ Λ'

end Gabbro.Grammatik
