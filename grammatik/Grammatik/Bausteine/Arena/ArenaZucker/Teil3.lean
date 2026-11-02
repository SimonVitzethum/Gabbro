module

public import Grammatik.Bausteine.Arena.ArenaZucker.Teil1

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## C11 required allocation

    `Block.narrowRequired` applied to the arena counter: the same typed
    narrowing as `arenaAlloc` with a logical failure instead of a source
    `else`. Below the hard bound it stores and bumps exactly like
    `arenaRumpf`; at the bound it is `Logik.kapazitaet`, excluded by the
    caller's capacity duty (`KoerperGutS/SA`). Committed-storage
    availability, the provider path and the `KoerperGut` duty propagation
    are OPEN (design rows "No-else allocation" and "Allocation export/IR");
    export keeps the supplied-`else` semantics unchanged. -/

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **`let i = allocRequired A (v); …`** -- required narrowing of the
    counter into `0 ..< hi`, then the shared store-and-bump body. No
    `voll` branch: full is a logical failure, never a silent wrap. -/
def arenaAllocRequired (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') :
    Block D V l Γ Λ Λ' :=
  .narrowRequired (Expr.umTyp A.hz (Expr.glob A.zaehl hLG)) 0 (D.count A.tab - 1)
    (arenaRumpf A v hwT hLT hwG hLG rest)

end Block

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **Below the hard bound, a required allocation runs its body** -- the
    syntactic half of the capacity duty, mirroring
    `arenaAlloc_unter_schranke` with no `else` to take. -/
theorem arenaAllocRequired_unter_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < D.count A.tab) :
    execBlock (V := V) O passes R
        (Block.arenaAllocRequired A v hwT hLT hwG hLG rest) σ ρ
      = (execBlock O passes R (Block.arenaRumpf A v hwT hLT hwG hLG rest)
          (σ.lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ, by omega⟩ ρ)).schrumpf := by
  have hc : (0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1 :=
    ⟨A.stand_nonneg σ, by have := h; unfold ArenaForm.stand at this; omega⟩
  simp only [Block.arenaAllocRequired, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_pos hc]
  rfl

#print axioms arenaAllocRequired_unter_schranke

end Bedeutung
end Gabbro.Grammatik
