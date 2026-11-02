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
    caller's capacity duty. The duty is the existing one, not a new channel:
    the second clause of `KoerperGutS`/`KoerperGutSA` excludes EVERY `Logik`
    outcome of the body's run, `kapazitaet` included, and it travels through
    calls with the generic `torRuf`/`rufAt` handler machinery
    (`NutzerPflicht`/`LogikPflicht(A)`); no `Spec.lean` change. The static
    arena commits all its slots, so no provider or committed-storage
    availability beyond the counter bound is owed; dynamic (`max`) and
    unbounded (`pb`) arenas elaborate to no `ArenaForm` here. Export keeps
    the supplied-`else` semantics unchanged. -/

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

/-- **At the hard bound, a required allocation is a capacity failure** -- the
    syntactic half of the capacity duty: a full arena at a required allocation
    is `Logik.kapazitaet`, never a silent wrap, a fabricated value or a
    hardware failure. The caller's `KoerperGutS`/`KoerperGutSA` duty
    (`NutzerPflicht`/`LogikPflicht(A)`) excludes exactly this outcome. -/
theorem arenaAllocRequired_an_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ = D.count A.tab) :
    execBlock (V := V) O passes R
        (Block.arenaAllocRequired A v hwT hLT hwG hLG rest) σ ρ
      = .logik .kapazitaet := by
  have hp := A.hpos
  have hn : ¬ ((0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1) := by
    have := h; unfold ArenaForm.stand at this; omega
  simp only [Block.arenaAllocRequired, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_neg hn]

#print axioms arenaAllocRequired_an_schranke

/-- **The required allocation stores at index `0` on the empty arena** -- the
    joint witness: an empty counter is strictly under the bound, so the shared
    body runs with the fresh index. -/
theorem zeuge_allocRequired_leer (O : Orakel ArenaZeuge.ZD) (passes : Nat)
    (R : ∀ f : ArenaZeuge.ZD.Fn, World ArenaZeuge.ZD → Env ArenaZeuge.ZD (ArenaZeuge.ZD.params f) → RufAusgang f)
    (rest : Block ArenaZeuge.ZV false [Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab)] [] []) :
    execBlock (V := ArenaZeuge.ZV) O passes R
        (Block.arenaAllocRequired ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
        (ArenaZeuge.welt 0 (by decide) (by decide)) .nil
      = (execBlock O passes R
          (Block.arenaRumpf ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
          ((ArenaZeuge.welt 0 (by decide) (by decide)).lese [] [Sum.inr ()])
          (.cons ⟨0, by decide, by decide⟩ .nil)).schrumpf :=
  arenaAllocRequired_unter_schranke O passes R _ _ rfl _ rfl _ _ _ .nil (by decide)

/-- **And on the full arena it is a capacity failure, never a wrap** -- the
    same fixture at the bound: the joint witness that a required allocation
    has no success continuation to confuse with its failure. -/
theorem zeuge_allocRequired_voll_kapazitaet (O : Orakel ArenaZeuge.ZD) (passes : Nat)
    (R : ∀ f : ArenaZeuge.ZD.Fn, World ArenaZeuge.ZD → Env ArenaZeuge.ZD (ArenaZeuge.ZD.params f) → RufAusgang f)
    (rest : Block ArenaZeuge.ZV false [Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab)] [] []) :
    execBlock (V := ArenaZeuge.ZV) O passes R
        (Block.arenaAllocRequired ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
        (ArenaZeuge.welt 4 (by decide) (by decide)) .nil
      = .logik .kapazitaet :=
  arenaAllocRequired_an_schranke O passes R _ _ rfl _ rfl _ _ _ .nil (by decide)

end Bedeutung
end Gabbro.Grammatik
