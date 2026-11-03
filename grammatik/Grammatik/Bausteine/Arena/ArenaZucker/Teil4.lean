module

public import Grammatik.Bausteine.Arena.ArenaZucker.Teil1

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## C18 end-block allocation

    The end-block halves of `Block.arenaAlloc`/`Block.arenaAllocRequired`: the same
    typed narrowing of the arena counter, the same shared store-and-bump body, with
    an end-block rest -- for an allocation that is the last binding of a body (or of
    an `else` branch that must not fall through). Below the hard bound the body runs
    exactly as in the block form; at the bound the `else` branch runs (or the outcome
    is the logical capacity failure `Logik.kapazitaet` for the required form,
    excluded by the caller's capacity duty). No `Spec.lean` change: the static arena
    commits all its slots, so no provider or committed-storage availability beyond
    the counter bound is owed; OOM stays user logic and an arena's `else` at its
    declared ceiling is a capacity bound. -/

namespace Endblock
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The body of an end-block allocation: the store, then the bump, ending in an
    end block. Named, because all four theorems below speak about it. -/
def arenaRumpf (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ) :
    Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ :=
  .cons (.assignSlot A.tab A.feld (Expr.var .here) (Expr.weaken v) hwT hLT)
    (.cons (.assignGlob A.zaehl (Block.arenaBump A) hwG hLG) rest)

/-- **`let i = alloc A (v) else B; …` at the end of a body** -- `Block.arenaAlloc`
    with an end-block rest: the counter narrowing into `0 ..< hi` with the `else`
    branch `B`, then the shared store-and-bump body. -/
def arenaAlloc (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ) :
    Endblock D V l Γ Λ :=
  .narrow (Expr.umTyp A.hz (Expr.glob A.zaehl hLG)) 0 (D.count A.tab - 1) voll
    (arenaRumpf A v hwT hLT hwG hLG rest)

/-- **`let i = allocRequired A (v); …` at the end of a body** --
    `Block.arenaAllocRequired` with an end-block rest: the required narrowing of
    the counter into `0 ..< hi`, then the shared store-and-bump body. Full is a
    logical failure, never a silent wrap. -/
def arenaAllocRequired (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ) :
    Endblock D V l Γ Λ :=
  .narrowRequired (Expr.umTyp A.hz (Expr.glob A.zaehl hLG)) 0 (D.count A.tab - 1)
    (arenaRumpf A v hwT hLT hwG hLG rest)

end Endblock

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **Below the hard bound, an end-block `alloc` does not take its `else`** -- the
    end-block half of `arenaAlloc_unter_schranke`, mirroring it with no `else` to
    take. -/
theorem arenaAllocEnd_unter_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < D.count A.tab) :
    execEnd (V := V) O passes R
        (Endblock.arenaAlloc A v hwT hLT hwG hLG voll rest) σ ρ
      = (execEnd O passes R (Endblock.arenaRumpf A v hwT hLT hwG hLG rest)
          (σ.lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ, by omega⟩ ρ)).schrumpf := by
  have hc : (0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1 :=
    ⟨A.stand_nonneg σ, by have := h; unfold ArenaForm.stand at this; omega⟩
  simp only [Endblock.arenaAlloc, execEnd, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_pos hc]
  rfl

#print axioms arenaAllocEnd_unter_schranke

/-- **At the hard bound, an end-block `alloc` takes its `else`** -- the full arena
    is the branch the surface `else` names; the declared ceiling refuses the store,
    and the `else` path is the only continuation. -/
theorem arenaAllocEnd_an_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ = D.count A.tab) :
    execEnd (V := V) O passes R
        (Endblock.arenaAlloc A v hwT hLT hwG hLG voll rest) σ ρ
      = execEnd O passes R voll (σ.lese Λ [Sum.inr A.zaehl]) ρ := by
  have hp := A.hpos
  have hn : ¬ ((0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1) := by
    have := h; unfold ArenaForm.stand at this; omega
  simp only [Endblock.arenaAlloc, execEnd, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_neg hn]

#print axioms arenaAllocEnd_an_schranke

/-- **Below the hard bound, a required end-block allocation runs its body** -- the
    syntactic half of the capacity duty, mirroring `arenaAllocRequired_unter_schranke`
    with no `else` to take. -/
theorem arenaAllocRequiredEnd_unter_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < D.count A.tab) :
    execEnd (V := V) O passes R
        (Endblock.arenaAllocRequired A v hwT hLT hwG hLG rest) σ ρ
      = (execEnd O passes R (Endblock.arenaRumpf A v hwT hLT hwG hLG rest)
          (σ.lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ, by omega⟩ ρ)).schrumpf := by
  have hc : (0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1 :=
    ⟨A.stand_nonneg σ, by have := h; unfold ArenaForm.stand at this; omega⟩
  simp only [Endblock.arenaAllocRequired, execEnd, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_pos hc]
  rfl

#print axioms arenaAllocRequiredEnd_unter_schranke

/-- **At the hard bound, a required end-block allocation is a capacity failure** --
    a full arena at a required allocation is `Logik.kapazitaet`, never a silent
    wrap, a fabricated value or a hardware failure; the caller's `KoerperGutS/SA`
    duty excludes exactly this outcome. The declared ceiling refuses the store. -/
theorem arenaAllocRequiredEnd_an_schranke (A : ArenaForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (rest : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ = D.count A.tab) :
    execEnd (V := V) O passes R
        (Endblock.arenaAllocRequired A v hwT hLT hwG hLG rest) σ ρ
      = .logik .kapazitaet := by
  have hp := A.hpos
  have hn : ¬ ((0 : Int) ≤ (Wert.umTyp A.hz (σ.globs A.zaehl)).n ∧
      (Wert.umTyp A.hz (σ.globs A.zaehl)).n ≤ D.count A.tab - 1) := by
    have := h; unfold ArenaForm.stand at this; omega
  simp only [Endblock.arenaAllocRequired, execEnd, eval_umTyp, orte_umTyp, eval, Expr.orte,
    World.globs_lese]
  rw [dif_neg hn]

#print axioms arenaAllocRequiredEnd_an_schranke

/-- **The `else` branch is not taken on the empty arena, and the index is `0`.** -/
theorem zeuge_alloc_leer_end (O : Orakel ArenaZeuge.ZD) (passes : Nat)
    (R : ∀ f : ArenaZeuge.ZD.Fn, World ArenaZeuge.ZD → Env ArenaZeuge.ZD (ArenaZeuge.ZD.params f) → RufAusgang f)
    (voll : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [] [])
    (rest : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab)] []) :
    execEnd (V := ArenaZeuge.ZV) O passes R
        (Endblock.arenaAlloc ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll rest)
        (ArenaZeuge.welt 0 (by decide) (by decide)) .nil
      = (execEnd O passes R
          (Endblock.arenaRumpf ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
          ((ArenaZeuge.welt 0 (by decide) (by decide)).lese [] [Sum.inr ()])
          (.cons ⟨0, by decide, by decide⟩ .nil)).schrumpf :=
  arenaAllocEnd_unter_schranke O passes R ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll rest _ .nil (by decide)

/-- **And it IS taken on the full one** -- the ceiling refuses the store, and the
    `else` path is the only continuation. -/
theorem zeuge_alloc_voll_end (O : Orakel ArenaZeuge.ZD) (passes : Nat)
    (R : ∀ f : ArenaZeuge.ZD.Fn, World ArenaZeuge.ZD → Env ArenaZeuge.ZD (ArenaZeuge.ZD.params f) → RufAusgang f)
    (voll : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [] [])
    (rest : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab)] []) :
    execEnd (V := ArenaZeuge.ZV) O passes R
        (Endblock.arenaAlloc ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll rest)
        (ArenaZeuge.welt 4 (by decide) (by decide)) .nil
      = execEnd O passes R voll
          ((ArenaZeuge.welt 4 (by decide) (by decide)).lese [] [Sum.inr ()]) .nil :=
  arenaAllocEnd_an_schranke O passes R ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf voll rest _ .nil (by decide)

/-- **The required end-block allocation stores at index `0` on the empty arena.** -/
theorem zeuge_allocRequired_leer_end (O : Orakel ArenaZeuge.ZD) (passes : Nat)
    (R : ∀ f : ArenaZeuge.ZD.Fn, World ArenaZeuge.ZD → Env ArenaZeuge.ZD (ArenaZeuge.ZD.params f) → RufAusgang f)
    (rest : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab)] []) :
    execEnd (V := ArenaZeuge.ZV) O passes R
        (Endblock.arenaAllocRequired ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
        (ArenaZeuge.welt 0 (by decide) (by decide)) .nil
      = (execEnd O passes R
          (Endblock.arenaRumpf ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
          ((ArenaZeuge.welt 0 (by decide) (by decide)).lese [] [Sum.inr ()])
          (.cons ⟨0, by decide, by decide⟩ .nil)).schrumpf :=
  arenaAllocRequiredEnd_unter_schranke O passes R ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest _ .nil (by decide)

/-- **And on the full arena it is a capacity failure, never a wrap** -- the ceiling
    refuses the store; no success continuation can be confused with the failure. -/
theorem zeuge_allocRequired_voll_end (O : Orakel ArenaZeuge.ZD) (passes : Nat)
    (R : ∀ f : ArenaZeuge.ZD.Fn, World ArenaZeuge.ZD → Env ArenaZeuge.ZD (ArenaZeuge.ZD.params f) → RufAusgang f)
    (rest : Endblock ArenaZeuge.ZD ArenaZeuge.ZV false [Ty.index (ArenaZeuge.ZD.count ArenaZeuge.Log.tab)] []) :
    execEnd (V := ArenaZeuge.ZV) O passes R
        (Endblock.arenaAllocRequired ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest)
        (ArenaZeuge.welt 4 (by decide) (by decide)) .nil
      = .logik .kapazitaet :=
  arenaAllocRequiredEnd_an_schranke O passes R ArenaZeuge.Log ArenaZeuge.sieben rfl ArenaZeuge.zeuge_darf rfl ArenaZeuge.zeuge_gdarf rest _ .nil (by decide)

end Bedeutung
end Gabbro.Grammatik
