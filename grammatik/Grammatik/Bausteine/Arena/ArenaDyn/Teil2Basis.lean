module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Bausteine.Arena.ArenaDyn.Teil1

@[expose] public section

namespace Gabbro.Grammatik.ArenaDyn
section Form
open Gabbro.Grammatik
variable {D : Deklaration}
section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **Below the committed prefix, `alloc` does not take its `else`** -- the
    model half of the R-commit rule. The body is `ArenaZucker`'s
    `arenaRumpf`, unchanged: past the test, a dynamic arena IS a static one.
    The index bound is the OLD used counter, as there. -/
theorem dynAlloc_unter_commit (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < A.komSt σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = (execBlock O passes R (Block.arenaRumpf A.toArenaForm v hwT hLT hwG hLG rest)
          (((σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm])).lese Λ [Sum.inr A.zaehl])
          (.cons ⟨A.stand σ, A.stand_nonneg σ,
            by have := A.komSt_le σ; omega⟩ ρ)).schrumpf := by
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · exact arenaAlloc_unter_schranke O passes R A.toArenaForm v hwT hLT hwG hLG voll rest _ ρ
      (by have := A.komSt_le σ
          show A.stand σ < D.count A.tab
          omega)
  · next hno =>
      refine absurd ?_ hno
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      exact h

/-- **At or above the committed prefix, `alloc` takes its `else`** -- even
    with room to the ceiling. That is the whole difference between a
    reservation and storage: the arena is not full and the allocation is
    refused all the same, because the slot is not committed yet. -/
theorem dynAlloc_ueber_commit (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.komSt σ ≤ A.stand σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]) ρ).zuAusgang := by
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · next hja =>
      exfalso
      revert hja
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      unfold DynForm.komSt ArenaForm.stand at h
      omega
  · rfl

/-- **THE SIMULATION** (the shape PLAN-DYNAMIC section 9 fixes): a dynamic
    allocation whose index stays under its path's committed prefix runs the
    STATIC-max form -- the very same `Block.arenaAlloc` over the very same
    `ArenaForm`, on a world that differs from the dynamic one only in the
    trace (the two recorded reads of the guard). The second and third
    conjuncts are that difference, measured: the storage is the same
    storage. Every static-arena theorem therefore transfers to the right
    hand side verbatim, and growth is an observable no-op -- `dynGrow_commit`
    is the frame that says the only thing a `grow` can change about this
    equation is the guard it passes. -/
theorem dynAlloc_simuliert (A : DynForm D)
    (v : Expr D Γ Λ (D.typ A.tab A.feld))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt A.zaehl = true) (hLG : gdarf D A.zaehl Λ)
    (hLK : gdarf D A.komm Λ)
    (voll : Endblock D V l Γ Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : A.stand σ < A.komSt σ) :
    execBlock (V := V) O passes R
        (Block.dynAlloc A v hwT hLT hwG hLG hLK voll rest) σ ρ
      = execBlock O passes R (Block.arenaAlloc A.toArenaForm v hwT hLT hwG hLG voll rest)
          (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]) ρ ∧
      (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]).globs = σ.globs ∧
      (σ.lese Λ [Sum.inr A.zaehl, Sum.inr A.komm]).slots = σ.slots := by
  refine ⟨?_, rfl, rfl⟩
  simp only [Block.dynAlloc, execBlock, Block.dynUnterKomm, Expr.orte, orte_umTyp,
    List.singleton_append]
  split
  · rfl
  · next hno =>
      refine absurd ?_ hno
      simp only [eval, eval_umTyp, wahr?, World.globs_lese, decide_eq_true_eq]
      exact h

end Bedeutung


end Form

end Gabbro.Grammatik.ArenaDyn
