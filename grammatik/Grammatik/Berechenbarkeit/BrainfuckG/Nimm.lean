import Grammatik.Berechenbarkeit.BrainfuckG.Kopf
import Grammatik.Berechenbarkeit.Storage.GStack.Drain

/-! Brainfuck on G, part 2: taking a byte off a stack into the head. Brainfuck's `>`, `<` and `,` read the top of
one stack, or `0` when the stack is empty (the tape is zero beyond its ends, EOF reads as zero). `nimm` is that
statement in G: the head of the stack is compared with the empty sentinel; on empty the head local becomes `0`,
otherwise the top cell is unlinked, its payload saved into the head local and the cell released. Both outcomes
leave every other stack exactly as it was (`pop_multi`). -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG

open Brainfuck ArenaKette Storage.GStack

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- `0` at the byte type. -/
def nullByte : Expr D Γ Λ ByteTy := .widen (by decide) (by decide) (.lit 0)

/-- **`nimm`**: `if head(k) = end then h = 0 else { let v, i = pop k; h = v; free i }`. -/
def nimm {K : Type} (L : LinkFeld A) (G : K → LinkKopf A) (k : K) (hp : D.typ A.tab A.feld = ByteTy)
    (x : Var Γ ByteTy)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (failure : Endblock D V l Γ Λ) : Stmt D V l Γ Λ Λ :=
  .ite (emptyGuard (G k) hLH)
    (.cons (.assignVar x nullByte) .nil)
    (Block.popAndRelease L (G k) hwH hLH hwT hLT hwF hLF failure
      (.cons (.assignVar (.there (.there x)) (Expr.umTyp hp (.var .here))) .nil))

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- On an empty stack the head becomes `0`; no stack changes. -/
theorem nimm_leer {K : Type} [DecidableEq K] (L : LinkFeld A) (G : K → LinkKopf A) (k : K)
    (hp : D.typ A.tab A.feld = ByteTy) (x : Var Γ ByteTy)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) (vals : K → List (Wert D (D.typ A.tab A.feld)))
    (hm : MultiRep L G σ vals) (hf : A.FreiOk σ) (hk : vals k = []) :
    ∃ σ', execStmt O passes R (nimm L G k hp x hwH hLH hwT hLT hwF hLF failure) σ ρ =
        .ok σ' (ρ.set x (kodiere 0)) ∧ MultiRep L G σ' vals ∧ A.FreiOk σ' := by
  have he : (G k).st σ = D.count A.tab := Represents.empty_head (hk ▸ MultiRep.stapel hm k)
  let σ1 := σ.lese Λ (emptyGuard (Γ := Γ) (G k) hLH).orte
  refine ⟨σ1.lese Λ (nullByte (Γ := Γ) (Λ := Λ)).orte, ?_, MultiRep.lese (MultiRep.lese hm _ _) _ _,
    A.freiOk_gleich (σ := σ1) rfl (fun _ => rfl) rfl (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)⟩
  have hg : eval (σ.lese Λ (emptyGuard (Γ := Γ) (G k) hLH).orte) (emptyGuard (G k) hLH)
      (σ.lese Λ (emptyGuard (Γ := Γ) (G k) hLH).orte) ρ = true := by
    rw [emptyGuard_eval]
    exact decide_eq_true he
  simp only [nimm, execStmt, hg, wahr?, ite_true, execBlock]
  rfl

/-- On a non-empty stack the head becomes its top byte, the stack loses exactly that cell, and every other stack
stays as it was. -/
theorem nimm_voll {K : Type} [DecidableEq K] (L : LinkFeld A) (G : K → LinkKopf A)
    (hinj : Function.Injective fun k => (G k).g) (k : K)
    (hp : D.typ A.tab A.feld = ByteTy) (x : Var Γ ByteTy)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (failure : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) (vals : K → List (Wert D (D.typ A.tab A.feld)))
    (v : Wert D (D.typ A.tab A.feld)) (tl : List (Wert D (D.typ A.tab A.feld)))
    (hm : MultiRep L G σ vals) (hf : A.FreiOk σ) (hk : vals k = v :: tl) :
    ∃ σ', execStmt O passes R (nimm L G k hp x hwH hLH hwT hLT hwF hLF failure) σ ρ =
        .ok σ' (ρ.set x (Wert.umTyp hp v)) ∧ MultiRep L G σ' (Function.update vals k tl) ∧ A.FreiOk σ' := by
  have hne : (G k).st σ < D.count A.tab := Represents.nonempty (hk ▸ MultiRep.stapel hm k)
  let σ1 := σ.lese Λ (emptyGuard (Γ := Γ) (G k) hLH).orte
  have hg : eval σ1 (emptyGuard (G k) hLH) σ1 ρ = false := by
    rw [emptyGuard_eval]
    exact decide_eq_false (fun h => by
      have : (G k).st σ1 = (G k).st σ := rfl
      omega)
  let e : Expr D (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ ByteTy := Expr.umTyp hp (.var .here)
  let rest : Gabbro.Grammatik.Block D V l (D.typ A.tab A.feld :: Ty.index (D.count A.tab) :: Γ) Λ Λ :=
    .cons (.assignVar (.there (.there x)) e) .nil
  obtain ⟨σ2, kk, hpop, hm2, hf2⟩ := pop_multi O passes R L G hinj k hwH hLH hwT hLT hwF hLF failure rest σ1 ρ
    v tl vals hk (MultiRep.lese hm _ _) (A.freiOk_gleich (σ := σ) rfl (fun _ => rfl) rfl hf)
  refine ⟨σ2.lese Λ e.orte,
    ?_, MultiRep.lese hm2 _ _, A.freiOk_gleich (σ := σ2) rfl (fun _ => rfl) rfl hf2⟩
  have hg' : eval (σ.lese Λ (emptyGuard (Γ := Γ) (G k) hLH).orte) (emptyGuard (G k) hLH)
      (σ.lese Λ (emptyGuard (Γ := Γ) (G k) hLH).orte) ρ = false := hg
  simp only [nimm, execStmt, hg', wahr?, Bool.false_eq_true, ite_false]
  change execBlock O passes R (Block.popAndRelease L (G k) hwH hLH hwT hLT hwF hLF failure rest) σ1 ρ = _
  rw [hpop]
  simp only [rest, e, execBlock, execStmt, eval_umTyp, eval, Env.get_cons_here]
  rfl

end Execution

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG
