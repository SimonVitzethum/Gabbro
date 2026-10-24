import Grammatik.Berechenbarkeit.BrainfuckG.Kopf
import Grammatik.Berechenbarkeit.Storage.GStack.TakeOrBump

/-! Brainfuck on G, part 3: putting the head byte onto a stack. Brainfuck's `>`, `<` and `.` push the head onto one
stack (the tape behind the head, or the output). `lege` is that block in G: a cell from the free list or a fresh
one (`Block.takeOrBump`) receives the head byte and is linked on top of the stack. The arena is finite, so the
push can fail: with the free list empty and the counter at the count it runs the declared failure block, and in no
other case. On success exactly the chosen stack grows by the head byte; every other stack stays as it was. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG

open Brainfuck ArenaKette Storage.GStack

variable {D : Deklaration} {A : FreiForm D} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- A local at an equal type. -/
def varUm {τ σ : Ty} (h : τ = σ) (x : Var Γ τ) : Var Γ σ := h ▸ x

theorem get_varUm {τ σ : Ty} (h : τ = σ) (x : Var Γ τ) (ρ : Env D Γ) :
    ρ.get (varUm h x) = Wert.umTyp h (ρ.get x) := by
  subst h; rfl

/-- **`lege`**: `let i = alloc (h) else voll; link i on stack k`. -/
def lege {K : Type} (L : LinkFeld A) (G : K → LinkKopf A) (k : K) (hp : D.typ A.tab A.feld = ByteTy)
    (x : Var Γ ByteTy)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (voll : Endblock D V l Γ Λ) : Gabbro.Grammatik.Block D V l Γ Λ Λ :=
  Block.pushAllocated (Block.takeOrBump A (.var (varUm hp.symm x)) hwT hLT hwF hLF hwU hLU voll) L (G k)
    hwT hLT hwH hLH .nil

section Execution

variable (O : Orakel D) (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **A push with room**: when a freed cell exists or the counter is below the count, stack `k` grows by the head
byte, every other stack is unchanged and the free list stays well formed. -/
theorem lege_ok {K : Type} [DecidableEq K] (L : LinkFeld A) (G : K → LinkKopf A)
    (hinj : Function.Injective fun k => (G k).g) (k : K)
    (hp : D.typ A.tab A.feld = ByteTy) (x : Var Γ ByteTy)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) (vals : K → List (Wert D (D.typ A.tab A.feld)))
    (hm : MultiRep L G σ vals) (hf : A.FreiOk σ)
    (hroom : A.kopfSt σ < D.count A.tab ∨ A.stand σ < D.count A.tab) :
    ∃ σ', execBlock O passes R (lege L G k hp x hwT hLT hwF hLF hwU hLU hwH hLH voll) σ ρ = .ok σ' ρ ∧
      MultiRep L G σ' (Function.update vals k (Wert.umTyp hp.symm (ρ.get x) :: vals k)) ∧ A.FreiOk σ' := by
  have ha : ∃ slot, Allocated O passes R A
      (Block.takeOrBump A (.var (varUm hp.symm x)) hwT hLT hwF hLF hwU hLU voll) σ ρ (ρ.get (varUm hp.symm x)) slot := by
    by_cases hk : A.kopfSt σ < D.count A.tab
    · exact ⟨_, takeOrBump_reused O passes R A _ hwT hLT hwF hLF hwU hLU voll σ ρ hf hk⟩
    · have hnone : A.kopfSt σ = D.count A.tab := by have := A.kopfSt_le σ; omega
      exact ⟨_, takeOrBump_fresh O passes R A _ hwT hLT hwF hLF hwU hLU voll σ ρ hf hnone
        (hroom.resolve_left hk)⟩
  obtain ⟨slot, ha⟩ := ha
  obtain ⟨σ', kk, hexec, _, hm', hf'⟩ := push_multi O passes R _ L G hinj k hwT hLT hwH hLH σ ρ
    (ρ.get (varUm hp.symm x)) vals slot hm ha
  refine ⟨σ', ?_, by rw [get_varUm] at hm'; exact hm', hf'⟩
  unfold lege
  rw [hexec]
  rfl

/-- **Out of memory is the failure block**: with no freed cell and the counter at the count, `lege` runs `voll`. -/
theorem lege_voll {K : Type} (L : LinkFeld A) (G : K → LinkKopf A) (k : K)
    (hp : D.typ A.tab A.feld = ByteTy) (x : Var Γ ByteTy)
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwF : V.gschreibt A.kopf = true) (hLF : gdarf D A.kopf Λ)
    (hwU : V.gschreibt A.zaehl = true) (hLU : gdarf D A.zaehl Λ)
    (hwH : V.gschreibt (G k).g = true) (hLH : gdarf D (G k).g Λ)
    (voll : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hnone : A.kopfSt σ = D.count A.tab) (hfull : A.stand σ = D.count A.tab) :
    execBlock O passes R (lege L G k hp x hwT hLT hwF hLF hwU hLU hwH hLH voll) σ ρ =
      (execEnd O passes R voll ((σ.lese Λ (freeEmpty (Γ := Γ) A hLF).orte).lese Λ [Sum.inr A.zaehl]) ρ).zuAusgang :=
  takeOrBump_full O passes R A _ hwT hLT hwF hLF hwU hLU voll _ σ ρ hnone hfull

end Execution

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG
