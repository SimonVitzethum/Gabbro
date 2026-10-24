import Grammatik.Bausteine.Arena.Ownership.Calls

/-! Generic source certificates for ownership operations. These are actual G
end blocks, not assumed foreign functions. The theorems quantify over every
declaration, argument environment, world, oracle and call handler. -/

namespace Gabbro.Grammatik.ArenaOwnership

variable {D : Deklaration}

def emptyResult (f : D.Fn) (he : D.erg f = none) {Γ : Ctx} {Λ : List (Res D)} :
    ErgExpr D Γ Λ (vertragVon D f).erg := by
  change ErgExpr D Γ Λ (D.erg f)
  rw [he]
  exact .empty

def valueResult {Γ : Ctx} {Λ : List (Res D)} {erg : Option Ty} {τ : Ty}
    (he : erg = some τ) (e : Expr D Γ Λ τ) : ErgExpr D Γ Λ erg := by
  subst he
  exact .val e

theorem valueResult_eval {Γ : Ctx} {Λ : List (Res D)} {erg : Option Ty} {τ : Ty}
    (he : erg = some τ) (e : Expr D Γ Λ τ) (σ0 σ : World D) (ρ : Env D Γ) :
    ergWert he (evalErg σ0 (valueResult he e) σ ρ) = eval σ0 e σ ρ := by
  subst he
  rfl

def identityContract (A : FreiForm D) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (he : D.erg f = some (Ty.index (D.count A.tab))) : Contract D f where
  requires := fun frame s ρ => ∃ h, s.owns frame h ∧ h.slot = (ρ.get x).n
  ensures := fun _frame s ρ s' answer =>
    match answer with
    | .value v => s' = s ∧ (ergWert he v).n = (ρ.get x).n
    | .reason _ => False

def identityBody (A : FreiForm D) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (he : D.erg f = some (Ty.index (D.count A.tab)))
    (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende) :
    Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  .ret (valueResult he (.var x)) hend

theorem identity_checked (A : FreiForm D) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (he : D.erg f = some (Ty.index (D.count A.tab)))
    (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende)
    (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    (frame : Frame) (s : State) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hf : A.FreiOk σ) :
    (identityContract A f x he).bodyPost A frame s ρ
      (execEnd O passes R (identityBody A f x he hend) σ ρ) := by
  refine ⟨s, State.agrees_reads ha _ _, free_invariant_reads hf _ _, rfl, ?_⟩
  exact congrArg (fun v => v.n) (valueResult_eval he (.var x) _ _ _)

def destructorContract (A : FreiForm D) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab))) : Contract D f where
  requires := fun frame s ρ => ∃ h, s.owns frame h ∧ h.slot = (ρ.get x).n
  ensures := fun frame s ρ s' answer =>
    match answer with
    | .value _ => ∃ h, s.owns frame h ∧ h.slot = (ρ.get x).n ∧ s.release frame h = some s'
    | .reason _ => False

/-- The ordinary source expansion of a destructor. -/
def destructorBody (A : FreiForm D) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab))) (he : D.erg f = none)
    (hwT : (vertragVon D f).schreibt A.tab = true)
    (hLT : darf D A.tab (Signatur.anfang D (D.signatur f)))
    (hwK : (vertragVon D f).gschreibt A.kopf = true)
    (hLK : gdarf D A.kopf (Signatur.anfang D (D.signatur f)))
    (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende) :
    Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  .cons (.ite .tru (Block.freiVar A x hwT hLT hwK hLK .nil) .nil)
    (.ret (emptyResult f he) hend)

/-- Discharges the destructor's body obligation from the executed free
form, including its actual parameter identity and unrelated live slots. -/
theorem destructor_checked (A : FreiForm D) (f : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab))) (he : D.erg f = none)
    (hwT : (vertragVon D f).schreibt A.tab = true)
    (hLT : darf D A.tab (Signatur.anfang D (D.signatur f)))
    (hwK : (vertragVon D f).gschreibt A.kopf = true)
    (hLK : gdarf D A.kopf (Signatur.anfang D (D.signatur f)))
    (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende)
    (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    (frame : Frame) (s : State) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (hpre : (destructorContract A f x).requires frame s ρ) :
    (destructorContract A f x).bodyPost A frame s ρ
      (execEnd O passes R (destructorBody A f x he hwT hLT hwK hLK hend) σ ρ) := by
  obtain ⟨h, hown, hslot⟩ := hpre
  obtain ⟨s', σ', hs, hr, ha', hf', _, _⟩ := release_execution O passes R A s frame h x
    hwT hLT hwK hLK (l := false) .nil (σ.lese (Signatur.anfang D (D.signatur f)) []) ρ
    (State.agrees_reads ha _ _) (free_invariant_reads hf _ _) hown hslot.symm
  change execBlock O passes R (Block.freiVar A x hwT hLT hwK hLK .nil)
    (σ.lese (Signatur.anfang D (D.signatur f)) []) ρ = .ok σ' ρ at hr
  simp only [destructorBody, execEnd, execStmt, Expr.orte, eval, wahr?, ite_true]
  rw [hr]
  exact ⟨s', State.agrees_reads ha' _ _, free_invariant_reads hf' _ _, h, hown, hslot, hs⟩

end Gabbro.Grammatik.ArenaOwnership
