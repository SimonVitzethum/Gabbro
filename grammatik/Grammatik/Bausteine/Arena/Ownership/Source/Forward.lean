import Grammatik.Bausteine.Arena.Ownership.Source.Calls
import Grammatik.Bausteine.Arena.Ownership.Source.Parameters

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

def forwardDestructor (f g : D.Fn)
    (args : Args D (D.params f) (Signatur.anfang D (D.signatur f)) (D.params g))
    (hp : RufPasst D (vertragVon D f) (D.signatur g) (Signatur.anfang D (D.signatur f)))
    (hr : D.gruende g = 0) (he : D.erg f = none)
    (hend : (nach D g (Signatur.anfang D (D.signatur f))).Perm (vertragVon D f).ende) :
    Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  .cons (.call g args hp hr) (.ret (emptyResult f he) hend)

/-- Nested ownership forwarding is an ordinary checked G call. Its proof
works for any respecting handler, including the induction hypothesis for
recursive and mutually recursive calls. -/
theorem forwardDestructor_checked (A : FreiForm D) (C : ∀ f, Contract D f) (f g : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (y : Var (D.params g) (Ty.index (D.count A.tab)))
    (hC : C g = destructorContract A g y)
    (args : Args D (D.params f) (Signatur.anfang D (D.signatur f)) (D.params g))
    (harg : argument args y = .var x)
    (hp : RufPasst D (vertragVon D f) (D.signatur g) (Signatur.anfang D (D.signatur f)))
    (hr : D.gruende g = 0) (he : D.erg f = none)
    (hend : (nach D g (Signatur.anfang D (D.signatur f))).Perm (vertragVon D f).ende)
    (O : Orakel D) (passes : Nat)
    (R : ∀ k : D.Fn, World D → Env D (D.params k) → RufAusgang k) (hR : Respects A C R)
    (frame : Frame) (s : State) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hf : A.FreiOk σ)
    (hpre : (destructorContract A f x).requires frame s ρ) :
    (destructorContract A f x).bodyPost A frame s ρ
      (execEnd O passes R (forwardDestructor f g args hp hr he hend) σ ρ) := by
  obtain ⟨h, ho, hx⟩ := hpre
  let child : Frame := ⟨frame.thread, frame.activation + 1⟩
  obtain ⟨si, incoming, hm⟩ := State.move_exists ho (g := child) rfl
  have hmprops := State.move_valid ha.1 frame child h hm
  have hargValue : ((evalArgs (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) args (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) ρ).get y).n = h.slot := by
    rw [← eval_argument, harg]
    exact hx.symm
  have pre : (C g).requires child si (evalArgs (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) args (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) ρ) := by
    rw [hC]
    exact ⟨incoming, hmprops.2.1, hmprops.2.2.2.1.trans hargValue.symm⟩
  have post := hR g child si (σ.lese (Signatur.anfang D (D.signatur f)) args.orte)
    (evalArgs (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) args (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) ρ)
    (State.move_agrees (State.agrees_reads ha _ _) frame child h incoming hm)
    (free_invariant_reads hf _ _) pre
  simp only [forwardDestructor, execEnd, execStmt]
  cases hc : R g (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) (evalArgs (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) args (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) ρ) with
  | ok σ' v =>
    have hout := post.1 σ' v hc
    rw [hC] at hout
    obtain ⟨s', ha', hf', first, hfirst, hslot, heffect⟩ := hout
    have hid : first = incoming := State.own_handles_equal hfirst hmprops.2.1
      (hslot.trans (hmprops.2.2.2.1.trans hargValue.symm).symm)
    subst first
    refine ⟨s', State.agrees_reads ha' _ _, free_invariant_reads hf' _ _, h, ho, hx, ?_, ?_, ?_⟩
    · simpa only [hmprops.2.2.2.1] using heffect.1
    · intro j hj
      exact (heffect.2.1 j (hmprops.2.2.2.1 ▸ hj)).trans (State.move_other hm j hj)
    · have hn := heffect.2.2
      rw [State.move_next hm] at hn
      omega
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => trivial
  | hardware e => trivial

#print axioms forwardDestructor_checked

def forwardIdentity (A : FreiForm D) (f g : D.Fn)
    (args : Args D (D.params f) (Signatur.anfang D (D.signatur f)) (D.params g))
    (hf : D.erg f = some (Ty.index (D.count A.tab)))
    (hg : D.erg g = some (Ty.index (D.count A.tab)))
    (hp : RufPasst D (vertragVon D f) (D.signatur g) (Signatur.anfang D (D.signatur f)))
    (hr : D.gruende g = 0)
    (hend : (nach D g (Signatur.anfang D (D.signatur f))).Perm (vertragVon D f).ende) :
    Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) :=
  .bindCall g args hg hp hr (.ret (valueResult hf (.var .here)) hend)

theorem forwardIdentity_checked (A : FreiForm D) (C : ∀ f, Contract D f) (f g : D.Fn)
    (x : Var (D.params f) (Ty.index (D.count A.tab)))
    (y : Var (D.params g) (Ty.index (D.count A.tab)))
    (hf : D.erg f = some (Ty.index (D.count A.tab)))
    (hg : D.erg g = some (Ty.index (D.count A.tab)))
    (hC : C g = identityContract A g y hg .owned)
    (args : Args D (D.params f) (Signatur.anfang D (D.signatur f)) (D.params g))
    (harg : argument args y = .var x)
    (hp : RufPasst D (vertragVon D f) (D.signatur g) (Signatur.anfang D (D.signatur f)))
    (hr : D.gruende g = 0)
    (hend : (nach D g (Signatur.anfang D (D.signatur f))).Perm (vertragVon D f).ende)
    (O : Orakel D) (passes : Nat)
    (R : ∀ k : D.Fn, World D → Env D (D.params k) → RufAusgang k) (hR : Respects A C R)
    (frame : Frame) (s : State) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hfree : A.FreiOk σ)
    (hpre : (identityContract A f x hf .owned).requires frame s ρ) :
    (identityContract A f x hf .owned).bodyPost A frame s ρ
      (execEnd O passes R (forwardIdentity A f g args hf hg hp hr hend) σ ρ) := by
  obtain ⟨h, ho, hx⟩ := hpre
  let child : Frame := ⟨frame.thread, frame.activation + 1⟩
  have hargValue : h.slot = ((evalArgs (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) args
      (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) ρ).get y).n := by
    rw [← eval_argument, harg]
    exact hx
  simp only [forwardIdentity, execEnd]
  cases hc : R g (σ.lese (Signatur.anfang D (D.signatur f)) args.orte)
      (evalArgs (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) args
        (σ.lese (Signatur.anfang D (D.signatur f)) args.orte) ρ) with
  | ok σ' v =>
    obtain ⟨s', k, ha', hf', heffect, hvalue, _⟩ := identity_result A C R hR g y hg hC
      frame child rfl s h _ _ (State.agrees_reads ha _ _) (free_invariant_reads hfree _ _) ho hargValue hc
    refine ⟨s', State.agrees_reads ha' _ _, free_invariant_reads hf' _ _, ?_, h, k, ho, hx, heffect⟩
    let result : ErgExpr D (Ty.index (D.count A.tab) :: D.params f)
        (nach D g (Signatur.anfang D (D.signatur f))) (D.erg f) := valueResult hf (.var .here)
    let observed := σ'.lese (nach D g (Signatur.anfang D (D.signatur f))) result.orte
    have hrval := valueResult_eval hf (.var (.here : Var (Ty.index (D.count A.tab) :: D.params f) _))
      (Λ := nach D g (Signatur.anfang D (D.signatur f)))
      observed observed (Env.cons (ergWert hg v) ρ)
    exact (congrArg (fun v => v.n) hrval).trans (hvalue.symm.trans (heffect.2.1.trans hx))
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => trivial
  | hardware e => trivial

#print axioms forwardIdentity_checked

end Gabbro.Grammatik.ArenaOwnership.Source
