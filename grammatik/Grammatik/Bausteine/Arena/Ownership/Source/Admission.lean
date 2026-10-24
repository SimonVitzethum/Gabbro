import Grammatik.Bausteine.Arena.Ownership.Source.Forward

/-! Source certificates for the ownership function forms. Constructors refer
to actual G bodies and executable expression checks. No constructor accepts
a semantic ownership-preservation proposition. Unrepresented body shapes
have no certificate; this fragment is not the whole G source language. -/

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

inductive CheckedBody (A : FreiForm D) (C : ∀ f, Contract D f) (f : D.Fn) :
    Contract D f →
    Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)) → Prop where
  | identity (x : Var (D.params f) (Ty.index (D.count A.tab)))
      (he : D.erg f = some (Ty.index (D.count A.tab))) (mode : PassingMode)
      (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende) :
      CheckedBody A C f (identityContract A f x he mode) (identityBody A f x he hend)
  | destroy (x : Var (D.params f) (Ty.index (D.count A.tab))) (he : D.erg f = none)
      (hwT : (vertragVon D f).schreibt A.tab = true)
      (hLT : darf D A.tab (Signatur.anfang D (D.signatur f)))
      (hwK : (vertragVon D f).gschreibt A.kopf = true)
      (hLK : gdarf D A.kopf (Signatur.anfang D (D.signatur f)))
      (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende) :
      CheckedBody A C f (destructorContract A f x) (destructorBody A f x he hwT hLT hwK hLK hend)
  | factory (he : D.erg f = some (Ty.index (D.count A.tab))) (oom : Fin (D.gruende f))
      (ready : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool)
      (v : Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (D.typ A.tab A.feld))
      (ready_checked : checkExpression A (Context.empty (D.params f)) ready = true)
      (payload_checked : checkExpression A (Context.empty (D.params f)) v = true)
      (hwT : (vertragVon D f).schreibt A.tab = true)
      (hLT : darf D A.tab (Signatur.anfang D (D.signatur f)))
      (hwU : (vertragVon D f).gschreibt A.zaehl = true)
      (hLU : gdarf D A.zaehl (Signatur.anfang D (D.signatur f)))
      (hwF : (vertragVon D f).gschreibt A.kopf = true)
      (hLF : gdarf D A.kopf (Signatur.anfang D (D.signatur f)))
      (hLC : gdarf D A.komm (Signatur.anfang D (D.signatur f)))
      (hend : (Signatur.anfang D (D.signatur f)).Perm (vertragVon D f).ende) :
      CheckedBody A C f (factoryContract A f he)
        (factoryBody A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend)
  | forward (g : D.Fn) (x : Var (D.params f) (Ty.index (D.count A.tab)))
      (y : Var (D.params g) (Ty.index (D.count A.tab))) (hC : C g = destructorContract A g y)
      (args : Args D (D.params f) (Signatur.anfang D (D.signatur f)) (D.params g))
      (args_checked : checkArguments A (Context.parameter x .owned) args = true)
      (harg : argument args y = .var x)
      (hp : RufPasst D (vertragVon D f) (D.signatur g) (Signatur.anfang D (D.signatur f)))
      (hr : D.gruende g = 0) (he : D.erg f = none)
      (hend : (nach D g (Signatur.anfang D (D.signatur f))).Perm (vertragVon D f).ende) :
      CheckedBody A C f (destructorContract A f x) (forwardDestructor f g args hp hr he hend)
  | forwardValue (g : D.Fn) (x : Var (D.params f) (Ty.index (D.count A.tab)))
      (y : Var (D.params g) (Ty.index (D.count A.tab)))
      (hf : D.erg f = some (Ty.index (D.count A.tab)))
      (hg : D.erg g = some (Ty.index (D.count A.tab)))
      (hC : C g = identityContract A g y hg .owned)
      (args : Args D (D.params f) (Signatur.anfang D (D.signatur f)) (D.params g))
      (args_checked : checkArguments A (Context.parameter x .owned) args = true)
      (harg : argument args y = .var x)
      (hp : RufPasst D (vertragVon D f) (D.signatur g) (Signatur.anfang D (D.signatur f)))
      (hr : D.gruende g = 0)
      (hend : (nach D g (Signatur.anfang D (D.signatur f))).Perm (vertragVon D f).ende) :
      CheckedBody A C f (identityContract A f x hf .owned) (forwardIdentity A f g args hf hg hp hr hend)

theorem CheckedBody.sound (A : FreiForm D) (C : ∀ f, Contract D f) (f : D.Fn)
    (contract : Contract D f)
    (body : Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f)))
    (checked : CheckedBody A C f contract body)
    (O : Orakel D) (passes : Nat)
    (R : ∀ k : D.Fn, World D → Env D (D.params k) → RufAusgang k) (hR : Respects A C R)
    (frame : Frame) (s : State) (σ : World D) (ρ : Env D (D.params f))
    (ha : s.agrees A σ) (hf : A.FreiOk σ) (hpre : contract.requires frame s ρ) :
    contract.bodyPost A frame s ρ (execEnd O passes R body σ ρ) := by
  cases checked with
  | identity x he mode hend => exact identity_checked A f x he mode hend O passes R frame s σ ρ ha hf hpre
  | destroy x he hwT hLT hwK hLK hend =>
    exact destructor_checked A f x he hwT hLT hwK hLK hend O passes R frame s σ ρ ha hf hpre
  | factory he oom ready v _ _ hwT hLT hwU hLU hwF hLF hLC hend =>
    exact factory_checked A f he oom ready v hwT hLT hwU hLU hwF hLF hLC hend O passes R frame s σ ρ ha hf
  | forward g x y hC args _ harg hp hr he hend =>
    exact forwardDestructor_checked A C f g x y hC args harg hp hr he hend O passes R hR frame s σ ρ ha hf hpre
  | forwardValue g x y hret hg hC args _ harg hp hr hend =>
    exact forwardIdentity_checked A C f g x y hret hg hC args harg hp hr hend O passes R hR frame s σ ρ ha hf hpre

def CheckedProgram (P : Programm D) (A : FreiForm D) (C : ∀ f, Contract D f) : Prop :=
  ∀ f, CheckedBody A C f (C f) (P.rumpf f)

/-- Body obligations follow from source certificates, for every oracle,
budget, parameter environment and handler. They are not user obligations. -/
theorem checked_bodies (P : Programm D) (A : FreiForm D) (C : ∀ f, Contract D f)
    (checked : CheckedProgram P A C) (O : Orakel D) (passes : Nat) : Bodies P A C O passes := by
  intro R hR f frame s σ ρ ha hf hpre
  exact CheckedBody.sound A C f (C f) (P.rumpf f) (checked f) O passes R hR frame s σ ρ ha hf hpre

theorem checked_calls (P : Programm D) (A : FreiForm D) (C : ∀ f, Contract D f)
    (checked : CheckedProgram P A C) (O : Orakel D) (passes fuel : Nat) :
    Respects A C (rufAt P O passes fuel) :=
  rufAt_ownership P A C O passes (checked_bodies P A C checked O passes) fuel

#print axioms checked_bodies
#print axioms checked_calls

end Gabbro.Grammatik.ArenaOwnership.Source
