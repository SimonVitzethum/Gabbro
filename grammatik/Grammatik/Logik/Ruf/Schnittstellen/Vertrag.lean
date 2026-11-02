module

public import Grammatik.Logik.Vertraege.VertragOrtB

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

namespace CallContract

variable {S : Signatur D.Tab D.Glob D.Lock D.Marke}

/-- The interface precondition at the operand-entry world and actual arguments. -/
def preHolds (C : CallContract D S) (s0 : World D) (ρ : Env D S.params) : Prop :=
  wahr? (eval s0 C.pre s0 ρ) = true

/-- A normal interface return, with separate entry/current worlds, the original
    arguments and the actual optional result. Reason exits have no normal post. -/
def postHolds (C : CallContract D S) (s0 s1 : World D) (ρ : Env D S.params)
    (v : ErgVal D S.erg) : Prop :=
  wahr? (eval s0 C.post s1 (ergEnv S.erg v ρ)) = true

theorem trivial_pre (s0 : World D) (ρ : Env D S.params) :
    (CallContract.trivial D S).preHolds s0 ρ := rfl

theorem trivial_post (s0 s1 : World D) (ρ : Env D S.params) (v : ErgVal D S.erg) :
    (CallContract.trivial D S).postHolds s0 s1 ρ v := rfl

end CallContract

/-- Transport the actual target result to its structurally matching interface.
    This changes only its type, without decoding or synthesizing a value. -/
def ptrResult {f : D.Fn} {n : Nat} (hf : D.passt f n = true)
    (v : ErgVal D (D.erg f)) : ErgVal D (D.sigNr n).erg :=
  cast (congrArg (ErgVal D) (D.passt_sig hf).erg) v

/-- O43 for one admitted target. Requires is contravariant; ensures is
    covariant and conditional on the same interface precondition. The two
    worlds, arguments and return value are arbitrary, independent of a body
    execution or an enumeration of observed targets. -/
def PtrZielVerfeinert (P : Programm D) (f : D.Fn) (n : Nat)
    (hf : D.passt f n = true) : Prop :=
  (∀ (s0 : World D) (ρ : Env D (D.sigNr n).params),
    (P.ptrVertrag n).preHolds s0 ρ → ReqAmEintritt P f s0 (umsig hf ρ)) ∧
  (∀ (s0 s1 : World D) (ρ : Env D (D.sigNr n).params) (v : ErgVal D (D.erg f)),
    (P.ptrVertrag n).preHolds s0 ρ → EnsAmRueck P f s0 s1 (umsig hf ρ) v →
      (P.ptrVertrag n).postHolds s0 s1 ρ (ptrResult hf v))

/-- Universal target refinement. Every route to a pointer value uses the same
    `D.passt`: address-taking, stored/parameter/result pointers and oracle
    decoding are all covered, including targets absent from a particular run.
    Structural conformance and exporter success do not establish this duty. -/
def PtrVerfeinert (P : Programm D) : Prop :=
  ∀ (f : D.Fn) (n : Nat) (hf : D.passt f n = true), PtrZielVerfeinert P f n hf

/-- Select O43 using the evidence already carried by a function-pointer value. -/
theorem PtrVerfeinert.req {P : Programm D} (h : PtrVerfeinert P) {n : Nat}
    (p : Wert D (.fnptr n)) (s0 : World D) (ρ : Env D (D.sigNr n).params)
    (hp : (P.ptrVertrag n).preHolds s0 ρ) :
    ReqAmEintritt P p.val s0 (umsig p.property ρ) :=
  (h p.val n p.property).1 s0 ρ hp

/-- The interface post follows from the selected target's own normal ensures.
    Its concrete contract remains available; no target contract is replaced. -/
theorem PtrVerfeinert.ens {P : Programm D} (h : PtrVerfeinert P) {n : Nat}
    (p : Wert D (.fnptr n)) (s0 s1 : World D) (ρ : Env D (D.sigNr n).params)
    (v : ErgVal D (D.erg p.val)) (hp : (P.ptrVertrag n).preHolds s0 ρ)
    (hv : EnsAmRueck P p.val s0 s1 (umsig p.property ρ) v) :
    (P.ptrVertrag n).postHolds s0 s1 ρ (ptrResult p.property v) :=
  (h p.val n p.property).2 s0 s1 ρ v hp hv

end Gabbro.Grammatik
