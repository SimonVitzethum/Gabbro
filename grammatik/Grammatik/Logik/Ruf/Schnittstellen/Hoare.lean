module

public import Grammatik.Logik.Ruf.Schnittstellen.Rufstelle
public import Grammatik.Logik.Ruf.Hoare.HoareRuf

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- The indirect statement-call rule against the existing `execStmt`. The
    pointer is evaluated once in the recorded operand world. A normal outcome
    retains the concrete target's ensures and exposes the interface post with
    the same entry world, original arguments and transported actual result.
    As for `hoare_call`, this is partial correctness; it adds no termination
    or whole-body prefix claim. -/
theorem hoare_callInd (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : RespektiertVertraege P R) (hRef : PtrVerfeinert P)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (s0 : World D) (r0 : Env D Γ) :
    let target := eval s0 p s0 r0
    let ρa := evalArgs s0 args s0 r0
    STTripel (V := V) (l := l) O passes R (.callInd p args hp hr)
      (fun σ ρ => σ.lese Λ (p.orte ++ args.orte) = s0 ∧ ρ = r0 ∧
        (P.ptrVertrag n).preHolds s0 ρa)
      (fun s1 ρ' => ρ' = r0 ∧
        ∃ v, R target.val s0 (umsig target.property ρa) = RufAusgang.ok s1 v ∧
          EnsAmRueck P target.val s0 s1 (umsig target.property ρa) v ∧
          (P.ptrVertrag n).postHolds s0 s1 ρa (ptrResult target.property v)) := by
  dsimp only
  let target := eval s0 p s0 r0
  let ρa := evalArgs s0 args s0 r0
  intro σ ρ hPre s1 ρ' hrun
  obtain ⟨hworld, henv, hpre⟩ := hPre
  subst ρ
  have hreq := PtrVerfeinert.req hRef target s0 ρa hpre
  have hrun' : (match R target.val s0 (umsig target.property ρa) with
    | .ok σ' _ => Ausgang.ok (V := V) (l := l) σ' r0
    | .why _ r => keinGrundSig target.property hr r
    | .logik e => Ausgang.logik e
    | .hardware e => Ausgang.hardware e) = Ausgang.ok s1 ρ' := by
    simpa only [execStmt, hworld] using hrun
  cases hout : R target.val s0 (umsig target.property ρa) with
  | ok σ' v =>
    simp only [hout] at hrun'
    cases hrun'
    have hv := hR target.val s0 (umsig target.property ρa) hreq _ v hout
    exact ⟨rfl, v, hout, hv, PtrVerfeinert.ens hRef target s0 _ ρa v hpre hv⟩
  | why σ' r => exact keinGrundSig target.property hr r
  | logik e =>
    simp only [hout] at hrun'
    cases hrun'
  | hardware e =>
    simp only [hout] at hrun'
    cases hrun'

end Gabbro.Grammatik
