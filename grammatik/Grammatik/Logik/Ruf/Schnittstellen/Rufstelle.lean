module

public import Grammatik.Logik.Ruf.Schnittstellen.Vertrag
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt.T1

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}

/-- The local interface duty shared by statement, block-binding and end-binding
    indirect calls. Its world is exactly the operand-entry world of `execStmt`,
    `execBlock` and `execEnd`, after recording pointer and argument reads.
    A whole-body prefix judgment must establish this at every executed site;
    this local predicate does not assume anything about reachable machines. -/
def PtrRufPflicht (P : Programm D) (p : Expr D Γ Λ (.fnptr n))
    (args : Args D Γ Λ (D.sigNr n).params) (σ : World D) (ρ : Env D Γ) : Prop :=
  let s0 := σ.lese Λ (p.orte ++ args.orte)
  (P.ptrVertrag n).preHolds s0 (evalArgs s0 args s0 ρ)

/-- The interface duty and universal refinement establish the actual selected
    function's requires at exactly the world and arguments used by dispatch.
    No lookup by signature number replaces the runtime-selected function. -/
theorem PtrRufPflicht.req {P : Programm D} (hR : PtrVerfeinert P)
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {σ : World D} {ρ : Env D Γ} (h : PtrRufPflicht P p args σ ρ) :
    let s0 := σ.lese Λ (p.orte ++ args.orte)
    let target := eval s0 p s0 ρ
    ReqAmEintritt P target.val s0 (umsig target.property (evalArgs s0 args s0 ρ)) :=
  PtrVerfeinert.req hR _ _ _ h

/-- The concrete caller gate opens because the selected target's own requires
    follows from O43. The selected handler, body and result remain unchanged. -/
theorem PtrRufPflicht.torRuf {P : Programm D} (hR : PtrVerfeinert P)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {σ : World D} {ρ : Env D Γ} (h : PtrRufPflicht P p args σ ρ) :
    let s0 := σ.lese Λ (p.orte ++ args.orte)
    let target := eval s0 p s0 ρ
    torRuf P R target.val s0 (umsig target.property (evalArgs s0 args s0 ρ)) =
      R target.val s0 (umsig target.property (evalArgs s0 args s0 ρ)) := by
  dsimp only
  unfold torRuf
  exact if_pos (PtrRufPflicht.req hR h)

/-- At a normal return, expose the interface post while retaining the concrete
    ensures as a separate fact. Reason exits supply no premise of this shape. -/
theorem PtrRufPflicht.ens {P : Programm D} (hR : PtrVerfeinert P)
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {σ : World D} {ρ : Env D Γ} (h : PtrRufPflicht P p args σ ρ)
    (s1 : World D)
    (v : ErgVal D (D.erg (eval (σ.lese Λ (p.orte ++ args.orte)) p
      (σ.lese Λ (p.orte ++ args.orte)) ρ).val))
    (hv : let s0 := σ.lese Λ (p.orte ++ args.orte)
      let target := eval s0 p s0 ρ
      EnsAmRueck P target.val s0 s1 (umsig target.property (evalArgs s0 args s0 ρ)) v) :
    let s0 := σ.lese Λ (p.orte ++ args.orte)
    let target := eval s0 p s0 ρ
    (P.ptrVertrag n).postHolds s0 s1 (evalArgs s0 args s0 ρ) (ptrResult target.property v) :=
  PtrVerfeinert.ens hR _ _ _ _ v h hv

/-- Concrete return logs retain the selected function's full contract. O43
    projects an interface post from that logged fact and the interface pre;
    it does not substitute an interface stub into machine G. -/
theorem ptrPost_of_vertragAmOrtG {P : Programm D} (hR : PtrVerfeinert P)
    {M : RufMaschineG D} (hV : VertragAmOrtG P M) (thread : Faden)
    (p : Wert D (.fnptr n)) (s0 s1 : World D) (ρ : Env D (D.sigNr n).params)
    (v : ErgVal D (D.erg p.val)) (hp : (P.ptrVertrag n).preHolds s0 ρ)
    (hev : RufEreignisF.rueck p.val (umsig p.property ρ) v s0 s1 ∈
      (M.faeden thread).log) :
    (P.ptrVertrag n).postHolds s0 s1 ρ (ptrResult p.property v) := by
  have hv := (hV thread _ hev).2 p.val (umsig p.property ρ) v s0 s1 rfl
  exact PtrVerfeinert.ens hR p s0 s1 ρ v hp hv

end Gabbro.Grammatik
