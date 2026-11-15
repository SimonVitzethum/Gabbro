/- One callee-entry proof shared by all direct call forms inside blocks. -/
module
public import Stage0.Senke.Bild.Block.Else
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- Enter the callee from a block's actual call prefix. The caller frame may carry
    enclosing locks and loop targets: only its depth word and capacity matter here.
    The result is the callee's first body boundary, after its checked prologue. -/
theorem BlockCallSite.eintritt {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O]
    (hB : B.Ok) {Lm j : Nat} (hc : BildCodes B.L B.P B.passes B.A B.C Lm)
    (hdv : B.dv = BitVec.ofNat 64 (j + 1)) (hcap : B.cap = (j + 1 + 1) * Lm)
    (hj : j + 1 < 2 ^ 64) {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn}
    {args : Args D Γ Λ (D.params g)} {pc : Runner.W} {m : Runner.Mem}
    {σ : World D} {ρ : Env D Γ}
    (hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ)
    (h : BlockCallSite B g args pc m σ ρ)
    (hreq : ReqAmEintritt B.P g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ)) :
    ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat)
      (pcI : Runner.W) (mI : Runner.Mem),
      Star ⟨pc, B.fp⟩ m ⟨pcI, fpc⟩ mI ∧
      (rumpfRahmen B.L B.O B.passes B.P B.A B.C Lm j g fpc Kc Ksc rpc B.fp
        (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) B.H ensc).Ok ∧
      (rumpfRahmen B.L B.O B.passes B.P B.A B.C Lm j g fpc Kc Ksc rpc B.fp
        (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) B.H ensc).RandIR
        (B.P.rumpf g) pcI mI (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) := by
  obtain ⟨ca, ta, hca, ht, pre, hu, hw, hH⟩ := h
  have ht' := ht
  rw [hcap] at ht'
  simp only [callTop] at ht'
  have capacity : (j + 1 + 1) * Lm ≤ B.Ks - frei Γ B.reserved := by omega
  obtain ⟨m2, s2, _, hW2, hK2, hF2, hP2, g0, g1, g2, gE, gW, gy⟩ :=
    callC_eintritt (hc.addr g) args (σ.lese Λ args.orte) hca (by omega) pre hu hB.win hw
  rw [hdv] at g2
  obtain ⟨ensc, pcI, mI, sP, hOk, hRand⟩ :=
    prolog_rand (Y := B.L) (P := B.P) (O := B.O) (passes := B.passes) (A := B.A)
      (C := B.C) (Lm := Lm) hc.fa hc.low hc.addr hc.len (k := j) hj capacity
      hW2 hK2 hF2 hP2 g0 g1 g2 gE gW gy
      (HeldIn.ruf (V := vertragVon D B.f) hH hp) hreq
  exact ⟨_, _, _, _, ensc, pcI, mI, s2.trans sP, hOk,
    BodyFrame.randIR_lese hRand (Signatur.anfang D (D.signatur g)) (B.P.requires g).orte⟩

/-- A reason answer also passed the entry contract. Failed entry contracts use the
    logic channel and cannot masquerade as a reason returned by the body. -/
theorem rufAt_why_req {P : Programm D} {O : Orakel D} {passes j : Nat} {g : D.Fn}
    {σ σ2 : World D} {ρ : Env D (D.params g)} {r : Fin (D.gruende g)}
    (h : rufAt P O passes (j + 1) g σ ρ = .why σ2 r) : ReqAmEintritt P g σ ρ :=
  Classical.byContradiction fun hn => by
    rw [rufAt_vorbed P O passes j g σ ρ hn] at h
    cases h

#print axioms BlockCallSite.eintritt

end Gabbro.Stage0.Senke.BildLauf
