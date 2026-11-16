/- Calls inside blocks, in and out on both the image and machine G. -/
module
public import Stage0.Senke.Bild.Block.Eintritt
public import Stage0.Senke.Bild.Block.Praefix
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- A whole call window, with a fixed image endpoint and the actual waiting caller.
    The image reaches the callee's first boundary; from every boundary behind the
    callee's decomposed prefix, machine G returns to the same caller continuation.
    `out` describes either a result-bound block or a reason-bound error end block. -/
def BlockFenster (B : BodyFrame D) (Lm j : Nat) (g : D.Fn) (σc : World D)
    (ρc : Env D (D.params g)) (thr : Faden) (caller : RufRahmenG D)
    (stapel : List (RufRahmenG D)) (Agl : D.Lock → Prop)
    {Γe : Ctx} {Λe : List (Res D)} (ebe : Endblock D (vertragVon D g) false Γe Λe)
    (σe : World D) (ρe : Env D Γe) (pc : Runner.W) (m : Runner.Mem) (M : RufMaschineG D)
    (out : Runner.W → Runner.Mem → RufMaschineG D → Prop) : Prop :=
  ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat)
    (pcI pcN : Runner.W) (mI mN : Runner.Mem) (M1 M2 : RufMaschineG D) (σm : World D),
    let Bc := rumpfRahmen B.L B.O B.passes B.P B.A B.C Lm j g fpc Kc Ksc rpc B.fp σc ρc B.H ensc
    Bc.Ok ∧ Star ⟨pc, B.fp⟩ m ⟨pcI, fpc⟩ mI ∧
    RufLaufG B.P B.O B.passes thr M M1 ∧ RandL Bc thr (caller :: stapel) ρc σm Agl
      (B.P.rumpf g) pcI mI M1 σc ρc ∧
    Star ⟨pc, B.fp⟩ m ⟨pcN, B.fp⟩ mN ∧ RufLaufG B.P B.O B.passes thr M M2 ∧ out pcN mN M2 ∧
    ∀ {Me : RufMaschineG D}, RandGL thr (caller :: stapel) g ρc σm Agl ebe Me σe ρe →
      ∃ M3, RufLaufG B.P B.O B.passes thr Me M3 ∧ out pcN mN M3

/-- A bound call in a block, on both sides. The image's endpoint includes the result
    store; the machine's endpoint includes the pop and context-shrinking continuation. -/
theorem randDannL_bindCall_ein_aus {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O]
    (hB : B.Ok) {Lm j : Nat} (hc : BildCodes B.L B.P B.passes B.A B.C Lm)
    (hRdepth : B.R = rufAt B.P B.O B.passes (j + 1))
    (hdv : B.dv = BitVec.ofNat 64 (j + 1)) (hcap : B.cap = (j + 1 + 1) * Lm)
    (hj : j + 1 < 2 ^ 64) (hO : Leseblind B.O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ}
    {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {k : GRest D (vertragVon D B.f) l Γ Λ'} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ2 : World D} {ρ : Env D Γ} {v : ErgVal D (D.erg g)}
    (h : RandDannL B thr stapel rho s0 Agl (.bindCall g args he hp hr rest) k pc m M σ ρ)
    (hR : rufAt B.P B.O B.passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle B.P Agl (j + 1) g) {Γe : Ctx} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D g) false Γe Λe} {σe : World D} {ρe : Env D Γe}
    (hkC : Zerlegung (rufZRahmen B.L B.O B.passes B.P B.A j g (rufWelt B.P g σ Λ args)
      (rufEnv g σ Λ args ρ)) Agl (TiefAlle B.P Agl j) (B.P.rumpf g)
      (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) ebe σe ρe) :
    BlockFenster B Lm j g (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) thr
      ⟨B.f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩ stapel Agl ebe σe ρe pc m M
      (fun pcN mN M3 => RandDannL B thr stapel rho s0 Agl rest (.schrumpf k)
        pcN mN M3 σ2 (.cons (ergWert he v) ρ)) := by
  have hR' : B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v := by
    rw [hRdepth]
    exact hR
  obtain ⟨n, mN, sN, _, _, hN⟩ := BodyFrame.randBIR_bindCall hB h.1 hR'
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, sI, hOk, hI⟩ :=
    BlockCallSite.eintritt hB hc hdv hcap hj hp (BodyFrame.randBIR_bindCall_site h.1) (rufAt_ok_req hR)
  obtain ⟨M1, σm, hl1, hG, hout⟩ := randDannGL_bindCall_ein_aus h.2 hR hg hkC
  have hRuf := rufOk_gleich_tiefAlle (P := B.P) (O := B.O) (passes := B.passes) thr Agl j
  obtain ⟨Me, hlP, hGe⟩ := randGL_zerlegung
    (B := rufZRahmen B.L B.O B.passes B.P B.A j g
      (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ)) hO hRuf hkC hG
  obtain ⟨M2, hl2, hG2⟩ := hout hGe
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, _, mI, mN, M1, M2, σm,
    hOk, sI, hl1, ⟨hI, hG⟩, sN, hl1.trans (hlP.trans hl2), ⟨hN, hG2⟩, ?_⟩
  intro Me hMe
  obtain ⟨M3, hl3, hG3⟩ := hout hMe
  exact ⟨M3, hl3, hN, hG3⟩

#print axioms randDannL_bindCall_ein_aus

end Gabbro.Stage0.Senke.BildLauf
