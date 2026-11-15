/- The fallible block-call window, with normal and reason endpoints. -/
module
public import Stage0.Senke.Bild.Block.Lauf
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- The image enters lowered end-block code while G enters its canonical block
    representation with an aborting continuation. This is the reason arm of `else`. -/
def RandAbbruchL (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D))
    (rho : Env D (D.params B.f)) (s0 : World D) (Agl : D.Lock → Prop)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (err : Endblock D (vertragVon D B.f) l Γ Λ)
    (k : GRest D (vertragVon D B.f) l Γ Λ') (pc : Runner.W) (m : Runner.Mem)
    (M : RufMaschineG D) (σ : World D) (ρ : Env D Γ) : Prop :=
  B.RandIR err pc m σ ρ ∧
    RandDannGL thr stapel B.f rho s0 Agl err.alsBlock.2 (.abbruch k) M σ ρ

/-- Fallible bound call, normal channel: bind the result and retain the success
    arm's adjusted loop targets. The error code is skipped on normal fallthrough. -/
theorem randDannL_bindCallElse_ein_aus {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O]
    (hB : B.Ok) {Lm j : Nat} (hc : BildCodes B.L B.P B.passes B.A B.C Lm)
    (hRdepth : B.R = rufAt B.P B.O B.passes (j + 1))
    (hdv : B.dv = BitVec.ofNat 64 (j + 1)) (hcap : B.cap = (j + 1 + 1) * Lm)
    (hj : j + 1 < 2 ^ 64) (hO : Leseblind B.O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ}
    {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ} {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D B.f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {k : GRest D (vertragVon D B.f) l Γ Λ'} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ2 : World D} {ρ : Env D Γ} {v : ErgVal D (D.erg g)}
    (h : RandDannL B thr stapel rho s0 Agl (.bindCallElse g args he hp hr err rest) k pc m M σ ρ)
    (hR : rufAt B.P B.O B.passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle B.P Agl (j + 1) g) {Γe : Ctx} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D g) false Γe Λe} {σe : World D} {ρe : Env D Γe}
    (hkC : Zerlegung (rufZRahmen B.L B.O B.passes B.P B.A j g (rufWelt B.P g σ Λ args)
      (rufEnv g σ Λ args ρ)) Agl (TiefAlle B.P Agl j) (B.P.rumpf g)
      (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) ebe σe ρe) :
    BlockFenster B Lm j g (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) thr
      ⟨B.f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩
      stapel Agl ebe σe ρe pc m M
      (fun pcN mN M3 => ∃ n, RandDannL (B.suffix n) thr stapel rho s0 Agl rest (.schrumpf k)
        pcN mN M3 σ2 (.cons (ergWert he v) ρ)) := by
  have hR' : B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v := by
    rw [hRdepth]
    exact hR
  obtain ⟨pcN, mN, n, sN, _, hN⟩ := BodyFrame.randBIR_bindCallElse_ok hB h.1 hR'
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, sI, hOk, hI⟩ :=
    BlockCallSite.eintritt hB hc hdv hcap hj hp (BodyFrame.randBIR_bindCallElse_site h.1) (rufAt_ok_req hR)
  obtain ⟨M1, σm, hl1, hG, hout⟩ := randDannGL_bindCallElse_ein_aus (hO.toP B.P) h.2 hR hg hkC
  have hRuf := rufOk_gleich_tiefAlle (P := B.P) (passes := B.passes) (hO.toP B.P) thr Agl j
  obtain ⟨Me, hlP, hGe⟩ := randGL_zerlegung hO hRuf hkC hG
  obtain ⟨M2, hl2, hG2⟩ := hout hGe
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, pcN, mI, mN, M1, M2, σm,
    hOk, sI, hl1, ⟨hI, hG⟩, sN, hl1.trans (hlP.trans hl2), ⟨n, hN, hG2⟩, ?_⟩
  intro Me hMe
  obtain ⟨M3, hl3, hG3⟩ := hout hMe
  exact ⟨M3, hl3, n, hN, hG3⟩

/-- Fallible bound call, reason channel: copy and bind the reason before entering
    the error end block; machine G returns through its reason pop rule. -/
theorem randDannL_bindCallElse_ein_aus_why {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O]
    (hB : B.Ok) {Lm j : Nat} (hc : BildCodes B.L B.P B.passes B.A B.C Lm)
    (hRdepth : B.R = rufAt B.P B.O B.passes (j + 1))
    (hdv : B.dv = BitVec.ofNat 64 (j + 1)) (hcap : B.cap = (j + 1 + 1) * Lm)
    (hj : j + 1 < 2 ^ 64) (hO : Leseblind B.O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ}
    {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ} {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D B.f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {k : GRest D (vertragVon D B.f) l Γ Λ'} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ2 : World D} {ρ : Env D Γ} {r : Fin (D.gruende g)}
    (h : RandDannL B thr stapel rho s0 Agl (.bindCallElse g args he hp hr err rest) k pc m M σ ρ)
    (hR : rufAt B.P B.O B.passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .why σ2 r)
    (hg : TiefAlle B.P Agl (j + 1) g) {Γe : Ctx} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D g) false Γe Λe} {σe : World D} {ρe : Env D Γe}
    (hkC : Zerlegung (rufZRahmen B.L B.O B.passes B.P B.A j g (rufWelt B.P g σ Λ args)
      (rufEnv g σ Λ args ρ)) Agl (TiefAlle B.P Agl j) (B.P.rumpf g)
      (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) ebe σe ρe) :
    BlockFenster B Lm j g (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) thr
      ⟨B.f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩
      stapel Agl ebe σe ρe pc m M
      (fun pcN mN M3 => RandAbbruchL B thr stapel rho s0 Agl err (.schrumpf k)
        pcN mN M3 σ2 (.cons r ρ)) := by
  have hR' : B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .why σ2 r := by
    rw [hRdepth]
    exact hR
  obtain ⟨pcN, mN, sN, _, hN⟩ := BodyFrame.randBIR_bindCallElse_why hB h.1 hR'
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, sI, hOk, hI⟩ :=
    BlockCallSite.eintritt hB hc hdv hcap hj hp (BodyFrame.randBIR_bindCallElse_site h.1) (rufAt_why_req hR)
  obtain ⟨M1, σm, hl1, hG, hout⟩ := randDannGL_bindCallElse_ein_aus_why (hO.toP B.P) h.2 hR hg hkC
  have hRuf := rufOk_gleich_tiefAlle (P := B.P) (passes := B.passes) (hO.toP B.P) thr Agl j
  obtain ⟨Me, hlP, hGe⟩ := randGL_zerlegung hO hRuf hkC hG
  obtain ⟨M2, hl2, hG2⟩ := hout hGe
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, pcN, mI, mN, M1, M2, σm,
    hOk, sI, hl1, ⟨hI, hG⟩, sN, hl1.trans (hlP.trans hl2), ⟨hN, hG2⟩, ?_⟩
  intro Me hMe
  obtain ⟨M3, hl3, hG3⟩ := hout hMe
  exact ⟨M3, hl3, hN, hG3⟩

#print axioms randDannL_bindCallElse_ein_aus
#print axioms randDannL_bindCallElse_ein_aus_why

end Gabbro.Stage0.Senke.BildLauf
