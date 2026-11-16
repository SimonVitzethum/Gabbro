/- Plain direct calls share the same block window as bound calls. -/
module
public import Stage0.Senke.Bild.Block.Lauf
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- One complete statement at block position; retain the rest's fallthrough and
    both loop targets, just as `lowB` composes their code. -/
theorem BodyFrame.randBIR_schritt {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O]
    (hB : B.Ok) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)}
    {s : Stmt D (vertragVon D B.f) l Γ Λ Λ'} {rest : Block D (vertragVon D B.f) l Γ Λ' Λ''}
    {pc : Runner.W} {m : Runner.Mem} {σ σ2 : World D} {ρ ρ2 : Env D Γ}
    (h : B.RandBIR (.cons s rest) pc m σ ρ)
    (hex : execStmt B.O B.passes B.R s σ ρ = .ok σ2 ρ2) :
    ∃ (n : Nat) (m2 : Runner.Mem),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m2 ∧
      AgreeW B.L B.fp B.lo B.K m m2 ∧
      B.RandBIR rest (pc + BitVec.ofNat 64 (16 * n)) m2 σ2 ρ2 := by
  obtain ⟨c, top, hl, ht, hs, pre, hlo, hu, hk, hw, hpr, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cr, tr⟩, hcr, ⟨cs, ts⟩, hcs, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hFB : FB = 4 := rfl
  have hprefix := functionFrame_prefix B.P B.f
  have hlo0 := hB.lo0
  have ih := lowS_ok (O := B.O) (passes := B.passes) (R := B.R) (rp := B.rp) (cfp := B.cfp)
    (σ0 := B.σ0) (ρ0 := B.ρ0) (ex := exPlus B.ex cr.length) hB.spec hB.addr hB.lo0 hB.ens hB.scH
    s hH cs ts hcs (by omega) (by omega) hB.win m pc σ ρ pre.left (by omega) hlo hu hk hw hpr
  rw [hex] at ih
  obtain ⟨m2, s2, a2, e2, hw2, _⟩ := ih
  have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using pre.far)
  have pre2 : PreS B.L m2 (pc + BitVec.ofNat 64 (16 * cs.length)) B.fp B.K
      (frei Γ B.reserved) cr ρ2 B.reserved :=
    ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame a2,
      codeAt_agreeWIn hB.win a2 (codeAt_right pre.code) hf, hf, e2, trivial, wstab_true _ _⟩
  exact ⟨cs.length, m2, s2, a2, cr, tr, hcr, by omega, by omega, pre2, hlo,
    hu.agreeW hB.win a2 (by omega), hk.agreeW hB.win a2 (by omega), hw2, hpr, HeldIn.stmt s hH⟩

/-- A plain call in a block has the common direct-call prefix. -/
theorem BodyFrame.randBIR_call_site {B : BodyFrame D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D (vertragVon D B.f) l Γ (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandBIR (.cons (.call g args hp hr) rest) pc m σ ρ) : BlockCallSite B g args pc m σ ρ := by
  obtain ⟨c, top, hl, ht, _, pre, _, hu, _, hw, _, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cr, tr⟩, _, ⟨cs, ts⟩, hcs, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcs
  obtain ⟨⟨ca, ta⟩, hca, hc⟩ := hcs
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨ca, ta, hca, by omega, pre.left, hu, hw, hH⟩

/-- A plain block call, in and out on both sides, without binding a result. -/
theorem randDannL_call_ein_aus {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O]
    (hB : B.Ok) {Lm j : Nat} (hc : BildCodes B.L B.P B.passes B.A B.C Lm)
    (hRdepth : B.R = rufAt B.P B.O B.passes (j + 1))
    (hdv : B.dv = BitVec.ofNat 64 (j + 1)) (hcap : B.cap = (j + 1 + 1) * Lm)
    (hj : j + 1 < 2 ^ 64) (hO : Leseblind B.O)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params B.f)}
    {s0 : World D} {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Block D (vertragVon D B.f) l Γ (nach D g Λ) Λ'}
    {k : GRest D (vertragVon D B.f) l Γ Λ'} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ2 : World D} {ρ : Env D Γ} {v : ErgVal D (D.erg g)}
    (h : RandDannL B thr stapel rho s0 Agl (.cons (.call g args hp hr) rest) k pc m M σ ρ)
    (hR : rufAt B.P B.O B.passes (j + 1) g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v)
    (hg : TiefAlle B.P Agl (j + 1) g) {Γe : Ctx} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D g) false Γe Λe} {σe : World D} {ρe : Env D Γe}
    (hkC : Zerlegung (rufZRahmen B.L B.O B.passes B.P B.A j g (rufWelt B.P g σ Λ args)
      (rufEnv g σ Λ args ρ)) Agl (TiefAlle B.P Agl j) (B.P.rumpf g)
      (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) ebe σe ρe) :
    BlockFenster B Lm j g (rufWelt B.P g σ Λ args) (rufEnv g σ Λ args ρ) thr
      ⟨B.f, rho, s0, ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩ stapel Agl ebe σe ρe pc m M
      (fun pcN mN M3 => RandDannL B thr stapel rho s0 Agl rest k pcN mN M3 σ2 ρ) := by
  have hex : execStmt B.O B.passes B.R
      (.call g args hp hr : Stmt D (vertragVon D B.f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ2 ρ := by
    simp only [execStmt, hRdepth, hR]
  obtain ⟨n, mN, sN, _, hN⟩ := BodyFrame.randBIR_schritt hB h.1 hex
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, sI, hOk, hI⟩ :=
    BlockCallSite.eintritt hB hc hdv hcap hj hp (BodyFrame.randBIR_call_site h.1) (rufAt_ok_req hR)
  obtain ⟨M1, σm, hl1, hG, hout⟩ := randDannGL_ruf_ein_aus h.2 hR hg hkC
  have hRuf := rufOk_gleich_tiefAlle (P := B.P) (O := B.O) (passes := B.passes) thr Agl j
  obtain ⟨Me, hlP, hGe⟩ := randGL_zerlegung hO hRuf hkC hG
  obtain ⟨M2, hl2, hG2⟩ := hout hGe
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, _, mI, mN, M1, M2, σm,
    hOk, sI, hl1, ⟨hI, hG⟩, sN, hl1.trans (hlP.trans hl2), ⟨hN, hG2⟩, ?_⟩
  intro Me hMe
  obtain ⟨M3, hl3, hG3⟩ := hout hMe
  exact ⟨M3, hl3, hN, hG3⟩

end Gabbro.Stage0.Senke.BildLauf
