/- The emitted image reaches a bound call inside an if and returns to its block. -/
module
public import Stage0.Senke.Bild.Block.Fenster
public import Stage0.Senke.Bild.Block.WahlLauf
public import Stage0.Senke.Bild.Rek.EmittedRueck
@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {src : String} {K : Nat} {options : Profil.Options}

/-- The image theorem for `let x = g()` at the start of a selected `if` arm.
    From the loaded image and a source-only decomposed prefix of main, the image
    reaches the call inside the branch. Its whole window is classified into entry,
    callee-body and return parts (`BlockBild`); the return endpoint binds the result
    into the remaining block, on both sides. All named machines are reachable and
    satisfy every goal leg. No memory or machine boundary inside the if is assumed. -/
theorem Emitted.bild_ziel_aufruf_im_if [Kern] (output : Emitted src K options)
    (hZ : OldSource.zertifizierbar output.compiled.unit = true) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) (hAt : ∀ g, (declOf output.compiled.unit).atomar g = false)
    {r : (declOf output.compiled.unit).Fn}
    {ρr : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params r)}
    (hRuhig : Ruhig output.compiled.program output.fsA.1 r)
    (hreqr : ReqAmEintritt output.compiled.program r (output.sp0.welt []) ρr)
    {Q : AxEns (declOf output.compiled.unit)} (hN : NutzerPflichtA (output.einheit Q))
    {O : Orakel (declOf output.compiled.unit)} (hH : HardwareAnnahmen O Q)
    [TorOK output.image.Y O] [SichtOK O] {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG output.bytes)
    {thr : Faden} {Agl : (declOf output.compiled.unit).Lock → Prop} {j : Nat}
    (hj : output.image.depth - 1 = j + 1)
    {Γ : Ctx} {Λ Λ' : List (Res (declOf output.compiled.unit))} {τ : Ty}
    {g : (declOf output.compiled.unit).Fn}
    {args : Args (declOf output.compiled.unit) Γ Λ ((declOf output.compiled.unit).params g)}
    {he : (declOf output.compiled.unit).erg g = some τ}
    {hp : RufPasst (declOf output.compiled.unit)
      (vertragVon (declOf output.compiled.unit) output.compiled.main)
      ((declOf output.compiled.unit).signatur g) Λ}
    {hrg : (declOf output.compiled.unit).gruende g = 0}
    {restB : Block (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false (τ :: Γ) (nach (declOf output.compiled.unit) g Λ) Λ'}
    {other : Block (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false Γ Λ Λ'} {cnd : Expr (declOf output.compiled.unit) Γ Λ .bool}
    {restE : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) output.compiled.main)
      false Γ Λ'}
    {σ σ2 : World (declOf output.compiled.unit)} {ρ : Env (declOf output.compiled.unit) Γ}
    {v : ErgVal (declOf output.compiled.unit) ((declOf output.compiled.unit).erg g)}
    (hk : Zerlegung (output.zRahmen O) Agl (TiefAlle output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args
      (.cons (.ite cnd (.bindCall g args he hp hrg restB) other) restE) σ ρ)
    (hcond : wahr? (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ) = true)
    (hR : rufAt output.compiled.program O output.image.passes (j + 1) g
      ((σ.lese Λ cnd.orte).lese Λ args.orte) (rufEnv g (σ.lese Λ cnd.orte) Λ args ρ) = .ok σ2 v)
    (hgT : TiefAlle output.compiled.program Agl (j + 1) g)
    {Γe : Ctx} {Λe : List (Res (declOf output.compiled.unit))}
    {ebe : Endblock (declOf output.compiled.unit) (vertragVon (declOf output.compiled.unit) g) false Γe Λe}
    {σe : World (declOf output.compiled.unit)} {ρe : Env (declOf output.compiled.unit) Γe}
    (hkC : Zerlegung (rufZRahmen output.image.Y O output.image.passes output.compiled.program output.image.A j g
      (rufWelt output.compiled.program g (σ.lese Λ cnd.orte) Λ args) (rufEnv g (σ.lese Λ cnd.orte) Λ args ρ))
      Agl (TiefAlle output.compiled.program Agl j) (output.compiled.program.rumpf g)
      (rufWelt output.compiled.program g (σ.lese Λ cnd.orte) Λ args)
      (rufEnv g (σ.lese Λ cnd.orte) Λ args ρ) ebe σe ρe) :
    ∃ (C : (declOf output.compiled.unit).Fn → List II) (Lm : Nat) (ens : List II × Nat)
      (rp : Runner.W) (n1 n2 : Nat) (pc : Runner.W) (mc : Runner.Mem)
      (Mc : RufMaschineG (declOf output.compiled.unit)),
      let B := ((output.rahmen O C Lm rp ens).suffix n1).suffix n2
      let init := RufStartG output.compiled.program output.sp0
        (bildInit thr output.compiled.main output.args r ρr)
      let Z := fun M' => RufErreichbarG output.compiled.program O output.image.passes init M' ∧
        Ziel output.compiled.program (output.einheit Q).S O output.image.passes init M'
      Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ m ⟨pc, B.fp⟩ mc ∧
      RandDannL B thr [] output.args (output.sp0.welt []) Agl (.bindCall g args he hp hrg restB)
        (.dann .nil (.ende restE)) pc mc Mc (σ.lese Λ cnd.orte) ρ ∧ Z Mc ∧
      BlockBild B Lm j g (rufWelt output.compiled.program g (σ.lese Λ cnd.orte) Λ args)
        (rufEnv g (σ.lese Λ cnd.orte) Λ args ρ) thr
        ⟨output.compiled.main, output.args, output.sp0.welt [],
          ⟨false, Γ, nach (declOf output.compiled.unit) g Λ, ρ,
            .wartet restB (.dann .nil (.ende restE))⟩⟩ [] Agl ebe σe ρe pc mc
        (fun pcN mN M3 => RandDannL B thr [] output.args (output.sp0.welt []) Agl restB
          (.schrumpf (.dann .nil (.ende restE))) pcN mN M3 σ2 (.cons (ergWert he v) ρ)) Z := by
  have hA0 := output.akzeptiertSpec Q hZ hr hg hAt hH.2.2.2
  have hL : LogikPflicht output.compiled.program (output.einheit Q).S Q := logikPflicht_of_A hN.logik
  have hmain : output.compiled.main ∈ (output.einheit Q).ws := by
    show output.compiled.main ∈ [output.compiled.main]
    exact List.mem_cons_self
  have hreq : ReqAmEintritt output.compiled.program output.compiled.main (output.sp0.welt []) output.args :=
    hN.start.req ⟨output.compiled.main, output.args⟩ (List.mem_append_left _ List.mem_cons_self)
  have hhaelt : (declOf output.compiled.unit).haelt output.compiled.main = [] := (hA0.wurzeln _ hmain).1
  have hZ' : StartZulaessig output.compiled.program (output.einheit Q).S output.fsA.1 (output.einheit Q).ws
      output.sp0 (bildInit thr output.compiled.main output.args r ρr) :=
    startZulaessig_bild hmain hRuhig hreq hreqr hN.start.sperren
  obtain ⟨C, Lm, ens, rp, pcB, mB, run0, hOk, hRand, hcodes, hdep⟩ :=
    output.bild_anfang_codes hr hg O loaded hreq
  have hSt : RandL (output.rahmen O C Lm rp ens) thr [] output.args (output.sp0.welt []) Agl
      (output.compiled.program.rumpf output.compiled.main) pcB mB
      (RufStartG output.compiled.program output.sp0 (bildInit thr output.compiled.main output.args r ρr))
      (output.sp0.welt []) output.args :=
    ⟨hRand, randGL_von (randG_start output.compiled.program output.sp0 Agl (bildInit_gleich rfl) hhaelt
      (bildInit_frei hRuhig.1))⟩
  have hk' : Zerlegung (output.rahmen O C Lm rp ens) Agl
      (TiefAlle output.compiled.program Agl (output.image.depth - 1))
      (output.compiled.program.rumpf output.compiled.main) (output.sp0.welt []) output.args
      (.cons (.ite cnd (.bindCall g args he hp hrg restB) other) restE) σ ρ := zerlegung_rahmen hk
  have hRuf := rufOk_gleich_tiefAlle (P := output.compiled.program) (O := O) (passes := output.image.passes)
    thr Agl (output.image.depth - 1)
  obtain ⟨pce, me, Me, st, hl, hRe⟩ := randL_zerlegung hOk hRuf hk' hSt
  obtain ⟨n1, n2, pc, mc, Mc, stB, hlB, hB⟩ := randL_ite_eintritt hOk hRe hcond
  have hreach := rufErreichbar_lauf (hl.trans hlB) RufErreichbarG.start
  letI : TorOK (((output.rahmen O C Lm rp ens).suffix n1).suffix n2).L
      (((output.rahmen O C Lm rp ens).suffix n1).suffix n2).O := by
    change TorOK output.image.Y O
    infer_instance
  have hwindow := randDannL_bindCall_ein_aus ((hOk.suffix n1).suffix n2) hcodes
    (by exact congrArg (rufAt output.compiled.program O output.image.passes) hj)
    (by exact congrArg (BitVec.ofNat 64) hj)
    (by exact congrArg (fun k => (k + 1) * Lm) hj)
    (by have := Nat.lt_of_le_of_lt (Nat.sub_le output.image.depth 1) hdep; omega)
    (leseblind_alle O) hB hR hgT hkC
  refine ⟨C, Lm, ens, rp, n1, n2, pc, mc, Mc, run0.trans (st.trans stB), hB,
    ⟨hreach, ziel_aus output.compiled.program (output.einheit Q).S Q output.fsA output.lsA
      (output.einheit Q).ws hA0 hL O hH output.image.passes output.sp0 _ hZ' Mc hreach⟩, ?_⟩
  exact BlockFenster.ziel hwindow hkC output.lsA hA0 hL hH hZ' hreach

#print axioms Emitted.bild_ziel_aufruf_im_if

end Gabbro.Stage0
