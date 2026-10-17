/- Part 2 of 5 of `KorrespondenzAllg` (split by instrumente/teile/lean-teilen.py; the umbrella `KorrespondenzAllg.lean` imports all parts). -/
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ### The DEVICE: one named premise, and the three step judgements

    A volatile access is not memory. `corrW` -- the relation every judgement of
    pass (i) carries -- relates the C memory to the Gabbro world, and a device
    window is neither (CFormenH.lean, CUTS: *"device windows are not in the
    relation"*). Everything a device row needs beyond the row itself is
    therefore collected in ONE named premise, `GerAnnahme`, and that premise
    travels with the theorem: it is not decided, not derived and not hidden.

    **WHAT A DEVICE CHAIN CLAIMS, in one sentence:** *if the profile holds and
    the register answers inside its declared type, every run of the emitted C
    corresponds to the model's register step.* It claims NOTHING about what the
    device does -- neither that it answers, nor that it answers the truth, nor
    that it keeps the promise its declaration states. Where the answer does not
    fit the declared type (`Hardware.register`) or breaks the declared promise
    (`Hardware.geraet`), the Gabbro side ends in an ERROR and the
    correspondence says nothing at all: that is the residue, and it stands
    where the reader can see it. -/

section Geraet

/-- **THE HARDWARE PROFILE** of a certificate's device table -- the six facts
    the check cannot decide, as ONE premise. Two of them (`fenster`, `passt`)
    are about the emitted layout, two (`lebt`, `adr`) about the platform, one
    (`einig`) is the `hdev` premise of `regLies_step` lifted from one program
    point to the whole unit, and one (`rund`) is a property of the register's
    declared TYPE. -/
structure GerAnnahme (EL : EmitLay D) (orc : DevOrc) (O : Orakel D) (GT : GerTafel D) : Prop where
  /-- (G1) THE WINDOW. Every register sits at its offset in a block the layout
      declares `mmio`, in a cell of exactly the declared width, and that block
      is one the emitted unit DECLARES as a device window (`EmitLay.devs`) --
      which is what makes it mapped in every related state (`corrW`'s third
      clause). *That clause is the one line of this work that is not in the
      certificate*: a device window is not memory, and that it is there at all
      is the platform's word, carried in the relation next to the liveness of
      every table and global. -/
  fenster : GT.ein = true → ∀ r : D.Reg, ∃ B : BlkLay, EL.lay (.dev (GT.dnr r)) = some B ∧
      B.kind = .mmio ∧ B.lay.cell (GT.off r) = some (.int false (GT.wid r)) ∧
      EL.devs (GT.dnr r) = true
  /-- (G3) THE ADDRESS. Every address expression the check ACCEPTS for `r`
      evaluates to `r`'s cell, in every state and frame, touching neither
      memory nor the trace. For the `(volatile uint8_t *)(uintptr_t)BASE + K`
      spelling this is a THEOREM (`ev_devReg`, discharged by
      `gerAdr_devH`); for the emitter's own `d->basis + K` it is the
      assumption that the handle local carries the window's base. -/
  adr : ∀ (r : D.Reg) (cp : CX), regAdrOk GT cp r = true →
      ∀ (fr : Nat) (st : CSt) (ρC : CLok),
        ev EL.lay orc fr cp st ρC = some (.ptr ⟨.dev (GT.dnr r), (GT.off r : Int)⟩, st)
  /-- (G4) THE DECLARED TYPE FITS THE CELL. -/
  passt : GT.ein = true → ∀ r : D.Reg, tyFits (D.rtyp r) (.int false (GT.wid r)) = true
  /-- (G5) ONE DEVICE, TWO ORACLES. The C device oracle and Gabbro's
      `Orakel.regLies` answer the same machine. This is `regLies_step`'s
      `hdev`, lifted from one program point to the profile. -/
  einig : GT.ein = true → ∀ (r : D.Reg) (σ : World D) (st : CSt),
      cWrap (GT.wid r) (orc st.obs ⟨.dev (GT.dnr r), (GT.off r : Int)⟩
        (.int false (GT.wid r))) = O.regLies r σ
  /-- (G6) THE ANSWER READS BACK. WHERE the raw word fits the declared type,
      its decoding encodes back to it. A property of the register's TYPE and
      not of the device: for an integer register it is `rfl`
      (`gerRund_int`); a `bool` register cannot meet it, and that is a
      refusal by name, not a silent admission. -/
  rund : GT.ein = true → ∀ (r : D.Reg) (σ : World D) (v : Wert D (D.rtyp r)),
      einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v →
      encW (D.rtyp r) v = O.regLies r σ

/-- **THE EMPTY DEVICE TABLE MEETS THE PROFILE**, and meets it with nothing:
    no device row is admitted under it, so every one of the five facts is
    vacuous. This is what the two closed chains pass, and it is why the
    generic theorem lost NO hypothesis it had before 2026-09-16. -/
theorem gerAnn_leer (EL : EmitLay D) (orc : DevOrc) (O : Orakel D) {GT : GerTafel D}
    (h : GT.ein = false) : GerAnnahme EL orc O GT where
  fenster := by intro he; rw [h] at he; exact absurd he (by simp)
  adr := by
    intro r cp hadr
    have he := regAdrOk_ein hadr
    rw [h] at he
    exact absurd he (by simp)
  passt := by intro he; rw [h] at he; exact absurd he (by simp)
  einig := by intro he; rw [h] at he; exact absurd he (by simp)
  rund := by intro he; rw [h] at he; exact absurd he (by simp)

variable {EL : EmitLay D} {orc : DevOrc} {O : Orakel D} {GT : GerTafel D}

/-- (G3) IS A THEOREM FOR THE DIRECT-BASE SPELLING. `ev_devReg` (CFormenH.lean)
    settles `(volatile uint8_t *)(uintptr_t)BASE + K` outright, provided the
    table's base is the window's and the offset inside it. Only the emitter's
    handle spelling `d->basis + K` needs the assumption. -/
theorem gerAdr_devH (hF : ∀ r : D.Reg, ∃ B : BlkLay, EL.lay (.dev (GT.dnr r)) = some B ∧
      B.kind = .mmio ∧ B.base = GT.basis r ∧ GT.off r ≤ B.lay.size)
    (r : D.Reg) (fr : Nat) (st : CSt) (ρC : CLok) :
    ev EL.lay orc fr (.padd (.devH (GT.dnr r) (GT.basis r)) (.lit (GT.off r))) st ρC =
      some (.ptr ⟨.dev (GT.dnr r), (GT.off r : Int)⟩, st) := by
  obtain ⟨B, hL, hk, hb, hs⟩ := hF r
  have := ev_devReg EL.lay orc fr (GT.dnr r) B hL hk (GT.off r) hs st ρC
  rwa [hb] at this

/-- (G6) IS A THEOREM FOR AN INTEGER REGISTER: `einpassen` at `.int lo hi`
    hands back the word it was given, and `encW` is the identity on it. -/
theorem gerRund_int {r : D.Reg} {lo hi : Int} (hty : D.rtyp r = .int lo hi)
    (σ : World D) (v : Wert D (D.rtyp r))
    (h : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v) :
    encW (D.rtyp r) v = O.regLies r σ := by
  revert v
  rw [hty]
  intro v h
  show Zahl.n v = O.regLies r σ
  have he : einpassen O.zeiger (Ty.int lo hi) (O.regLies r σ) =
      if hh : lo ≤ O.regLies r σ ∧ O.regLies r σ ≤ hi then
        some ⟨O.regLies r σ, hh.1, hh.2⟩ else Option.none := rfl
  rw [he] at h
  split at h
  · injection h with h'
    subst h'
    rfl
  · exact absurd h (by simp)

/-- The access check at a register's cell, out of the profile. -/
theorem gerAcc (hP : GerAnnahme EL orc O GT) (hein : GT.ein = true) (r : D.Reg)
    {σ : World D} {st : CSt} (hc : corrW EL σ st) :
    accOk EL.lay st ⟨.dev (GT.dnr r), ((GT.off r : Nat) : Int)⟩ (.int false (GT.wid r)) .vol
      = true := by
  obtain ⟨B, hL, hk, hcell, hdv⟩ := hP.fenster hein r
  unfold accOk
  rw [show (⟨.dev (GT.dnr r), ((GT.off r : Nat) : Int)⟩ : CPtr).blk = CBlk.dev (GT.dnr r) from rfl,
    hL]
  dsimp only
  rw [hc.2.2 (GT.dnr r) hdv, hk,
    show ((GT.off r : Nat) : Int).toNat = GT.off r from Int.toNat_natCast _, hcell]
  simp [BKind.permits]

/-- **H9 WITH THE ADDRESS AS A PREMISE.** `T x = (*(volatile T *)(cp));` for
    any address the check accepts. The proof is `regLies_step`'s, with
    `ev_devReg` replaced by the profile's `adr`: nothing new is assumed about
    the device, only the spelling of its address is widened to the one the
    emitter writes. -/
theorem gerLies_step (X : TVCtx D) (hP : GerAnnahme X.EL X.orc X.O GT) {Γ : Ctx}
    (K : CEnvLay D Γ) (rg : D.Reg) {cp : CX} (hadr : regAdrOk GT cp rg = true)
    {x : Nat} {τc : CTy} (hfit : tyFits (D.rtyp rg) τc = true)
    (hK : K.okB = true) (hf : K.freshB x = true)
    (σ : World D) (st : CSt) (hc : corrW X.EL σ st) (ρG : Env D Γ) (ρC : CLok)
    (hr : EnvRel X.EL K ρG ρC) (v : Wert D (D.rtyp rg))
    (hv : einpassen X.O.zeiger (D.rtyp rg) (X.O.regLies rg σ) = some v) :
    ∃ st', Exec X.EL.lay X.orc X.fr X.CR X.XR
        (.set x τc (.vld cp (.int false (GT.wid rg)))) st ρC
        (.norm st' (lokUpd ρC x (.int (X.O.regLies rg σ)))) ∧
      corrW X.EL σ st' ∧
      EnvRel X.EL (K.push (D.rtyp rg) x) (.cons v ρG)
        (lokUpd ρC x (.int (X.O.regLies rg σ))) := by
  have hein := regAdrOk_ein hadr
  have hacc := gerAcc hP hein rg hc
  have hvl : vLoad X.EL.lay X.orc st ⟨.dev (GT.dnr rg), ((GT.off rg : Nat) : Int)⟩
      (.int false (GT.wid rg)) =
      some (X.O.regLies rg σ, CSt.mk st.mem st.live
        (.vrd ⟨.dev (GT.dnr rg), ((GT.off rg : Nat) : Int)⟩ (.int false (GT.wid rg))
          (X.O.regLies rg σ) :: st.obs)) := by
    unfold vLoad
    rw [if_pos hacc, ← hP.einig hein rg σ st]
  have hev := ev_vld (hP.adr rg cp hadr X.fr st ρC) hvl
  have henc := hP.rund hein rg σ v hv
  have hvc : ValCorr X.EL (D.rtyp rg) v (.int (X.O.regLies rg σ)) := by
    rw [← henc]
    exact valCorr_encW _ τc v hfit
  have hconv : convV τc (.int (X.O.regLies rg σ)) = some (.int (X.O.regLies rg σ)) := by
    rw [← henc]
    exact convV_of_valFits _ _ (encW_fits _ _ v hfit)
  exact ⟨_, Exec.set hev hconv, hc, envRel_push hK hf hr v _ hvc⟩

/-- **H10 WITH THE ADDRESS AS A PREMISE**, and as a `StmtCorr`: `R = e;` is
    `(*(volatile T *)(cp)) = e;`. A device write has no Gabbro trace
    (`Orakel.regSchreib` answers `Unit`), so what is proved is that the C
    statement RUNS, changes no memory, and leaves the relation standing -- the
    observation it appends is the emitted C's, with no model half to compare
    it to. That absence is the store side of the named assumption. -/
theorem gerSchreib_step (X : TVCtx D) (hP : GerAnnahme X.EL X.orc X.O GT) (m : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)
    (rg : D.Reg) (hkl : (D.rklasse rg).schreibbar = true)
    {e : Expr D Γ Λ (D.rtyp rg)} {cp ce : CX} (hadr : regAdrOk GT cp rg = true)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.regWrite (V := V) (l := l) rg hkl e)
      (.vstore cp (.int false (GT.wid rg)) ce) := by
  intro σ st ρG ρC hc hr _
  have hein := regAdrOk_ein hadr
  have hfit := hP.passt hein rg
  have hc' : corrW X.EL (σ.lese Λ e.orte) st := (corrW_lese _ _ _ _ _).mpr hc
  obtain ⟨v, st1, h1, hv, hc1⟩ := he.run X K hc' hr
  have hve := valCorr_int_of_fits _ _ _ _ hfit hv
  subst hve
  have hacc := gerAcc hP hein rg hc1
  have hvf := encW_fits _ _ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG) hfit
  have hvs : vStore X.EL.lay st1 ⟨.dev (GT.dnr rg), ((GT.off rg : Nat) : Int)⟩
      (.int false (GT.wid rg))
      (encW (D.rtyp rg) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG)) =
      some (CSt.mk st1.mem st1.live
        (.vwr ⟨.dev (GT.dnr rg), ((GT.off rg : Nat) : Int)⟩ (.int false (GT.wid rg))
          (encW (D.rtyp rg) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρG)) :: st1.obs)) := by
    unfold vStore
    rw [hacc, hvf]
    rfl
  exact ⟨_, Exec.vstore (hP.adr rg cp hadr X.fr st ρC) h1 (convV_of_valFits _ _ hvf) hvs,
    _, ρC, rfl, hc1, hr⟩

/-- **THE DEVICE READ AS A BLOCK STEP** (`Block.regLies`). Two of the model's
    five hardware outcomes live here, and NEITHER is discharged: an answer
    outside the declared type is `Hardware.register`, an answer against the
    declared promise is `Hardware.geraet`, and in both the Gabbro block ends in
    an error, where `BlockSem` claims nothing. -/
theorem bsem_regLies (X : TVCtx D) (hP : GerAnnahme X.EL X.orc X.O GT) (m : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ)
    (rg : D.Reg) (hkl : (D.rklasse rg).lesbar = true)
    (rest : Block D V l (D.rtyp rg :: Γ) Λ Λ') {x : Nat} {τc : CTy} {cp : CX} {cr : CS}
    (hadr : regAdrOk GT cp rg = true) (hfit : tyFits (D.rtyp rg) τc = true)
    (hK : K.okB = true) (hf : K.freshB x = true)
    (hrest : BlockSem X m (K.push (D.rtyp rg) x) rest cr) :
    BlockSem X m K (Block.regRead rg hkl rest)
      (.seq (.set x τc (.vld cp (.int false (GT.wid rg)))) cr) := by
  intro σ st ρG ρC hc hr hnf
  have hex : execBlock X.O X.passes X.R (Block.regRead rg hkl rest) σ ρG =
      (match einpassen X.O.zeiger (D.rtyp rg) (X.O.regLies rg σ) with
       | Option.some v =>
           if D.rzusage rg v then (execBlock X.O X.passes X.R rest σ (.cons v ρG)).schrumpf
           else .hardware (.geraet rg)
       | Option.none => .hardware (.register rg)) := rfl
  rw [hex] at hnf ⊢
  cases hv : einpassen X.O.zeiger (D.rtyp rg) (X.O.regLies rg σ) with
  | none => rw [hv] at hnf; exact absurd hnf (by simp [Ausgang.istFehler])
  | some v =>
      rw [hv] at hnf
      dsimp only at hnf ⊢
      by_cases hz : D.rzusage rg v = true
      · simp only [hz, if_true] at hnf ⊢
        rw [istFehler_schrumpf] at hnf
        obtain ⟨st1, hE, hc1, hr1⟩ :=
          gerLies_step X hP K rg hadr hfit hK hf σ st hc ρG ρC hr v hv
        obtain ⟨o, h2, hO⟩ := hrest σ st1 (.cons v ρG) _ hc1 hr1 hnf
        exact ⟨o, Exec.seqN hE h2, stOut_schrumpf X m _ o hO⟩
      · have hz' : D.rzusage rg v = false := by
          cases h' : D.rzusage rg v
          · rfl
          · exact absurd h' hz
        simp only [hz', if_false] at hnf
        exact absurd hnf (by simp [Ausgang.istFehler])

/-- **THE CHECKED DEVICE READ AS A BLOCK STEP** (`Block.regLiesElse`) -- the
    interesting one. A device promise that does NOT hold is a BRANCH of the
    program, not a stop: `Hardware.geraet` is gone, and the `else` arm must
    correspond like any other. What is left of the hardware residue is the ONE
    outcome no program can catch: an answer outside the declared TYPE
    (`Hardware.register`), where there is no value to branch on. -/
theorem bsem_regLiesElse (X : TVCtx D) (hP : GerAnnahme X.EL X.orc X.O GT) (m : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ)
    (rg : D.Reg) (hkl : (D.rklasse rg).lesbar = true)
    (zusage : Expr D (D.rtyp rg :: Γ) Λ .bool) (e0 : ErgExpr D Γ Λ V.erg)
    (hΛ : Λ.Perm V.ende) (rest : Block D V l (D.rtyp rg :: Γ) Λ Λ')
    {x : Nat} {τc : CTy} {cp cc : CX} {crr : Option (CTy × CX)} {cr : CS}
    (hadr : regAdrOk GT cp rg = true) (hfit : tyFits (D.rtyp rg) τc = true)
    (hK : K.okB = true) (hf : K.freshB x = true)
    (hzus : ExprCorr X (K.push (D.rtyp rg) x) cc zusage)
    (herg : ErgCorr X K e0 crr)
    (hrest : BlockSem X m (K.push (D.rtyp rg) x) rest cr) :
    BlockSem X m K (Block.regReadElse rg hkl zusage (Endblock.ret e0 hΛ) rest)
      (.seq (.seq (.set x τc (.vld cp (.int false (GT.wid rg))))
        (.ite (.lnot cc) (.ret crr) .skip)) cr) := by
  intro σ st ρG ρC hc hr hnf
  have hex : execBlock X.O X.passes X.R
      (Block.regReadElse rg hkl zusage (Endblock.ret e0 hΛ) rest) σ ρG =
      (match einpassen X.O.zeiger (D.rtyp rg) (X.O.regLies rg σ) with
       | Option.some v =>
           if wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρG)) then
             (execBlock X.O X.passes X.R rest (σ.lese Λ zusage.orte) (.cons v ρG)).schrumpf
           else (execEnd X.O X.passes X.R (Endblock.ret e0 hΛ) (σ.lese Λ zusage.orte)
             ρG).zuAusgang
       | Option.none => .hardware (.register rg)) := rfl
  rw [hex] at hnf ⊢
  cases hv : einpassen X.O.zeiger (D.rtyp rg) (X.O.regLies rg σ) with
  | none => rw [hv] at hnf; exact absurd hnf (by simp [Ausgang.istFehler])
  | some v =>
      rw [hv] at hnf
      dsimp only at hnf ⊢
      obtain ⟨st1, hE, hc1, hr1⟩ :=
        gerLies_step X hP K rg hadr hfit hK hf σ st hc ρG ρC hr v hv
      have hcl : corrW X.EL (σ.lese Λ zusage.orte) st1 := (corrW_lese _ _ _ _ _).mpr hc1
      obtain ⟨st2, h2, hc2⟩ := hzus.runB X (K.push (D.rtyp rg) x) hcl hr1
      have hcc : ev X.EL.lay X.orc X.fr (CX.lnot cc) st1
          (lokUpd ρC x (.int (X.O.regLies rg σ))) =
          some (.int (b2i (!(wahr? (eval (σ.lese Λ zusage.orte) zusage
            (σ.lese Λ zusage.orte) (Env.cons v ρG))))), st2) := by
        simp only [ev, h2, truth_b2i]
      by_cases hb : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte)
          (.cons v ρG)) = true
      · rw [if_pos hb] at hnf ⊢
        rw [istFehler_schrumpf] at hnf
        rw [hb] at hcc
        obtain ⟨o, h3, hO⟩ := hrest _ st2 (.cons v ρG) _ hc2 hr1 hnf
        exact ⟨o, Exec.seqN (Exec.seqN hE (Exec.iteF hcc (truth_b2i false) Exec.skip)) h3,
          stOut_schrumpf X m _ o hO⟩
      · have hb' : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte)
            (.cons v ρG)) = false := by
          cases h' : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte)
            (.cons v ρG))
          · rfl
          · exact absurd h' hb
        rw [if_neg hb] at hnf ⊢
        rw [hb'] at hcc
        have hcl2 : corrW X.EL (σ.lese Λ zusage.orte) st2 := hc2
        have hc3 : corrW X.EL ((σ.lese Λ zusage.orte).lese Λ e0.orte) st2 :=
          (corrW_lese _ _ _ _ _).mpr hcl2
        obtain ⟨st3, cv, hR, hc4, hrc⟩ := ergCorr_run X K herg hc3 (envRel_pop hr1)
        exact ⟨_, Exec.seqX (Exec.seqN hE
          (Exec.iteT hcc (truth_b2i true) hR)) rfl,
          st3, cv, rfl, hc4, hrc⟩

end Geraet
/-! ## 2. Soundness, expression by expression -/


end Gabbro.Grammatik
