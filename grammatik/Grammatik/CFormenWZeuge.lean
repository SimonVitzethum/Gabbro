/-
  File:      Grammatik/CFormenWZeuge.lean
  Subject:   The witnesses of `CFormenW.lean` (rule 13).

  1. THE DIFFERENCE, as a run (`retry_unterschied_zeuge`): on `refD`
     (ReferenzB.lean), `retry 1 until konto[0] == 100 { konto[0] = 100; }`
     with an overflow block that writes `konto[1] = 100`. The one pass
     makes the condition true. The OLD model (`retryLaufAlt`, the `0`
     case of `retryLauf` before 2026-09-13) runs the overflow block and
     writes `konto[1]`; the corrected model (`execStmt` with the corrected
     `retryLauf`, = `retryLaufC`) and the emitted loop do not
     (`retry_c_zeuge`: the C run from the zero state ends with
     `konto[0] = 100`, `konto[1] = 0`). The overflow block is a fixture:
     the emitter admits only a `never` exit there -- a write makes the
     difference visible in memory.

  2. THE EMITTED LOOP OF A CORPUS PROGRAM against the model as it stands
     (`warte_zeuge`): `beispiele/66-transport-rueckgabe.gab`,
     `warte_auf_fertig`, as the emitter wrote it on 2026-09-13 (binary
     built from this tree on ki-pc-fisch-101):

         static bool warte_auf_fertig(bool bereit) {
             {
                 uint32_t _r1 = 0;
                 for (; !(bereit) && _r1 < 64u; _r1 += 1) {
                 }
                 if (_r1 >= 64u && !(bereit)) { gib_auf(); }
             }
             return bereit;
         }

     with `extern fn gib_auf() -> never`: a foreign call (`CS.ext 0`)
     that never returns (`XR` relates nothing), and in Gabbro a foreign
     answer of type `never`, which the oracle cannot supply -- the
     hardware assumption. `scorr_retry` applies (the overflow is always
     an error), `cCorr_ruf` makes the callee relation, and the call
     `warte_auf_fertig(true)` runs end to end on both sides.
-/
import Grammatik.CFormenW
import Grammatik.CFormenZeuge

namespace Gabbro.Grammatik

/-! ## 1. The difference, on `refD` -/

/-- `konto[0] == 100`. -/
def wBis : Expr refD [.int 0 10] [Res.held (D := refD) ()] .bool :=
  .eq (.slot () () refIdxEin refDarf) (.lit 100)

/-- Index `1`. -/
def wIdx1 : Expr refD [.int 0 10] [Res.held (D := refD) ()] (.index (refD.count ())) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- The pass: `konto[0] = 100;`. -/
def wBody : Block refD (vertragVon refD refEin) true [.int 0 10] [Res.held (D := refD) ()]
    [Res.held (D := refD) ()] :=
  .cons (.assignSlot () () refIdxEin refHundert (refEin_schreibt ()) refDarf) .nil

/-- The overflow block of the fixture: `konto[1] = 100;`. -/
def wUeb : Block refD (vertragVon refD refEin) false [.int 0 10] [Res.held (D := refD) ()]
    [Res.held (D := refD) ()] :=
  .cons (.assignSlot () () wIdx1 refHundert (refEin_schreibt ()) refDarf) .nil

/-- `retry 1 until konto[0] == 100 { konto[0] = 100; } on_exceeded { konto[1] = 100; }`. -/
def wRetry : Stmt refD (vertragVon refD refEin) false [.int 0 10] [Res.held (D := refD) ()]
    [Res.held (D := refD) ()] :=
  .retry 1 wBis wBody wUeb

/-- WITNESS, the difference: from `refW0` (both slots `0`), the OLD
    model's run writes `konto[1]` (the overflow block ran after the one
    pass made the condition true); the corrected model (`execStmt`) and
    `retrySemC` do not. -/
theorem retry_unterschied_zeuge :
    (∃ σ', retryLaufAlt (fun σ ρ => execBlock refO 0 (rufAt refP refO 0 1) wBody σ ρ)
        (travInv wBis) (fun σ ρ => execBlock refO 0 (rufAt refP refO 0 1) wUeb σ ρ) 1
        refW0 refRho7 = .ok σ' refRho7 ∧
      (σ'.slots () 0 ()).n = 100 ∧ (σ'.slots () 1 ()).n = 100) ∧
    (∃ σ', execStmt refO 0 (rufAt refP refO 0 1) wRetry refW0 refRho7 = .ok σ' refRho7 ∧
      (σ'.slots () 0 ()).n = 100 ∧ (σ'.slots () 1 ()).n = 0) ∧
    (∃ σ', retrySemC xEin 1 wBis wBody wUeb refW0 refRho7 = .ok σ' refRho7 ∧
      (σ'.slots () 0 ()).n = 100 ∧ (σ'.slots () 1 ()).n = 0) :=
  ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩

/-- The same run, located by `retryLauf_C_verschieden`: the budget is
    spent after one pass, and there the condition holds. -/
theorem retry_unterschied_ort :
    ∃ σ0, retryErschoepft (fun σ ρ => execBlock refO 0 (rufAt refP refO 0 1) wBody σ ρ)
        (travInv wBis) 1 refW0 refRho7 = some (σ0, refRho7) ∧
      (travInv wBis σ0 refRho7).2 = true :=
  ⟨_, rfl, rfl⟩

/-! The emitted loop for the fixture, C locals as in `einzahlen`
(`k = 0`, `i = 1`, `b = 2`) and the counter `_r = 3`. -/

/-- `k->slots[0].stand` -/
def cSlot0 : CX := .slotA (.var 0) (.lit 0) 2 4 0
/-- `k->slots[1].stand` -/
def cSlot1 : CX := .slotA (.var 0) (.lit 1) 2 4 0

/-- `k->slots[0].stand == 100` -/
def cWBis : CX := .cmp .eq CIT.u32 (.ld cSlot0 cU32) (.lit 100)

def cWBody : CS := .seq (.store cSlot0 cU32 (.lit 100)) .skip
def cWUeb : CS := .seq (.store cSlot1 cU32 (.lit 100)) .skip

theorem wBis_corr : ExprCorr xEin kEin cWBis wBis :=
  ecorr_eq xEin kEin CIT.u32
    (ecorr_slotParam xEin kEin kEin_pp () rfl refDarf
      (ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 0)))
    (ecorr_lit xEin kEin 100) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

theorem wBody_corr (m' : Nat) : BlockSem xEin m' kEin wBody cWBody :=
  cCorr_block xEin m' (BlockCorr.cons
    (scorr_assignSlotParam xEin kEin m' kEin_pp () rfl _ _
      (ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 0))
      (ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 100))) BlockCorr.nil)

theorem wUeb_corr (m : Nat) : BlockSem xEin m kEin wUeb cWUeb :=
  cCorr_block xEin m (BlockCorr.cons
    (scorr_assignSlotParam xEin kEin m kEin_pp () rfl _ _
      (ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 1))
      (ecorr_weiter xEin kEin _ _ (ecorr_lit xEin kEin 100))) BlockCorr.nil)

/-- The fixture's loop corresponds to the corrected run (`scorrC_retry`,
    instantiated). -/
theorem wRetry_corrC (m m' : Nat) :
    ∀ (σ : World refD) (st : CSt) (ρG : Env refD [.int 0 10]) (ρC : CLok), corrW refEL σ st →
      EnvRel refEL kEin ρG ρC → (retrySemC xEin 1 wBis wBody wUeb σ ρG).istFehler = false →
      ∃ o, Exec refEL.lay tvOrc 2 xEin.CR tvXR (retryCS 3 1 cWBis cWBody m' cWUeb) st ρC o ∧
        StOut xEin m kEin (retrySemC xEin 1 wBis wBody wUeb σ ρG) o :=
  scorrC_retry xEin m m' kEin (z := 3) rfl rfl 1 (by decide) wBis_corr wBody cWBody
    (wBody_corr m') rfl wUeb cWUeb (wUeb_corr m)

/-- **Witness of `scorr_retry_voll`**: the fixture's `retry` -- whose
    overflow block WRITES memory, no `never` exit -- corresponds to the
    emitted loop against the corrected `execStmt` itself. -/
theorem wRetry_corr (m m' : Nat) :
    StmtCorr xEin m kEin wRetry (retryCS 3 1 cWBis cWBody m' cWUeb) :=
  scorr_retry_voll xEin m m' kEin (z := 3) rfl rfl 1 (by decide) wBis_corr wBody cWBody
    (wBody_corr m') rfl wUeb cWUeb (wUeb_corr m)

/-- WITNESS, the C side of the difference: the emitted loop, run from the
    zero state with the arguments of `einzahlen(k, 0, 7)`, ends normally
    with `konto[0] = 100` and `konto[1] = 0` -- the corrected run, not the
    model's. -/
theorem retry_c_zeuge :
    ∃ st' ρ', Exec refEL.lay tvOrc 2 xEin.CR tvXR (retryCS 3 1 cWBis cWBody 0 cWUeb) refSt0
        (lokUpd (lokUpd (lokUpd (fun _ => .undef) 2 (.int 7)) 1 (.int 0)) 0 (.ptr ⟨.tab 0, 0⟩))
        (.norm st' ρ') ∧
      st'.mem (.tab 0) 0 = .int 100 ∧ st'.mem (.tab 0) 4 = .int 0 := by
  obtain ⟨σ', hsem, h0, h1⟩ := retry_unterschied_zeuge.2.2
  obtain ⟨o, hx, hO⟩ := wRetry_corrC 0 0 refW0 refSt0 refRho7 _ refW0_corr ein_envRel
    (by rw [hsem]; rfl)
  have hO' := @Eq.subst _ (fun A => StOut xEin 0 kEin A o) _ _ hsem hO
  obtain ⟨st', ρ', ho, hc, -⟩ := hO'
  subst ho
  refine ⟨st', ρ', hx, ?_, ?_⟩
  · have := (hc.1 () rfl).2 0 () (by decide) (by decide)
    refine (this : st'.mem (.tab 0) 0 = _).trans ?_
    show CVal.int (σ'.slots () 0 ()).n = _
    rw [h0]
  · have := (hc.1 () rfl).2 1 () (by decide) (by decide)
    refine (this : st'.mem (.tab 0) 4 = _).trans ?_
    show CVal.int (σ'.slots () 1 ()).n = _
    rw [h1]

/-! ## 2. `beispiele/66`: `warte_auf_fertig` -/

/-- `warte_auf_fertig(bereit : bool) -> bool`. -/
def w66Sig : Signatur Empty Empty Empty Empty where
  params := [.bool]
  erg := some .bool
  gruende := 0
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The part of `beispiele/66` the function needs: no carrier, one
    function, one foreign function `gib_auf() -> never` (an `Ax` whose
    answer type is `never`). -/
def w66D : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun e => nomatch e
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun e => nomatch e
  eigner := fun e => nomatch e
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => w66Sig
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some .never
  aschreibt := fun _ e => nomatch e
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

def w66F : w66D.Fn := ()

def w66V : Vertrag w66D := vertragVon w66D w66F

/-- `until bereit` -/
def w66Bis : Expr w66D [.bool] [] .bool := .var .hier

/-- `gib_auf();` -- a foreign call whose answer is `never`. -/
def w66Ueb : Block w66D w66V false [.bool] [] [] :=
  .bindAxiom () .nil rfl (fun t => nomatch t) (fun g => nomatch g) (fun t => nomatch t)
    (fun g => nomatch g) .nil

/-- `retry warten until bereit bounded 64 ops on_exceeded gib_auf { }`. -/
def w66Retry : Stmt w66D w66V false [.bool] [] [] := .retry 64 w66Bis .nil w66Ueb

/-- The body: the loop, then `return bereit;`. -/
def w66Rumpf : Endblock w66D w66V false [.bool] [] :=
  .cons w66Retry (.ret (.wert (.var .hier)) (List.Perm.refl _))

def w66P : Programm w66D where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := fun _ => w66Rumpf

/-- The oracle: a foreign answer `0`, which does not fit `never`. -/
def w66O : Orakel w66D where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- No object: the unit has no table and no global. -/
def w66EL : EmitLay w66D where
  lay := fun _ => none
  tnr := fun t => nomatch t
  tnr_inj := fun t => nomatch t
  trec := fun t => nomatch t
  lay_tab := fun t => nomatch t
  trec_wf := fun t => nomatch t
  trec_count := fun t => nomatch t
  fnr := fun t => nomatch t
  fnr_lt := fun t => nomatch t
  fnr_inj := fun t => nomatch t
  fnr_fits := fun t => nomatch t
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- `bool` -/
def cBool : CTy := .int false .w8

/-- The emitted body: C local 0 is `bereit`, C local 1 the counter
    `_r1`; `gib_auf` is foreign call 0. -/
def cW66Body : CS :=
  .seq (retryCS 1 64 (.var 0) .skip 0 (.ext 0 [] none)) (.ret (some (cBool, .var 0)))

def cW66 : CFun := { params := [(0, cBool)], locals := [], body := cW66Body }

def w66CProg : CProg
  | 0 => some cW66
  | _ => none

/-- `bereit` in C local 0. -/
def kW66 : CEnvLay w66D [.bool] := ⟨[0], [], []⟩

/-- The body runs in frame 1; `gib_auf` never returns (`tvXR` relates
    nothing). -/
def xW66 : TVCtx w66D :=
  ⟨w66EL, tvOrc, 1, CallAt w66EL.lay tvOrc tvXR w66CProg 0, tvXR, w66O, 0, rufAt w66P w66O 0 0⟩

/-- The overflow block always ends in the hardware assumption. -/
theorem w66Ueb_nie (σ : World w66D) (ρ : Env w66D [.bool]) :
    (execBlock xW66.O xW66.passes xW66.R w66Ueb σ ρ).istFehler = true := rfl

/-- Its correspondence is therefore vacuous. -/
theorem w66Ueb_corr (m : Nat) : BlockSem xW66 m kW66 w66Ueb (.ext 0 [] none) := by
  intro σ st ρG ρC _ _ hnf
  rw [w66Ueb_nie σ ρG] at hnf
  exact Bool.noConfusion hnf

/-- The loop of `warte_auf_fertig` against the model's `retry`. -/
theorem w66_retry (m m' : Nat) :
    StmtCorr xW66 m kW66 w66Retry (retryCS 1 64 (.var 0) .skip m' (.ext 0 [] none)) :=
  scorr_retry xW66 m m' kW66 (z := 1) rfl rfl 64 (by decide) (ecorr_var xW66 kW66 .hier) .nil .skip
    (cCorr_block xW66 m' BlockCorr.nil) rfl w66Ueb _ (w66Ueb_corr m) w66Ueb_nie

/-- The body of `warte_auf_fertig` against its emitted body. -/
theorem w66_end (m : Nat) : EndCorr xW66 m true kW66 w66Rumpf cW66Body :=
  EndCorr.cons (w66_retry m 0) (EndCorr.ret (List.Perm.refl _)
    ⟨cBool, .var 0, rfl, ecorr_var xW66 kW66 .hier, rfl⟩)

/-- THE CALLEE RELATION of `warte_auf_fertig` at depth 1. -/
theorem w66_fn : FnCorr w66EL (rufAt w66P w66O 0 1) (CallAt w66EL.lay tvOrc tvXR w66CProg 1)
    w66F 0 cW66.params kW66 :=
  cCorr_ruf w66EL tvOrc tvXR w66P w66O 0 0 w66CProg w66F 0 cW66 rfl kW66 0
    (cCorr_end xW66 0 true (w66_end 0))

/-- The world: nothing but the (empty) trace. -/
def w66W : World w66D := { slots := fun t => (nomatch t), globs := fun g => (nomatch g), spur := [] }

def w66St : CSt := { mem := fun _ _ => .undef, live := fun _ => true, obs := [] }

theorem w66_corr : corrW w66EL w66W w66St := ⟨fun t => (nomatch t), And.intro (fun g => (nomatch g)) (fun _ h => Bool.noConfusion h)⟩

/-- `bereit = true` on both sides. -/
def w66Rho : Env w66D (w66D.params w66F) := .cons (show Bool from true) .nil

theorem w66_envRel : EnvRel w66EL kW66 w66Rho (lokUpd (fun _ => .undef) 0 (.int 1)) := by
  refine ⟨?_, fun q hq => (nomatch hq), fun q hq => (nomatch hq)⟩
  intro τ x
  cases x with
  | hier => rfl
  | dort y => exact nomatch y

/-- WITNESS (rule 13), `warte_auf_fertig(true)` END TO END: the Gabbro
    call returns `true`; the emitted C, called with `1`, runs its `retry`
    (the header sees `bereit`, the check after the loop sees `_r1 = 0`)
    and returns `1`; the final states are related. -/
theorem warte_zeuge :
    ∃ (σ' : World w66D) (st' : CSt),
      rufAt w66P w66O 0 1 w66F w66W w66Rho = .ok σ' (show Bool from true) ∧
      CallAt w66EL.lay tvOrc tvXR w66CProg 1 0 w66St [.int 1] st' (some (.int 1)) ∧
      corrW w66EL σ' st' := by
  have hR : rufAt w66P w66O 0 1 w66F w66W w66Rho = .ok _ (show Bool from true) := rfl
  obtain ⟨st', rv, hC, hO⟩ := w66_fn w66W w66St w66Rho [.int 1] _ w66_corr rfl w66_envRel
    (by rw [hR]; rfl)
  rw [hR] at hO
  obtain ⟨hc, c, hrv, hvc⟩ := hO
  have hc1 : c = .int 1 := hvc
  subst hrv
  subst hc1
  exact ⟨_, st', rfl, hC, hc⟩

#print axioms retry_unterschied_zeuge
#print axioms wRetry_corr
#print axioms retry_unterschied_ort
#print axioms retry_c_zeuge
#print axioms w66_retry
#print axioms w66_fn
#print axioms warte_zeuge

end Gabbro.Grammatik
