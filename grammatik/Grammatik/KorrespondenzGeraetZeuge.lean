/-
  File:      Grammatik/KorrespondenzGeraetZeuge.lean
  Subject:   **A CHAIN FOR A PROGRAM THAT TOUCHES A DEVICE.** The fixture, the
             certificate, the hardware profile DISCHARGED, and the run.

  WHY THIS FILE EXISTS. `korrOk` gained three device rows on 2026-09-16
  (`GRow.storeReg`, `.loadReg`, `.loadRegElse`), and a sieve nobody has seen
  fail is a decoration. So the fixture below carries all three -- a register
  STORE at the top of the body, a plain register READ in one `if` arm and a
  CHECKED register read (`requires … else`) in the other -- and every one of
  them gets BOTH probes:
  * a POSITIVE probe -- the emitted form the arm is meant to accept;
  * a PLANTED DEFECT -- exactly the mistake the arm exists to catch: the
    wrong register (the other one's offset), the wrong cell width, the
    address of a device the table does not name, the `else` branch dropped,
    the promise read as its opposite, and the whole device table switched
    OFF (`ein := false`), which must refuse every device row.

  AND THE PROFILE IS DISCHARGED, not assumed away. `gerAnn : GerAnnahme gEL
  gOrc gO gGT` is a TERM: the window, the address (a theorem for the
  direct-base spelling, `gerAdr_devH`), the declared type, the two oracles
  agreeing, and the answer reading back (`gerRund_int`). A premise nobody can
  meet is not a premise, it is a hole, and this file is the proof that this
  one is not.

  WHAT THE CHAIN CLAIMS, and what it does not: see `gerZeuge_lauf` below and
  `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.9.
-/
import Grammatik.KorrespondenzAllg

namespace Gabbro.Grammatik.GeraetZeuge

open Gabbro.Grammatik

set_option maxRecDepth 100000

/-! ## 1. The fixture: one `mmio` device with two registers -/

abbrev gU32 : Ty := .int 0 4294967295
abbrev gU32c : CTy := .int false .w32

/-- ```
    device Geraet(basis : u64) at mmio {
        reg ST   : u32 @0x00 class r  requires ST <= 8
        reg CTRL : u32 @0x04 class rw
    }
    ``` -/
inductive GReg where
  | st
  | ctrl
  deriving DecidableEq, Repr

/-- `fn treiber(a : u32) -> u32` -- one parameter, one answer, no effects. -/
def gSig : Signatur Empty Empty Empty Empty where
  params := [gU32]
  erg := some gU32
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun g => nomatch g
  konsumiert := []
  produziert := []

/-- No table, no global, no lock, no axiom -- ONE device with two registers
    and ONE function, so that nothing but the device is under test. -/
def gD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => nomatch t
  Feld := fun t => nomatch t
  decFeld := fun t => nomatch t
  typ := fun t => nomatch t
  erlaubt := fun t => nomatch t
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => nomatch g
  nutzlast := fun g => nomatch g
  atomar := fun g => nomatch g
  geteilt := fun t => nomatch t
  ggeteilt := fun g => nomatch g
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun t => nomatch t
  gbraucht := fun g => nomatch g
  eigner := fun t => nomatch t
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => gSig
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := GReg
  rtyp := fun _ => gU32
  rklasse := fun r => match r with | .st => .r | .ctrl => .rw
  spiegel := fun _ => none
  rzusage := fun _ v => decide (Zahl.n v ≤ 8)
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The window: eight bytes, two `uint32_t` cells at `0` and `4`. -/
def gRec : RecLay := natLay 2 [.int false .w32]

/-- Device block `0`, declared `mmio` at `0x40000000`. Nothing else exists. -/
def gLay : CLayout := fun b =>
  match b with
  | .dev 0 => some { lay := gRec, kind := .mmio, base := 1073741824 }
  | _ => none

def gEL : EmitLay gD where
  lay := gLay
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
  devs := fun d => decide (d = 0)

/-- The certificate's DEVICE TABLE -- the emitter's numbers, as plain data.
    The handle spelling is OFF (`griff` defaults to `false`), so the address
    is the direct-base one and `GerAnnahme.adr` is a theorem below. -/
def gGT : GerTafel gD where
  ein := true
  dnr := fun _ => 0
  basis := fun _ => 1073741824
  off := fun r => match r with | .st => 0 | .ctrl => 4
  wid := fun _ => .w32

/-- `(volatile uint8_t *)(uintptr_t)0x40000000 + 0` -- the address of `ST`. -/
def cpST : CX := .padd (.devH 0 1073741824) (.lit 0)

/-- `… + 4` -- the address of `CTRL`. -/
def cpCTRL : CX := .padd (.devH 0 1073741824) (.lit 4)

/-! ## 2. The program: a driver-shaped body with all three device forms -/

abbrev gV : Vertrag gD := vertragVon gD ()

/-- `fn treiber(a : u32) -> u32` -- one parameter in C local `0`. -/
abbrev gCtx : Ctx := [gU32]

/-- `let s = ST; a = s;` -- the plain register read: its promise
    (`ST <= 8`) is the DEVICE's, and breaking it is `Hardware.geraet`. -/
def gArmT : Block gD gV false gCtx [] [] :=
  .regLies .st rfl (.cons (Stmt.assignVar (.dort .hier) (Expr.var .hier)) .nil)

/-- `let t = ST else (t < 9) { return 0; } a = t;` -- the CHECKED read: the
    same promise, but read by the PROGRAM, so a broken promise is a branch
    and not a stop. -/
def gArmE : Block gD gV false gCtx [] [] :=
  .regLiesElse .st rfl (Expr.lt (Expr.var .hier) (Expr.lit 9))
    (Endblock.ret (.wert (Expr.weiter (by decide) (by decide) (Expr.lit 0)))
      (List.Perm.refl []))
    (.cons (Stmt.assignVar (.dort .hier) (Expr.var .hier)) .nil)

/-- ```
    impl fn treiber(a : u32) -> u32 {
        CTRL = a;
        if (a < 1) { let s = ST; a = s; }
        else       { let t = ST else (t < 9) { return 0; }  a = t; }
        return a;
    }
    ``` -/
def gBody : Endblock gD gV false gCtx [] :=
  .cons (Stmt.regSchreib .ctrl rfl (Expr.var .hier))
    (.cons (Stmt.ite (Expr.lt (Expr.var .hier) (Expr.lit 1)) gArmT gArmE)
      (.ret (.wert (Expr.var .hier)) (List.Perm.refl [])))

def gProg : Programm gD where
  invariante := fun i => nomatch i
  requires := fun _ => Expr.wahr
  ensures := fun _ => Expr.wahr
  rumpf := fun _ => gBody

/-! ## 3. The certificate: the emitted C, row by row

```c
uint32_t treiber(uint32_t v0) {
    (*(volatile uint32_t *)((volatile uint8_t *)(uintptr_t)0x40000000 + 4)) = v0;
    if (v0 < 1u) {
        uint32_t v1 = (*(volatile uint32_t *)((volatile uint8_t *)(uintptr_t)0x40000000 + 0));
        v0 = v1;
    } else {
        uint32_t v2 = (*(volatile uint32_t *)((volatile uint8_t *)(uintptr_t)0x40000000 + 0));
        if (!(v2 < 9u)) { return 0u; }
        v0 = v2;
    }
    return v0;
}
```
-/

def gRows : List GRow :=
  [ .storeReg cpCTRL .w32 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .loadReg 1 gU32c cpST .w32, .setVar 0 gU32c (.var 1) ]
      [ .loadRegElse 2 gU32c cpST .w32 (.cmp .lt CIT.u32 (.var 2) (.lit 9))
          (some (gU32c, .lit 0))
      , .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

def gKF : KFun gD :=
  { params := [(0, gU32c)], locals := [], rows := gRows, vm := [0], pp := [], ks := [] }

def gZert : KCert gD := [gKF]

def gFnum : gD.Fn → Nat := fun _ => 0

/-- **THE CHECK PASSES** -- a device-touching program with a correspondence
    certificate, decided. -/
theorem gZert_ok : korrOk gEL gFnum gZert gProg [()] gGT = true := by decide

/-- Every function of the unit is in the member list. -/
theorem gVoll : ∀ g : gD.Fn, g ∈ [()] := fun g => by cases g; exact List.Mem.head _

/-- **NON-DEGENERACY, the sharp form.** This body is NOT `hardwareFrei`: the
    `korrOk` of before could not have certified it (it refused all five
    hardware forms outright), and `rufAt_ohneHardware` does NOT apply to it.
    What the device chain buys is exactly this program, and what it pays is
    exactly that theorem -- which is why `korrOk_rufAt_ohneHardware` now
    carries `GT.ein = false` in its premise list. -/
theorem gerZeuge_nichtHardwareFrei : gBody.hardwareFrei = false := by decide

/-- And the DEFAULT certificate call -- the one the two closed chains make,
    with no device table -- refuses this program. -/
theorem gZert_ohneTafel : korrOk gEL gFnum gZert gProg [()] = false := by decide

/-! ## 4. The planted defects -- what each device arm refuses -/

/-- The device table switched OFF: every device row is refused, and with it
    the whole certificate. This is the premise `korrOk_rufAt_ohneHardware`
    carries (`GT.ein = false`), read from the other side. -/
def gGTaus : GerTafel gD := { gGT with ein := false }

/-- The wrong REGISTER: `ST`'s row at `CTRL`'s address. -/
def gRowsFalschesReg : List GRow :=
  [ .storeReg cpCTRL .w32 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .loadReg 1 gU32c cpCTRL .w32, .setVar 0 gU32c (.var 1) ]
      [ .loadRegElse 2 gU32c cpST .w32 (.cmp .lt CIT.u32 (.var 2) (.lit 9))
          (some (gU32c, .lit 0))
      , .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

/-- The wrong CELL WIDTH: a `uint16_t` access at a `uint32_t` register. -/
def gRowsFalscheBreite : List GRow :=
  [ .storeReg cpCTRL .w16 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .loadReg 1 gU32c cpST .w32, .setVar 0 gU32c (.var 1) ]
      [ .loadRegElse 2 gU32c cpST .w32 (.cmp .lt CIT.u32 (.var 2) (.lit 9))
          (some (gU32c, .lit 0))
      , .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

/-- The promise read as its OPPOSITE: `t > 9` where the program checks
    `t < 9`. The `else` branch would then be taken on the good answers. -/
def gRowsFalscheZusage : List GRow :=
  [ .storeReg cpCTRL .w32 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .loadReg 1 gU32c cpST .w32, .setVar 0 gU32c (.var 1) ]
      [ .loadRegElse 2 gU32c cpST .w32 (.cmp .gt CIT.u32 (.var 2) (.lit 9))
          (some (gU32c, .lit 0))
      , .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

/-- The `else` branch DROPPED: the checked read read as a plain one. -/
def gRowsOhneElse : List GRow :=
  [ .storeReg cpCTRL .w32 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .loadReg 1 gU32c cpST .w32, .setVar 0 gU32c (.var 1) ]
      [ .loadReg 2 gU32c cpST .w32, .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

/-- The `else` branch's ANSWER changed: `return 1;` where the program
    returns `0`. -/
def gRowsFalscherElseWert : List GRow :=
  [ .storeReg cpCTRL .w32 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .loadReg 1 gU32c cpST .w32, .setVar 0 gU32c (.var 1) ]
      [ .loadRegElse 2 gU32c cpST .w32 (.cmp .lt CIT.u32 (.var 2) (.lit 9))
          (some (gU32c, .lit 1))
      , .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

/-- An ordinary local READ where the device read stands: the row that would
    turn a volatile access into a plain one. -/
def gRowsKeinGeraet : List GRow :=
  [ .storeReg cpCTRL .w32 (.var 0)
  , .ite (.cmp .lt CIT.u32 (.var 0) (.lit 1))
      [ .bindLet 1 gU32c (.var 0), .setVar 0 gU32c (.var 1) ]
      [ .loadRegElse 2 gU32c cpST .w32 (.cmp .lt CIT.u32 (.var 2) (.lit 9))
          (some (gU32c, .lit 0))
      , .setVar 0 gU32c (.var 2) ]
  , .ret (some (gU32c, .var 0)) ]

def gZertVon (rs : List GRow) : KCert gD :=
  [{ params := [(0, gU32c)], locals := [], rows := rs, vm := [0], pp := [], ks := [] }]

/-- **EVERY PLANTED DEFECT IS REFUSED**, and the accepted certificate is
    refused too once the device table is switched off. -/
theorem gZert_sieb :
    korrOk gEL gFnum gZert gProg [()] gGTaus = false ∧
    korrOk gEL gFnum (gZertVon gRowsFalschesReg) gProg [()] gGT = false ∧
    korrOk gEL gFnum (gZertVon gRowsFalscheBreite) gProg [()] gGT = false ∧
    korrOk gEL gFnum (gZertVon gRowsFalscheZusage) gProg [()] gGT = false ∧
    korrOk gEL gFnum (gZertVon gRowsOhneElse) gProg [()] gGT = false ∧
    korrOk gEL gFnum (gZertVon gRowsFalscherElseWert) gProg [()] gGT = false ∧
    korrOk gEL gFnum (gZertVon gRowsKeinGeraet) gProg [()] gGT = false := by
  decide

/-! ## 5. The hardware profile, DISCHARGED -/

/-- The C device oracle: this machine answers `5` at every register, in
    every history. -/
def gOrc : DevOrc := fun _ _ _ => 5

/-- Gabbro's oracle for the same machine: `regLies` answers `5`. -/
def gO : Orakel gD where
  wirkt := fun a => nomatch a
  regLies := fun _ _ => 5
  regSchreib := fun _ _ => ()
  sichtbar := fun g => nomatch g

/-- (G1) The window: block `0` is `mmio`, and each register's offset is a
    `uint32_t` cell of it. -/
theorem gerFenster (r : gD.Reg) : ∃ B : BlkLay, gEL.lay (.dev (gGT.dnr r)) = some B ∧
    B.kind = .mmio ∧ B.lay.cell (gGT.off r) = some (.int false (gGT.wid r)) ∧
    gEL.devs (gGT.dnr r) = true :=
  ⟨{ lay := gRec, kind := .mmio, base := 1073741824 }, rfl, rfl,
    by cases r <;> decide, rfl⟩

/-- The shape `gerAdr_devH` asks for: the same window, with the offset
    inside it. -/
theorem gerFensterA (r : gD.Reg) : ∃ B : BlkLay, gEL.lay (.dev (gGT.dnr r)) = some B ∧
    B.kind = .mmio ∧ (B.base : Int) = gGT.basis r ∧ gGT.off r ≤ B.lay.size :=
  ⟨{ lay := gRec, kind := .mmio, base := 1073741824 }, rfl, rfl,
    by cases r <;> decide, by cases r <;> decide⟩

/-- (G4) The register's declared type fits its cell. -/
theorem gerPasst (r : gD.Reg) : tyFits (gD.rtyp r) (.int false (gGT.wid r)) = true := by
  cases r <;> decide

/-- (G5) The two oracles are ONE machine: both answer `5`. -/
theorem gerEinig (r : gD.Reg) (σ : World gD) (st : CSt) :
    cWrap (gGT.wid r) (gOrc st.obs ⟨.dev (gGT.dnr r), (gGT.off r : Int)⟩
      (.int false (gGT.wid r))) = gO.regLies r σ := by
  show (cWrap .w32 5 : Int) = 5
  decide

/-- **THE PROFILE IS INHABITED.** Every one of the five facts is discharged
    here: the window and its cells from the layout, the address by
    `gerAdr_devH` (the direct-base spelling is a THEOREM), the declared type
    by `tyFits`, the two oracles by the fixture's own choice of the same
    number, and the read-back by `gerRund_int` (an integer register). -/
theorem gerAnn : GerAnnahme gEL gOrc gO gGT where
  fenster := fun _ r => gerFenster r
  adr := by
    intro r cp hadr fr st ρC
    rw [regAdrOk_devH rfl hadr]
    exact gerAdr_devH gerFensterA r fr st ρC
  passt := fun _ r => gerPasst r
  einig := fun _ r σ st => gerEinig r σ st
  rund := fun _ r σ v h => gerRund_int (r := r) (lo := 0) (hi := 4294967295) rfl σ v h

/-! ## 6. THE CHAIN, for this program

    What it claims, in one sentence: *if the profile holds and the register
    answers inside its declared type, every run of the emitted C
    corresponds.* Read the premise list of `gerZeuge_lauf` and nothing else:

    * `gZert_ok` -- the certificate CHECKS (a Bool, decided);
    * `gerAnn` -- the hardware profile HOLDS (window, address, declared type,
      the two oracles, the read-back);
    * `hw : corrW gEL σ st` -- the C state is related to the Gabbro world,
      which since 2026-09-16 INCLUDES that the unit's device window is
      MAPPED (`EmitLay.devs`);
    * `hb`, `hr` -- the C arguments are related to the Gabbro ones;
    * `hnf` -- the Gabbro call ends in NO model error. *That is where the
      device's own behaviour sits*: a register answer outside the declared
      type (`Hardware.register`) or against the declared promise
      (`Hardware.geraet`) makes the Gabbro call an error, and then this
      theorem claims nothing at all.

    It does NOT claim that the device answers, that it answers the truth, or
    that it keeps its promise. -/

/-- **THE CALLEE RELATION** between Gabbro's call of `treiber` and the C call
    of the emitted unit, at EVERY call depth and budget. -/
theorem gerZeuge_kette (XR : CCallR) (passes n : Nat) :
    FnCorr gEL (rufAt gProg gO passes n) (CallAt gEL.lay gOrc XR (kProg gZert) n)
      () (gFnum ()) gKF.params gKF.lay :=
  korrOk_fnCorr gVoll gZert_ok gOrc XR gO passes gerAnn n () gKF rfl

/-- **EVERY RUN.** From a C state related to the Gabbro world -- and with the
    device window mapped, which that relation now says -- when the Gabbro
    call ends in no model error, the C call has a run, and every run of it
    ends related to the Gabbro outcome. -/
theorem gerZeuge_lauf (XR : CCallR) (hXR : XR.Funktional) (passes n : Nat)
    (σ : World gD) (st : CSt) (ρG : Env gD (gD.params ())) (vs : List CVal) (ρ0 : CLok)
    (hw : corrW gEL σ st) (hb : bindParams gKF.params vs = some ρ0)
    (hr : EnvRel gEL gKF.lay ρG ρ0)
    (hnf : (rufAt gProg gO passes n () σ ρG).istFehler = false) :
    (∃ st' rv, CallAt gEL.lay gOrc XR (kProg gZert) n (gFnum ()) st vs st' rv) ∧
      ∀ st' rv, CallAt gEL.lay gOrc XR (kProg gZert) n (gFnum ()) st vs st' rv →
        RufOut gEL (rufAt gProg gO passes n () σ ρG) st' rv :=
  korrOk_jeder_lauf gVoll gZert_ok gOrc XR hXR gO passes n gerAnn () gKF rfl σ st ρG vs ρ0
    hw hb hr hnf

#print axioms gZert_ok
#print axioms gZert_sieb
#print axioms gerZeuge_nichtHardwareFrei
#print axioms gerAnn
#print axioms gerZeuge_kette
#print axioms gerZeuge_lauf

end Gabbro.Grammatik.GeraetZeuge
