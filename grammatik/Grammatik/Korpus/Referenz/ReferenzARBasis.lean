/-
  File:      Grammatik/ReferenzAR.lean
  Subject:   REFERENCE FIXTURE WITH AXIOMS AND REGISTERS -- the lane-146 gap.

  `refD` (`ReferenzB.lean`) has `Ax = Empty` and `Reg = Empty`, so no
  `axiomCall`/`bindAxiom`/`transition` certificate is even well-typed there
  and no rule-13 witness exists. This file adds a second, non-degenerate
  fixture `arD`: one table `konto` (2 slots, `.int 0 100`, guarded by the
  lock `m`), two nullary axioms with a real frame (both write `konto`;
  `ruf0` without result for `Stmt.axiomCall`, `ruf1` with `.int 0 10`
  result for `Block.bindAxiom`), and two device registers (`w` writable
  with mirror `r`, `r` readable) with `DecidableEq` carried as a separate
  instance (the declaration structure has no `decReg` field and shared
  files are not edited). The F-machine run takes the lock and fires the
  `axiomCall` leaf, whose oracle writes slot `0 := 100`.
-/
module
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
@[expose] public section


namespace Gabbro.Grammatik

/-- Device registers: `w` is writable and mirrors `r`; `r` is readable. -/
inductive ARReg where
  | w
  | r
  deriving DecidableEq, Repr

/-- Axioms: `ruf0` without result (the `Stmt.axiomCall` shape), `ruf1`
    with an `.int 0 10` result (the `Block.bindAxiom` shape). -/
inductive ARAx where
  | ruf0
  | ruf1
  deriving DecidableEq, Repr

/-- Signature of the single function `main`: no parameters, no result,
    holds the lock, may write the table. -/
def arSigMain : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The reference declaration with axioms and registers: one table
    `konto` of 2 slots with one `.int 0 100` field, guarded by the single
    lock `m`; one function `main` (`()`); two nullary axioms writing
    `konto`; two registers with `w` mirroring `r`. -/
def arD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun | 0 => arSigMain | _ => arSigMain
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := ARAx
  aparams := fun _ => []
  aerg := fun | .ruf0 => none | .ruf1 => some (.int 0 10)
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
  Reg := ARReg
  rtyp := fun _ => .int 0 255
  rklasse := fun | .w => .rw | .r => .r
  spiegel := fun | .w => some .r | .r => none
  rzusage := fun _ _ => true
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- `DecidableEq` on the registers, carried as a separate instance: the
    declaration structure has no `decReg` field and shared files stay
    untouched. -/
instance arDecReg : DecidableEq arD.Reg := by
  show DecidableEq ARReg
  infer_instance

/-- `w` is writable. -/
theorem arW_schreibbar : (arD.rklasse .w).schreibbar = true := by rfl

/-- `w` mirrors `r`. -/
theorem arW_spiegel : arD.spiegel .w = some .r := by rfl

/-- `r` is readable. -/
theorem arR_lesbar : (arD.rklasse .r).lesbar = true := by rfl

/-- `ruf0` takes no parameters. -/
theorem arRuf0_params : arD.aparams .ruf0 = [] := by rfl

/-- `ruf0` returns nothing. -/
theorem arRuf0_erg : arD.aerg .ruf0 = none := by rfl

/-- `ruf1` returns `.int 0 10`. -/
theorem arRuf1_erg : arD.aerg .ruf1 = some (.int 0 10) := by rfl

/-! ## 2. Holdings, frames, the program -/

/-- The lock holdings: the single lock. -/
abbrev arL : List (Res arD) := [Res.held (D := arD) ()]

/-- The table access is allowed holding the lock. -/
theorem arDarf : darf arD () arL := by
  intro w h
  simp only [arD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ arD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- `main` holds the lock: start equals the holdings. -/
theorem arStart : Signatur.anfang arD (arD.signatur ()) = arL := by rfl

/-- End holdings of `main`: the lock. -/
theorem arEnde : (vertragVon arD ()).ende = arL := by rfl

/-- `main` writes the table (contract level). -/
theorem arSchreibt (t : arD.Tab) :
    (vertragVon arD ()).schreibt t = true := by
  cases t <;> rfl

/-- Foreign-write frame of `ruf0`: the axiom writes only `konto`, which
    `main` may write. Stated as data (like the `RufPasst` fields): both
    sides are constantly `true`, so the hypothesis has no content to
    use -- the evidence is carried, not deduced. -/
def arHw0 : ∀ t : arD.Tab, arD.aschreibt .ruf0 t = true →
    (vertragVon arD ()).schreibt t = true :=
  fun t _ => by cases t <;> rfl

/-- Foreign-write frame of `ruf1`. -/
def arHw1 : ∀ t : arD.Tab, arD.aschreibt .ruf1 t = true →
    (vertragVon arD ()).schreibt t = true :=
  fun t _ => by cases t <;> rfl

/-- Global frame of `ruf0`: vacuous, there are no globals. -/
theorem arHg0 (g : arD.Glob) (hg : arD.agschreibt .ruf0 g = true) :
    (vertragVon arD ()).gschreibt g = true :=
  nomatch g

/-- Global frame of `ruf1`. -/
theorem arHg1 (g : arD.Glob) (hg : arD.agschreibt .ruf1 g = true) :
    (vertragVon arD ()).gschreibt g = true :=
  nomatch g

/-- Guard frame of `ruf0`: the written table is guarded by the held
    lock. Data, as above. -/
def arHd0 : ∀ t : arD.Tab, arD.aschreibt .ruf0 t = true →
    darf arD t arL :=
  fun t _ => by cases t; exact arDarf

/-- Guard frame of `ruf1`. -/
def arHd1 : ∀ t : arD.Tab, arD.aschreibt .ruf1 t = true →
    darf arD t arL :=
  fun t _ => by cases t; exact arDarf

/-- Global guard frame of `ruf0`. -/
theorem arHgd0 (g : arD.Glob) (hg : arD.agschreibt .ruf0 g = true) :
    gdarf arD g arL :=
  nomatch g

/-- Global guard frame of `ruf1`. -/
theorem arHgd1 (g : arD.Glob) (hg : arD.agschreibt .ruf1 g = true) :
    gdarf arD g arL :=
  nomatch g

/-- The `Stmt`-position axiom call: `ruf0()`. -/
def arAxStmt : Stmt arD (vertragVon arD ()) false []
    (vertragVon arD ()).ende (vertragVon arD ()).ende :=
  .axiomCall .ruf0 .nil rfl arHw0 arHg0 arHd0 arHgd0

/-- The axiom call at the lock holdings. -/
def arAxStmtAt : Stmt arD (vertragVon arD ()) false [] arL arL :=
  arEnde ▸ arAxStmt

/-- `main` body: call the axiom, return. -/
def arRumpf : Endblock arD (vertragVon arD ()) false [] arL :=
  .cons arAxStmtAt (.ret .empty (by rfl))

/-- The program: `main` requires `true`, ensures `true`, calls `ruf0`. -/
def arP : Programm arD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => arStart ▸ arRumpf

/-- `arP.rumpf` of `main` is the axiom-call body. -/
theorem arP_rumpf : arP.rumpf () = arStart ▸ arRumpf := by rfl


end Gabbro.Grammatik
