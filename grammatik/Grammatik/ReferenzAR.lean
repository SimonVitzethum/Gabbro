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
import Grammatik.RufMaschineF

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
theorem arW_schreibbar : (arD.rklasse .w).schreibbar = true := rfl

/-- `w` mirrors `r`. -/
theorem arW_spiegel : arD.spiegel .w = some .r := rfl

/-- `r` is readable. -/
theorem arR_lesbar : (arD.rklasse .r).lesbar = true := rfl

/-- `ruf0` takes no parameters. -/
theorem arRuf0_params : arD.aparams .ruf0 = [] := rfl

/-- `ruf0` returns nothing. -/
theorem arRuf0_erg : arD.aerg .ruf0 = none := rfl

/-- `ruf1` returns `.int 0 10`. -/
theorem arRuf1_erg : arD.aerg .ruf1 = some (.int 0 10) := rfl

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
theorem arStart : Signatur.anfang arD (arD.signatur ()) = arL := rfl

/-- End holdings of `main`: the lock. -/
theorem arEnde : (vertragVon arD ()).ende = arL := rfl

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
  .cons arAxStmtAt (.ret .keine (by rfl))

/-- The program: `main` requires `true`, ensures `true`, calls `ruf0`. -/
def arP : Programm arD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := fun _ => arStart ▸ arRumpf

/-- `arP.rumpf` of `main` is the axiom-call body. -/
theorem arP_rumpf : arP.rumpf () = arStart ▸ arRumpf := rfl

/-! ## 3. Oracle, memory, declared axiom ensures -/

/-- The written cap `100` in range. -/
def arV100 : Wert arD (.int 0 100) := ⟨100, by decide, by decide⟩

/-- The witness oracle: every axiom stores the cap `100` at `konto[0]`;
    `ruf1` answers raw `7` (in `.int 0 10`), `ruf0` answers raw `0`
    (ignored, it has no result). Register reads answer `0`. -/
def arO : Orakel arD where
  wirkt := fun a σ _ => match a with
    | .ruf0 => (σ.storeSlot () 0 () arV100, 0)
    | .ruf1 => (σ.storeSlot () 0 () arV100, 7)
  regLies := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbar := fun g => nomatch g

/-- The start memory: every slot reads `0`. -/
def arSp0 : Speicher arD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Start slot value: `0`. -/
theorem arSp0_slot :
    arSp0.slots () 0 () = (⟨0, by decide, by decide⟩ :
      Wert arD (arD.typ () ())) := rfl

/-- Declared ensures of the axioms (the `AxEns` shape of
    `AxiomVertrag.lean`, stated without the import): `ruf1` answers the
    new value of the slot it writes; `ruf0` promises nothing beyond its
    frame. -/
def arQ (a : arD.Ax) (σ' : World arD) (v : ErgVal arD (arD.aerg a)) : Bool :=
  match a with
  | .ruf0 => true
  | .ruf1 => decide (v.n = (σ'.slots () 0 ()).n)

/-! ## 4. The call-machine run: lock, then the axiom call -/

/-- Thread start: every thread runs `main`. -/
def arInit : Faden → Σ f : arD.Fn, Env arD (arD.params f)
  | _ => ⟨(), .nil⟩

/-- The start machine for the witness run. -/
def arM0 : RufMaschineF arD := RufStartF arP arSp0 arInit

/-- The lock is free at the start: every trace is empty. -/
theorem arFrei0 : RufFreiF arM0 1 (()) := by
  intro g hne hmem
  have e : (arM0.faeden g).spur = [] := rfl
  have hnil : offen (arM0.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List arD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing yet. -/
theorem arSelf0 : (() : arD.Lock) ∉ offen (arM0.faeden 1).spur := by
  intro hmem
  have e : (arM0.faeden 1).spur = [] := rfl
  have hnil : offen (arM0.faeden 1).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List arD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing, so the rank side is vacuous. -/
theorem arRang0 (K : arD.Lock) (hK : K ∈ offen (arM0.faeden 1).spur) :
    arD.rang K < arD.rang (()) := by
  have e : (arM0.faeden 1).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis arD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A: thread 1 takes the lock. -/
def arM1 : RufMaschineF arD :=
  ⟨arM0.speicher,
   rufUpdateF arM0.faeden 1
     ⟨(arM0.faeden 1).stapel, (arM0.faeden 1).kopf,
      Ereignis.nimmt () (offen (arM0.faeden 1).spur) :: (arM0.faeden 1).spur,
      (arM0.faeden 1).log⟩,
   arM0.lauf ++ rufEigenF 1 [Ereignis.nimmt () (offen (arM0.faeden 1).spur)],
   arM0.start⟩

theorem arSchrittA : RufSchrittF arP arO 0 arM0 1 arM1 := by
  unfold arM1
  exact RufSchrittF.nimmt arM0 1 () arSelf0 (fun K hK => arRang0 K hK)
    arFrei0

theorem arReachA : RufErreichbarF arP arO 0 arM0 arM1 :=
  RufErreichbarF.schritt _ _ 1 RufErreichbarF.start arSchrittA

/-- Thread 1 holds the lock exactly after step A. -/
theorem arM1haelt :
    HeldGenau arL (offen (arM1.faeden 1).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (arM1.faeden 1).spur = [()] := rfl
  rw [eH, eL]
  constructor
  · intro hL
    have heq : Res.held (D := arD) L = Res.held (D := arD) () :=
      (List.mem_singleton.mp hL)
    cases heq
    exact List.mem_singleton.mpr rfl
  · intro hL
    have heq : L = () :=
      (List.mem_singleton.mp (eH ▸ hL))
    cases heq
    exact List.mem_singleton.mpr rfl

/-- The read world of the axiom call: no argument reads (nullary). -/
def arW1 : World arD := (arM1.weltVon 1).lese arL []

/-- The answer world: the oracle stores the cap `100` at `konto[0]`. -/
def arS1 : World arD := (arO.wirkt .ruf0 arW1 .nil).1

/-- Step B: thread 1 fires the `ruf0` axiom call. The oracle answers
    without a result (`aerg` is `none`, so `einpassenErg` always fits)
    and its answer world carries the written cap. -/
def arMB : RufMaschineF arD :=
  ⟨arS1.speicher,
   rufUpdateF arM1.faeden 1
     ⟨(arM1.faeden 1).stapel,
      ⟨(arM1.faeden 1).kopf.f, (arM1.faeden 1).kopf.rho,
       (arM1.faeden 1).kopf.s0,
       ⟨false, [], arL, .nil, (.ret .keine (by rfl))⟩⟩,
      arS1.spur,
      (arM1.faeden 1).log⟩,
   arM1.lauf ++ rufEigenF 1 [],
   arM1.start⟩

theorem arSchrittB : RufSchrittF arP arO 0 arM1 1 arMB := by
  have hhead : (arM1.faeden 1).kopf.rest =
      ⟨false, [], arL, .nil,
        .cons arAxStmtAt (.ret .keine (by rfl))⟩ := rfl
  have hstep : (execStmt arO 0 keinRuf arAxStmtAt
      (arM1.weltVon 1) .nil) =
      Ausgang.ok (D := arD) (V := vertragVon arD (arM1.faeden 1).kopf.f)
        arS1 .nil := rfl
  have hneu : arS1.spur = [] ++ (arM1.faeden 1).spur := rfl
  have hkn : ∀ (L : arD.Lock) (h : List arD.Lock),
      Ereignis.nimmt L h ∉ ([] : List (Ereignis arD)) := by
    intro L h hm
    simp at hm
  exact RufSchrittF.blatt arM1 1 false [] arL arL
    arAxStmtAt _ .nil rfl hhead arM1haelt _ _ _ hstep hneu hkn

theorem arReachB : RufErreichbarF arP arO 0 arM0 arMB :=
  RufErreichbarF.schritt _ _ 1 arReachA arSchrittB

/-- `arM0` IS the start machine. -/
theorem arM0_start : arM0 = RufStartF arP arSp0 arInit := rfl

/-- The witness run: lock, then the memory-writing axiom call. -/
theorem arB_erreicht :
    RufErreichbarF arP arO 0 (RufStartF arP arSp0 arInit) arMB := by
  rw [← arM0_start]
  exact arReachB

/-- The final memory carries the written cap at `konto[0]`. -/
theorem arMB_slot : arMB.speicher.slots () 0 () = arV100 := by
  have hhit := storeSlot_hit (D := arD) arW1 () 0 () arV100
  have hmem : arMB.speicher.slots () 0 () =
      ((arW1.storeSlot () 0 () arV100).slots () 0 ()) := rfl
  rw [hmem]
  exact hhit

/-- Memory really moved: `konto[0]` reads `100`, the start reads `0`. -/
theorem arB_schreibt : arMB.speicher.slots () 0 () ≠
    arSp0.slots () 0 () := by
  have h100 := arMB_slot
  have h0 : arSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert arD (arD.typ () ())) := rfl
  rw [h100, h0]
  intro hcon
  have hn : (arV100.n) = ((⟨0, by decide, by decide⟩ :
      Wert arD (arD.typ () ())).n) := congrArg Zahl.n hcon
  simp [arV100] at hn

/-- Joint witness: the reached machine with its memory move, instantiated
    together. The run is NON-DEGENERATE: `main` writes `konto` by contract
    and by axiom frame, and step B changes the slot (`0 -> 100`). -/
theorem arB_schreibt_zeuge : ∃ (M : RufMaschineF arD),
    RufErreichbarF arP arO 0 (RufStartF arP arSp0 arInit) M ∧
    M.speicher.slots () 0 () ≠ arSp0.slots () 0 () :=
  ⟨arMB, arB_erreicht, arB_schreibt⟩

/-! ## CUTS:
  - The oracle `arO` is NOT shown `GutO`: it stores the cap without
    recording `axiomSpur` trace events, so the trace conjunct of `GutO`
    does not hold. No run step needs `GutO` (`blatt` runs `execStmt`
    only), and the certificates of `ZeugnisStmt3.lean` do not need it
    either -- they elaborate prints to typed terms, where the oracle
    never appears.
  - No PC-machine run: the one F run above is the non-degenerate witness
    every `ZeugnisStmt3` lemma builds on.
  - `arQ` is stated without the `AxEns` abbrev (no `AxiomVertrag` import):
    the declared-ensures shape, not the obligation theory around it.
-/

#print axioms Gabbro.Grammatik.arB_erreicht
#print axioms Gabbro.Grammatik.arB_schreibt
#print axioms Gabbro.Grammatik.arB_schreibt_zeuge

end Gabbro.Grammatik
