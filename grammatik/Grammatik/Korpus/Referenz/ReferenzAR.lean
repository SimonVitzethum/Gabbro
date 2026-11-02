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

public import Grammatik.Korpus.Referenz.ReferenzARBasis

namespace Gabbro.Grammatik
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
      Wert arD (arD.typ () ())) := by rfl

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
def arS1 : World arD := (arO.wirkt .ruf0 (arW1.fragt (Sum.inl ARAx.ruf0)) .nil).1

/-- Step B: thread 1 fires the `ruf0` axiom call. The oracle answers
    without a result (`aerg` is `none`, so `einpassenErg` always fits)
    and its answer world carries the written cap. -/
def arMB : RufMaschineF arD :=
  ⟨arS1.speicher,
   rufUpdateF arM1.faeden 1
     ⟨(arM1.faeden 1).stapel,
      ⟨(arM1.faeden 1).kopf.f, (arM1.faeden 1).kopf.rho,
       (arM1.faeden 1).kopf.s0,
       ⟨false, [], arL, .nil, (.ret .empty (by rfl))⟩⟩,
      arS1.spur,
      (arM1.faeden 1).log⟩,
   arM1.lauf ++ rufEigenF 1 [Ereignis.fremd (Sum.inl ARAx.ruf0)],
   arM1.start⟩

theorem arSchrittB : RufSchrittF arP arO 0 arM1 1 arMB := by
  have hhead : (arM1.faeden 1).kopf.rest =
      ⟨false, [], arL, .nil,
        .cons arAxStmtAt (.ret .empty (by rfl))⟩ := rfl
  have hstep : (execStmt arO 0 keinRuf arAxStmtAt
      (arM1.weltVon 1) .nil) =
      Ausgang.ok (D := arD) (V := vertragVon arD (arM1.faeden 1).kopf.f)
        arS1 .nil := rfl
  have hneu : arS1.spur = [Ereignis.fremd (Sum.inl ARAx.ruf0)] ++ (arM1.faeden 1).spur := rfl
  have hkn : ∀ (L : arD.Lock) (h : List arD.Lock),
      Ereignis.nimmt L h ∉ ([Ereignis.fremd (Sum.inl ARAx.ruf0)] : List (Ereignis arD)) := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  exact RufSchrittF.blatt arM1 1 false [] arL arL
    arAxStmtAt _ .nil rfl hhead arM1haelt _ _ _ hstep hneu hkn

theorem arReachB : RufErreichbarF arP arO 0 arM0 arMB :=
  RufErreichbarF.schritt _ _ 1 arReachA arSchrittB

/-- `arM0` IS the start machine. -/
theorem arM0_start : arM0 = RufStartF arP arSp0 arInit := by rfl

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
  simp only [arV100, Int.reduceEq] at hn

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
