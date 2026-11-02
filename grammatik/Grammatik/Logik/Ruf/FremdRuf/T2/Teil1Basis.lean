module

public import Grammatik.Logik.Ruf.FremdRuf.T1

@[expose] public section



namespace Gabbro.Grammatik

/-- After the leaf: memory carries `5` at slot `0`. -/
def fdPC1 : GenMaschine fdD :=
  ⟨(((fdPC0.weltVon 1).lese ([] : List (Res fdD))
      (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
      fdK0 () fdV5).speicher,
   genUpdate fdPC0.spuren 1
     (((fdPC0.weltVon 1).lese ([] : List (Res fdD))
       (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
       fdK0 () fdV5).spur,
   fdPC0.lauf ++ genEigen 1
     [Ereignis.zugriff () true ([] : List (Res fdD)) (fdPC0.weltVon 1).haelt],
   fdPC0.start,
   fdPC0.welten ++
     [((fdPC0.weltVon 1).lese ([] : List (Res fdD))
       (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
       fdK0 () fdV5],
   fdPC0.tiefe + 1⟩

/-- Firing the write from the start world stores `5` at slot `0`. -/
theorem fdPCwrite :
    (execStmt (D := fdD) (V := vertragVon fdD fdArbeit) fdO 0 keinRuf
      fdWriteSt (fdPC0.weltVon 1) Env.nil).welt =
      some (((fdPC0.weltVon 1).lese ([] : List (Res fdD))
        (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
        fdK0 () fdV5) := by rfl

/-- Thread 1 holds nothing at the start, as the leaf demands. -/
theorem fdPC1haelt :
    HeldGenau ([] : List (Res fdD)) (offen (fdPC0.spuren 1)) := by
  have e : offen (fdPC0.spuren 1) = [] := rfl
  rw [e]
  intro L
  exact nomatch L

/-- One PC step: thread 1 fires the writing leaf. -/
theorem fdPCschritt :
    PCSchritt fdP fdO 0 fdProg fdPC0 (fun _ => 0) 1 fdPC1
      (pcAdvance (fun _ => 0) 1) := by
  have hpc : (fdProg 1)[(fun _ => 0) 1]? =
      some (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := rfl
  have hneu : (((fdPC0.weltVon 1).lese ([] : List (Res fdD))
      (fdIdx.orte ++ fdVal5.orte)).schreibSlot () ([] : List (Res fdD))
      fdK0 () fdV5).spur =
      [Ereignis.zugriff () true ([] : List (Res fdD))
        (fdPC0.weltVon 1).haelt] ++ fdPC0.spuren 1 := rfl
  have hkn : ∀ (L : fdD.Lock) (h : List fdD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true ([] : List (Res fdD))
        (fdPC0.weltVon 1).haelt] := by
    intro L h hm
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
  have hmark : ∀ e ∈ [Ereignis.zugriff () true ([] : List (Res fdD))
      (fdPC0.weltVon 1).haelt], ∀ (m : fdD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := by
    intro e hm m st hlam
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.lambda, List.not_mem_nil] at hlam
  have hcar : ∀ e ∈ [Ereignis.zugriff () true ([] : List (Res fdD))
      (fdPC0.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers
          (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := by
    intro e hm o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [Ereignis.traeger, Option.some.injEq] at ho
    subst ho
    have hc : PCAtom.carriers (D := fdD)
        (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) =
        [Sum.inl (())] := rfl
    rw [hc]
    exact List.Mem.head _
  exact PCSchritt.leaf fdPC0 (fun _ => 0) 1
    (vertragVon fdD fdArbeit) false [] [] []
    fdWriteSt Env.nil rfl fdPC1haelt _ _ fdPCwrite hneu hkn
    [] [Sum.inl ()] hpc rfl hmark hcar

/-- The witness run from `GenStart`: the writing leaf. -/
theorem fdPC_erreicht :
    PCReach fdP fdO 0 fdProg (GenStart fdSp0) fdPC1
      (pcAdvance (fun _ => 0) 1) :=
  PCReach.step _ _ _ _ _ PCReach.start fdPCschritt

/-- The final memory carries `5` at slot `0`. -/
theorem fdPC_slot5 : fdPC1.speicher.slots () 0 () = fdV5 := by
  have hhit := storeSlot_hit (D := fdD)
    ((fdPC0.weltVon 1).lese ([] : List (Res fdD))
      (fdIdx.orte ++ fdVal5.orte)) () fdK0 () fdV5
  have k0 : fdK0 = (0 : Int) := rfl
  have hmem : fdPC1.speicher.slots () 0 () =
      ((((fdPC0.weltVon 1).lese ([] : List (Res fdD))
        (fdIdx.orte ++ fdVal5.orte)).storeSlot ()
        fdK0 () fdV5).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

/-- Memory really moved: slot `0` reads `5`, the start reads `0`. -/
theorem fdPC_schreibt : fdPC1.speicher.slots () 0 () ≠
    fdSp0.slots () 0 () := by
  have h5 := fdPC_slot5
  have h0 : fdSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert fdD (fdD.typ () ())) := rfl
  rw [h5, h0]
  intro hcon
  have hn : (fdV5.n) = ((⟨0, by decide, by decide⟩ :
      Wert fdD (fdD.typ () ())).n) := congrArg Zahl.n hcon
  simp only [fdV5, Int.reduceEq] at hn

/-! ## 8. Witnesses: joint premises on a non-degenerate program -/

/-- ZEUGE: every premise of `fremdruf_offen_lesen` holds jointly on
    the fixture -- the handing-out gate answers descriptor `3`, the
    reading gate is called with descriptor `3` and answers count `0`,
    both answers meet the declared ensures, both steps keep the
    gate-declared frames -- and the program is non-degenerate: the
    function writes the table and a reached run moves memory
    (`0 -> 5` at slot `0`). -/
theorem fremdruf_fd_zeuge :
    ∃ (σ : World fdD) (ρo : Env fdD (fdD.aparams fdOpen))
      (ρr : Env fdD (fdD.aparams fdRead))
      (v : ErgVal fdD (fdD.aerg fdOpen)) (w : ErgVal fdD (fdD.aerg fdRead)),
      GutO fdO ∧ AxVertragO fdQ fdO ∧
      fdGateOpen.eff = fdD.aschreibt fdOpen ∧
      fdGateOpen.effG = fdD.agschreibt fdOpen ∧
      fdGateRead.eff = fdD.aschreibt fdRead ∧
      fdGateRead.effG = fdD.agschreibt fdRead ∧
      einpassenErg fdO.zeiger (fdD.aerg fdOpen) (fdO.wirkt fdOpen σ ρo).2 = some v ∧
      einpassenErg fdO.zeiger (fdD.aerg fdRead)
        (fdO.wirkt fdRead (fdO.wirkt fdOpen σ ρo).1 ρr).2 = some w ∧
      fdD.schreibt fdArbeit () = true ∧
      ∃ (M : GenMaschine fdD) (pc : PCStand),
        PCReach fdP fdO 0 fdProg (GenStart fdSp0) M pc ∧
        M.speicher.slots () 0 () ≠ fdSp0.slots () 0 () :=
  ⟨fdWelt0, Env.nil, fdRho3, fdV3, fdW0,
    fdO_gut, fdQ_vertrag,
    fdGateOpen_eff, fdGateOpen_effG, fdGateRead_eff, fdGateRead_effG,
    fdFitO, fdFitR, rfl,
    fdPC1, _, fdPC_erreicht, fdPC_schreibt⟩

/-- Companion of `fremdruf_offen_lesen`: its premises, jointly. -/
theorem fremdruf_offen_lesen_zeuge :
    ∃ (gOpen gRead : GateData fdD) (σ : World fdD)
      (ρo : Env fdD (fdD.aparams fdOpen)) (ρr : Env fdD (fdD.aparams fdRead))
      (v : ErgVal fdD (fdD.aerg fdOpen)) (w : ErgVal fdD (fdD.aerg fdRead)),
      GutO fdO ∧ AxVertragO fdQ fdO ∧
      gOpen.eff = fdD.aschreibt fdOpen ∧
      gOpen.effG = fdD.agschreibt fdOpen ∧
      gRead.eff = fdD.aschreibt fdRead ∧
      gRead.effG = fdD.agschreibt fdRead ∧
      einpassenErg fdO.zeiger (fdD.aerg fdOpen) (fdO.wirkt fdOpen σ ρo).2 = some v ∧
      einpassenErg fdO.zeiger (fdD.aerg fdRead)
        (fdO.wirkt fdRead (fdO.wirkt fdOpen σ ρo).1 ρr).2 = some w := by
  obtain ⟨σ, ρo, ρr, v, w, hO, hQ, hEO, hEGO, hER, hEGR, hfO, hfR, _, _, _, _, _⟩ :=
    fremdruf_fd_zeuge
  exact ⟨fdGateOpen, fdGateRead, σ, ρo, ρr, v, w,
    hO, hQ, hEO, hEGO, hER, hEGR, hfO, hfR⟩

/-- Companion of `fremdruf_gate_gilt`: its premises, jointly. -/
theorem fremdruf_gate_gilt_zeuge :
    ∃ (g : GateData fdD) (a : fdD.Ax) (σ : World fdD)
      (ρ : Env fdD (fdD.aparams a)) (v : ErgVal fdD (fdD.aerg a)),
      GutO fdO ∧ AxVertragO fdQ fdO ∧
      g.eff = fdD.aschreibt a ∧ g.effG = fdD.agschreibt a ∧
      einpassenErg fdO.zeiger (fdD.aerg a) (fdO.wirkt a σ ρ).2 = some v :=
  ⟨fdGateOpen, fdOpen, fdWelt0, Env.nil, fdV3,
    fdO_gut, fdQ_vertrag, fdGateOpen_eff, fdGateOpen_effG, fdFitO⟩


end Gabbro.Grammatik
