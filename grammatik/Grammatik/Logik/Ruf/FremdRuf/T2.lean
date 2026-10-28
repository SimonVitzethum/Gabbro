/- Part 2 of 3 of `FremdRuf` (split by instrumente/teile/lean-teilen.py; the umbrella `FremdRuf.lean` imports all parts). -/
import Grammatik.Logik.Ruf.FremdRuf.T1

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
        fdK0 () fdV5) := rfl

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

/-! ## 9. Argument preconditions: the caller's half of a gate contract

  Fix lane F5 (review G10 F5, G04 F2). `AxVertragO` quantifies over EVERY
  argument environment: the declared ensures must hold whatever the caller
  passes. A real gate's behaviour depends on well-formed arguments (a
  NUL-terminated path for `open`, a descriptor that is open for `read`), so
  under `AxVertragO` alone a CALLER bug is booked as a failed hardware
  assumption. This section splits the premise:

  * `AxPre` -- the gate's declared argument precondition (its `requires`),
    over the call-time world and the passed arguments;
  * `AxVertragOP Pre Q O` -- the hardware premise restricted to calls that
    meet it (weaker than `AxVertragO`: `axVertragOP_of_O`);
  * `AufruferPflicht Pre a σ ρ` -- the caller's obligation at one call site,
    user logic (the `V` obligation `gabbro obligations` counts at every call
    of a gate with `requires`).

  At a call that meets the caller's obligation the restricted premise
  delivers exactly what the full one did (`fremdruf_gate_gilt_pre`). And
  the goal theorem is not touched: from the restricted premise the machine's
  oracle is re-dressed as one that meets the FULL premise (c) of
  `gabbro_ziel` (`hardware_aus_vertragP`: ill-formed calls answer a raw
  word outside the declared result type) and that agrees with the machine's
  oracle on every well-formed call (`mitVorbedingung_gleich`).
  `Spec.lean` is unchanged. -/

/-- A per-gate argument precondition: the declared `requires`, over the
    world at the call and the passed arguments. -/
abbrev AxPre (D : Deklaration) := ∀ a : D.Ax, World D → Env D (D.aparams a) → Bool

/-- The hardware premise restricted to well-formed calls: whenever the
    caller met the gate's precondition and the raw answer fits the declared
    result type, the declared ensures holds. -/
def AxVertragOP {D : Deklaration} (Pre : AxPre D) (Q : AxEns D) (O : Orakel D) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (v : ErgVal D (D.aerg a)),
    Pre a σ ρ = true →
    einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v → Q a (O.wirkt a σ ρ).1 v = true

/-- The caller's obligation at one call site: its arguments meet the gate's
    precondition. User logic, not hardware. -/
def AufruferPflicht {D : Deklaration} (Pre : AxPre D) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) : Prop :=
  Pre a σ ρ = true

/-- The restricted premise is weaker: every oracle meeting the full premise
    meets it, for every precondition. -/
theorem axVertragOP_of_O {D : Deklaration} (Pre : AxPre D) {Q : AxEns D} {O : Orakel D}
    (h : AxVertragO Q O) : AxVertragOP Pre Q O :=
  fun a σ ρ v _ hfit => h a σ ρ v hfit

/-- One gate call under the split premise: the caller's obligation plus the
    restricted hardware premise give the fitting answer's ensures, and the
    frame premise gives the gate-declared frame. Every premise is used:
    `hPflicht` and `hQ` give the ensures, `hO` the frame, `hEff`/`hEffG`
    restate it in the gate's own effect terms. -/
theorem fremdruf_gate_gilt_pre (g : GateData fdD) (a : fdD.Ax) (O : Orakel fdD)
    (Pre : AxPre fdD) (Q : AxEns fdD)
    (hO : GutO O) (hQ : AxVertragOP Pre Q O)
    (hEff : g.eff = fdD.aschreibt a) (hEffG : g.effG = fdD.agschreibt a)
    (σ : World fdD) (ρ : Env fdD (fdD.aparams a))
    (hPflicht : AufruferPflicht Pre a σ ρ)
    (v : ErgVal fdD (fdD.aerg a))
    (hfit : einpassenErg O.zeiger (fdD.aerg a) (O.wirkt a σ ρ).2 = some v) :
    Q a (O.wirkt a σ ρ).1 v = true ∧
    Rahmen g.eff g.effG σ (O.wirkt a σ ρ).1 := by
  refine ⟨hQ a σ ρ v hPflicht hfit, ?_⟩
  have hfr := (hO a σ ρ).1
  rw [hEff, hEffG]
  exact hfr

/-- The machine's oracle, re-dressed: the same answer world everywhere, the
    same raw answer on every well-formed call, and on an ill-formed call the
    raw word `raus a` (chosen outside the declared result type). -/
def mitVorbedingung {D : Deklaration} (Pre : AxPre D) (O : Orakel D) (raus : D.Ax → Int) :
    Orakel D :=
  { O with wirkt := fun a σ ρ =>
      ((O.wirkt a σ ρ).1, if Pre a σ ρ = true then (O.wirkt a σ ρ).2 else raus a) }

/-- On a well-formed call the re-dressed oracle IS the machine's oracle. -/
theorem mitVorbedingung_gleich {D : Deklaration} (Pre : AxPre D) (O : Orakel D)
    (raus : D.Ax → Int) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    (h : AufruferPflicht Pre a σ ρ) :
    (mitVorbedingung Pre O raus).wirkt a σ ρ = O.wirkt a σ ρ := by
  have h' : Pre a σ ρ = true := h
  show ((O.wirkt a σ ρ).1, if Pre a σ ρ = true then (O.wirkt a σ ρ).2 else raus a) =
    O.wirkt a σ ρ
  rw [if_pos h']

/-- **The bridge to premise (c) of `gabbro_ziel`.** Frame, register
    locality and the restricted ensures of the machine's oracle, plus raw
    words outside every declared result type, give the FULL hardware
    premise `HardwareAnnahmen` for the re-dressed oracle. The ill-formed
    calls are exactly the ones whose answers no longer fit. -/
theorem hardware_aus_vertragP {D : Deklaration} (Pre : AxPre D) (Q : AxEns D) (O : Orakel D)
    (raus : D.Ax → Int)
    (hO : GutO O) (hR : RegLokal O) (hQ : AxVertragOP Pre Q O)
    (hraus : ∀ a, einpassenErg O.zeiger (D.aerg a) (raus a) = none) :
    Zielsatz.HardwareAnnahmen (mitVorbedingung Pre O raus) Q := by
  refine ⟨fun a σ ρ => hO a σ ρ, hR, ?_⟩
  intro a σ ρ v hfit
  by_cases hp : Pre a σ ρ = true
  · have e := mitVorbedingung_gleich Pre O raus a σ ρ hp
    rw [e] at hfit ⊢
    exact hQ a σ ρ v hp hfit
  · have hn : ((mitVorbedingung Pre O raus).wirkt a σ ρ).2 = raus a := by
      show (if Pre a σ ρ = true then (O.wirkt a σ ρ).2 else raus a) = raus a
      rw [if_neg hp]
    have hz : (mitVorbedingung Pre O raus).zeiger = O.zeiger := rfl
    rw [hn, hz, hraus a] at hfit
    exact absurd hfit (by simp only [reduceCtorEq, not_false_eq_true])

/-! ### The fixture's preconditions, and an oracle only the split premise admits -/

/-- The descriptor a read call passes. -/
def fdKopf : Env fdD (fdD.aparams fdRead) → Int
  | .cons w _ => (w : Zahl 0 7).n

/-- The fixture's gate preconditions. `open`: the terminator of the path
    frame stands -- slot `1` reads `0` (the analog of example 149's
    `path_nul_terminated`; the open gate itself overwrites it with its
    marker `5`, so a second open without a fresh terminator is ill-formed).
    `read`: the descriptor passed is the one the open gate hands out (`3`). -/
def fdPre : AxPre fdD
  | true, σ, _ => decide ((σ.slots () 1 ()).n = 0)
  | false, _, ρ => decide (fdKopf ρ = 3)

/-- An oracle that keeps its contract on well-formed calls only: an open or
    a read with the handed-out descriptor answers as `fdO`; a read with any
    OTHER descriptor answers the slot value plus one -- the kernel's
    garbage for a caller's bug. -/
def fdObad : Orakel fdD where
  wirkt
    | true, σ, ρ => fdO.wirkt true σ ρ
    | false, σ, ρ => ((fdO.wirkt false σ ρ).1,
        if fdKopf ρ = 3 then (fdO.wirkt false σ ρ).2 else (σ.slots () 0 ()).n + 1)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- The bad oracle keeps the frames: its answer worlds are `fdO`'s. -/
theorem fdObad_gut : GutO fdObad := by
  intro a σ ρ
  cases a with
  | true => exact fdO_gut true σ ρ
  | false => exact fdO_gut false σ ρ

/-- The bad oracle meets the RESTRICTED premise: on every well-formed call
    it answers as `fdO`, which meets the full one. -/
theorem fdObad_vertragP : AxVertragOP fdPre fdQ fdObad := by
  intro a σ ρ v hp hfit
  cases a with
  | true => exact fdQ_vertrag true σ ρ v hfit
  | false =>
    have h3 : fdKopf ρ = 3 := of_decide_eq_true hp
    have e : fdObad.wirkt false σ ρ = fdO.wirkt false σ ρ := by
      show ((fdO.wirkt false σ ρ).1,
          if fdKopf ρ = 3 then (fdO.wirkt false σ ρ).2 else (σ.slots () 0 ()).n + 1) =
        fdO.wirkt false σ ρ
      rw [if_pos h3]
    rw [e] at hfit ⊢
    exact fdQ_vertrag false σ ρ v hfit

/-- A read call with descriptor `5`: not the handed-out one. -/
def fdRho5 : Env fdD (fdD.aparams fdRead) :=
  Env.cons (⟨5, by decide, by decide⟩ : Wert fdD (.int 0 7)) Env.nil

/-- The ill-formed read breaks the caller's obligation. -/
theorem fdPflicht_verletzt : ¬ AufruferPflicht fdPre fdRead fdWelt0 fdRho5 := by
  intro h
  have h' : decide (fdKopf fdRho5 = 3) = true := h
  have h5 : fdKopf fdRho5 = 3 := of_decide_eq_true h'
  have e : fdKopf fdRho5 = 5 := rfl
  omega

/-- **The split is load-bearing.** The bad oracle does NOT meet the full
    premise: its answer to the ill-formed read (`1`, while slot `0` reads
    `0`) fits and breaks the ensures. Under `AxVertragO` alone this caller
    bug would be the hardware's; under the split it is the caller's
    (`fdPflicht_verletzt`), and the hardware premise holds
    (`fdObad_vertragP`). -/
theorem fdObad_nicht_voll : ¬ AxVertragO fdQ fdObad := by
  intro h
  have hred : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
      (fdObad.wirkt fdRead fdWelt0 fdRho5).2
      = einpassen (D := fdD) fdObad.zeiger (.int 0 100) 1 := rfl
  have hfit : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
      (fdObad.wirkt fdRead fdWelt0 fdRho5).2
      = some (⟨1, by decide, by decide⟩ : Wert fdD (.int 0 100)) := by
    rw [hred]
    simp only [einpassen]
    split
    next hcond => rfl
    next hcond =>
      have hpos : (0 : Int) ≤ (1 : Int) ∧ (1 : Int) ≤ (100 : Int) := by decide
      exact absurd hpos hcond
  have hq := h fdRead fdWelt0 fdRho5 _ hfit
  have hq' : decide ((1 : Int) = (fdSp0.slots () 0 ()).n) = true := hq
  have h1 : (1 : Int) = (fdSp0.slots () 0 ()).n := of_decide_eq_true hq'
  have h0 : (fdSp0.slots () 0 ()).n = 0 := rfl
  omega

/-- The raw word the re-dressed oracle answers on an ill-formed call:
    `101`, outside both declared result types. -/
def fdRaus : fdD.Ax → Int := fun _ => 101

/-- `101` fits neither declared result type. -/
theorem fdRaus_passt_nicht (a : fdD.Ax) :
    einpassenErg fdObad.zeiger (fdD.aerg a) (fdRaus a) = none := by
  cases a with
  | true =>
    show einpassen (D := fdD) fdObad.zeiger (.int 0 7) 101 = none
    simp only [einpassen]
    split
    next hcond => exact absurd hcond.2 (by decide)
    next => rfl
  | false =>
    show einpassen (D := fdD) fdObad.zeiger (.int 0 100) 101 = none
    simp only [einpassen]
    split
    next hcond => exact absurd hcond.2 (by decide)
    next => rfl

/-- The fixture has no registers and no globals: register locality holds
    vacuously for every oracle over it. -/
theorem fdObad_regLokal : RegLokal fdObad :=
  ⟨fun r => (nomatch r), fun g => (nomatch g)⟩

/-- The world after the open call at the witness site. -/
def fdWelt1 : World fdD := (fdObad.wirkt fdOpen fdWelt0 Env.nil).1

/-- The read fit of the bad oracle at the well-formed witness call: the
    slot still reads `0`. -/
theorem fdObadFitR : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
    (fdObad.wirkt fdRead fdWelt1 fdRho3).2 = some fdW0 := by
  have hred : einpassenErg fdObad.zeiger (fdD.aerg fdRead)
        (fdObad.wirkt fdRead fdWelt1 fdRho3).2
        = einpassen (D := fdD) fdObad.zeiger (.int 0 100) 0 := rfl
  rw [hred]
  simp only [einpassen]
  split
  next hcond => rfl
  next hcond =>
    have hpos : (0 : Int) ≤ (0 : Int) ∧ (0 : Int) ≤ (100 : Int) := by decide
    exact absurd hpos hcond

/-- ZEUGE: every premise of `fremdruf_gate_gilt_pre` holds jointly on the
    fixture with the BAD oracle -- frame, restricted premise, the read gate's
    declared effects, the caller's obligation at a well-formed read after
    the open (descriptor `3`), a fitting answer -- and the witness is
    non-degenerate: the same oracle breaks the full premise
    (`fdObad_nicht_voll`), the precondition is false at another call
    (`fdPflicht_verletzt`), and the open gate's own precondition held
    at the start world (the terminator stood) and fails after it (the
    marker overwrote it). -/
theorem fremdruf_gate_gilt_pre_zeuge :
    ∃ (g : GateData fdD) (σ : World fdD) (ρ : Env fdD (fdD.aparams fdRead))
      (v : ErgVal fdD (fdD.aerg fdRead)),
      GutO fdObad ∧ AxVertragOP fdPre fdQ fdObad ∧
      g.eff = fdD.aschreibt fdRead ∧ g.effG = fdD.agschreibt fdRead ∧
      AufruferPflicht fdPre fdRead σ ρ ∧
      einpassenErg fdObad.zeiger (fdD.aerg fdRead) (fdObad.wirkt fdRead σ ρ).2 = some v ∧
      ¬ AxVertragO fdQ fdObad ∧
      ¬ AufruferPflicht fdPre fdRead fdWelt0 fdRho5 ∧
      AufruferPflicht fdPre fdOpen fdWelt0 Env.nil ∧
      ¬ AufruferPflicht fdPre fdOpen fdWelt1 Env.nil := by
  refine ⟨fdGateRead, fdWelt1, fdRho3, fdW0, fdObad_gut, fdObad_vertragP,
    fdGateRead_eff, fdGateRead_effG, ?_, fdObadFitR, fdObad_nicht_voll,
    fdPflicht_verletzt, ?_, ?_⟩
  · show decide (fdKopf fdRho3 = 3) = true
    exact decide_eq_true rfl
  · show decide ((fdWelt0.slots () 1 ()).n = 0) = true
    exact decide_eq_true rfl
  · intro h
    have h' : decide ((fdWelt1.slots () 1 ()).n = 0) = true := h
    have h0 : (fdWelt1.slots () 1 ()).n = 0 := of_decide_eq_true h'
    have h5 : (fdWelt1.slots () 1 ()).n = 5 := fdO_open_marke fdWelt0 Env.nil
    omega

/-- ZEUGE for the bridge: its premises hold jointly on the bad oracle (the
    one the full premise refuses), so the re-dressed oracle meets premise
    (c) of `gabbro_ziel` in full, and on the well-formed witness read it
    answers exactly as the machine's oracle does. -/
theorem hardware_aus_vertragP_zeuge :
    GutO fdObad ∧ RegLokal fdObad ∧ AxVertragOP fdPre fdQ fdObad ∧
      (∀ a, einpassenErg fdObad.zeiger (fdD.aerg a) (fdRaus a) = none) ∧
      ¬ AxVertragO fdQ fdObad ∧
      Zielsatz.HardwareAnnahmen (mitVorbedingung fdPre fdObad fdRaus) fdQ ∧
      (mitVorbedingung fdPre fdObad fdRaus).wirkt fdRead fdWelt1 fdRho3 =
        fdObad.wirkt fdRead fdWelt1 fdRho3 :=
  ⟨fdObad_gut, fdObad_regLokal, fdObad_vertragP, fdRaus_passt_nicht, fdObad_nicht_voll,
    hardware_aus_vertragP fdPre fdQ fdObad fdRaus fdObad_gut fdObad_regLokal
      fdObad_vertragP fdRaus_passt_nicht,
    mitVorbedingung_gleich fdPre fdObad fdRaus fdRead fdWelt1 fdRho3
      (show decide (fdKopf fdRho3 = 3) = true from decide_eq_true rfl)⟩

/-! ## 10. From single calls to call sequences (lane 262, OFFEN O23)

  `hardware_aus_vertragP` (§9) bridges one call: on a well-formed call the
  re-dressed oracle IS the machine's oracle (`mitVorbedingung_gleich`). What a
  gate client runs is a SEQUENCE of calls threading worlds -- open, then read
  in the world the open answered. This section lifts the coincidence to such
  sequences, at the oracle layer: if every call of the sequence meets the
  gate's precondition, folding the re-dressed oracle over the sequence gives
  the same worlds and raw answers as folding the machine's oracle.

  This is deliberately NOT a program run: no `Stmt`, no `execStmt`, no
  `bindAxiom` is involved, and nothing here is called a semantics. A machine
  run stepping through gate calls would need the F-machine residue shape
  (see CUTS). What is proved is the oracle-layer coincidence a run-level
  bridge stands on: under the caller's obligations at every call site, the two
  oracles agree on every call of the sequence. -/

/-- A sequence of oracle calls: each call names its gate and carries its own
    argument environment. The world is threaded, not stored: each call runs in
    the world the previous call answered. -/
def rufFolgeWirkt {D : Deklaration} (O : Orakel D) : World D →
    List (Σ a : D.Ax, Env D (D.aparams a)) → World D × List Int
  | σ, [] => (σ, [])
  | σ, ⟨a, ρ⟩ :: rest =>
    let (σ', w) := O.wirkt a σ ρ
    let (σ'', ws) := rufFolgeWirkt O σ' rest
    (σ'', w :: ws)


end Gabbro.Grammatik
