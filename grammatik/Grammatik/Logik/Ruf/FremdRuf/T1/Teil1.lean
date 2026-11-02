module
public import Grammatik.Logik.Ruf.FremdRuf.T1.Teil1Basis
import all Grammatik.Logik.Ruf.FremdRuf.T1.Teil1Basis

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Zielsatz.Kern.Spec

@[expose] public section



namespace Gabbro.Grammatik
/-- Recording of the handing-out call over the complete domains. -/
theorem fdO_spur_open (σ : World fdD) (ρ : Env fdD (fdD.aparams true))
    (hgt : ∀ t, fdD.aschreibt true t = true → ∀ L, Sum.inl L ∈ fdD.braucht t → L ∈ σ.haelt)
    (hgg : ∀ g, fdD.agschreibt true g = true → ∀ L, Sum.inl L ∈ fdD.gbraucht g → L ∈ σ.haelt) :
    ∃ tabs : List fdD.Tab, ∃ globs : List fdD.Glob, ∃ Λe : List (Res fdD),
      (∀ t, fdD.aschreibt true t = true → t ∈ tabs) ∧
      (∀ g, fdD.agschreibt true g = true → g ∈ globs) ∧
      (∀ t, fdD.aschreibt true t = true → darf fdD t Λe) ∧
      (∀ g, fdD.agschreibt true g = true → gdarf fdD g Λe) ∧
      (∀ m st, Res.marke m st ∉ Λe) ∧
      HeldIn Λe σ.haelt ∧
      (fdO.wirkt true σ ρ).1.spur = axiomSpur tabs globs true Λe σ.haelt ++ σ.spur := by
  refine ⟨[()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact fdTab_mem t
  · intro g hg
    exact nomatch g
  · intro t _
    exact fdD_darf t
  · intro g hg
    exact nomatch g
  · intro m st hm
    exact nomatch m
  · exact fdHeldIn_nil _
  · rfl

/-- Recording of the reading call over the complete domains. -/
theorem fdO_spur_read (σ : World fdD) (ρ : Env fdD (fdD.aparams false))
    (hgt : ∀ t, fdD.aschreibt false t = true → ∀ L, Sum.inl L ∈ fdD.braucht t → L ∈ σ.haelt)
    (hgg : ∀ g, fdD.agschreibt false g = true → ∀ L, Sum.inl L ∈ fdD.gbraucht g → L ∈ σ.haelt) :
    ∃ tabs : List fdD.Tab, ∃ globs : List fdD.Glob, ∃ Λe : List (Res fdD),
      (∀ t, fdD.aschreibt false t = true → t ∈ tabs) ∧
      (∀ g, fdD.agschreibt false g = true → g ∈ globs) ∧
      (∀ t, fdD.aschreibt false t = true → darf fdD t Λe) ∧
      (∀ g, fdD.agschreibt false g = true → gdarf fdD g Λe) ∧
      (∀ m st, Res.marke m st ∉ Λe) ∧
      HeldIn Λe σ.haelt ∧
      (fdO.wirkt false σ ρ).1.spur = axiomSpur tabs globs false Λe σ.haelt ++ σ.spur := by
  refine ⟨[()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    exact fdTab_mem t
  · intro g hg
    exact nomatch g
  · intro t _
    exact fdD_darf t
  · intro g hg
    exact nomatch g
  · intro m st hm
    exact nomatch m
  · exact fdHeldIn_nil _
  · rfl

/-- The oracle stays in its declared frames and records its writes. -/
theorem fdO_gut : GutO fdO := by
  intro a σ ρ
  cases a with
  | true =>
    refine ⟨fdO_rahmen_open σ ρ, fdO_haelt_open σ ρ, fun hgt hgg => ?_⟩
    exact fdO_spur_open σ ρ hgt hgg
  | false =>
    refine ⟨fdO_rahmen_read σ ρ, fdO_haelt_read σ ρ, fun hgt hgg => ?_⟩
    exact fdO_spur_read σ ρ hgt hgg

/-- The handing-out gate's answer world carries its marker: slot `1`
    reads `5`, whatever the world before. -/
theorem fdO_open_marke (σ : World fdD) (ρ : Env fdD (fdD.aparams true)) :
    ((fdO.wirkt true σ ρ).1.slots () 1 ()).n = 5 := by
  have hs : ((fdO.wirkt true σ ρ).1.slots () 1 ()) =
      (⟨5, by decide, by decide⟩ : Wert fdD (fdD.typ () ())) :=
    storeSlot_hit (D := fdD) σ () 1 () ⟨5, by decide, by decide⟩
  rw [hs]

/-- The oracle meets the declared ensures of both gates. -/
theorem fdQ_vertrag : AxVertragO fdQ fdO := by
  intro a σ ρ v h
  cases a with
  | true =>
    show decide (((fdO.wirkt true σ ρ).1.slots () 1 ()).n = 5) = true
    exact decide_eq_true (fdO_open_marke σ ρ)
  | false =>
    have hred : einpassenErg fdO.zeiger (fdD.aerg false) (fdO.wirkt false σ ρ).2
        = einpassen (D := fdD) fdO.zeiger (.int 0 100) (σ.slots () 0 ()).n := rfl
    rw [hred] at h
    simp only [einpassen] at h
    split at h
    next hcond =>
      have e : (⟨(σ.slots () 0 ()).n, hcond.1, hcond.2⟩ :
          Wert fdD (.int 0 100)) = v :=
        Option.some_inj.mp h
      subst e
      show decide (((⟨(σ.slots () 0 ()).n, hcond.1, hcond.2⟩ :
          Wert fdD (.int 0 100)) : Zahl 0 100).n
        = ((fdO.wirkt false σ ρ).1.slots () 0 ()).n) = true
      exact decide_eq_true rfl
    next hcond =>
      have hslot : (0 : Int) ≤ (σ.slots () 0 ()).n ∧ (σ.slots () 0 ()).n ≤ (100 : Int) :=
        Val.int_bereich (σ.slots () 0 ())
      exact absurd hslot hcond

/-! ## 5. Gates as data, answers only by ensures -/

/-- The open gate as program data: an illustration dispatch label with
    abstract register bindings, a cost bound and the declared effects.
    The label, bindings and cost constrain no answer; only the effects
    must match the frame (see `fremdruf_gate_gilt`). -/
def fdGateOpen : GateData fdD :=
  { num := 1001, regs := [0], kosten := 40, eff := fun _ => true,
    effG := fun g => nomatch g }

/-- The read gate as program data: a different illustration label. -/
def fdGateRead : GateData fdD :=
  { num := 1002, regs := [0, 1], kosten := 40, eff := fun _ => true,
    effG := fun g => nomatch g }

/-- The two illustration labels differ: two gates, not one. -/
theorem fdGate_num : fdGateOpen.num ≠ fdGateRead.num := by decide

/-- The open gate declares the frame it runs in. -/
theorem fdGateOpen_eff : fdGateOpen.eff = fdD.aschreibt fdOpen := by rfl

/-- The open gate declares no global writes. -/
theorem fdGateOpen_effG : fdGateOpen.effG = fdD.agschreibt fdOpen := by rfl

/-- The read gate declares the frame it runs in. -/
theorem fdGateRead_eff : fdGateRead.eff = fdD.aschreibt fdRead := by rfl

/-- The read gate declares no global writes. -/
theorem fdGateRead_effG : fdGateRead.effG = fdD.agschreibt fdRead := by rfl

/-- One gate call: the fitting answer meets the declared ensures and
    the step keeps the gate-declared frame. The dispatch label, the
    register bindings and the cost appear nowhere: answers are
    constrained only by the ensures, memory only by the frame. Every
    premise is used: `hQ` gives the ensures, `hO` the frame,
    `hEff`/`hEffG` restate it in the gate's own effect terms. -/
theorem fremdruf_gate_gilt (g : GateData fdD) (a : fdD.Ax) (O : Orakel fdD) (Q : AxEns fdD)
    (hO : GutO O) (hQ : AxVertragO Q O)
    (hEff : g.eff = fdD.aschreibt a) (hEffG : g.effG = fdD.agschreibt a)
    (σ : World fdD) (ρ : Env fdD (fdD.aparams a))
    (v : ErgVal fdD (fdD.aerg a))
    (hfit : einpassenErg O.zeiger (fdD.aerg a) (O.wirkt a σ ρ).2 = some v) :
    Q a (O.wirkt a σ ρ).1 v = true ∧
    Rahmen g.eff g.effG σ (O.wirkt a σ ρ).1 := by
  refine ⟨hQ a σ ρ v hfit, ?_⟩
  have hfr := (hO a σ ρ).1
  rw [hEff, hEffG]
  exact hfr

/-- Open then read: both fitting answers meet their declared ensures
    and both steps keep their gate-declared frames. The descriptor
    itself is never computed on; no label, binding or cost is
    consulted. Every premise is used through the two single-gate
    facts. -/
theorem fremdruf_offen_lesen (gOpen gRead : GateData fdD)
    (O : Orakel fdD) (Q : AxEns fdD)
    (hO : GutO O) (hQ : AxVertragO Q O)
    (hEffO : gOpen.eff = fdD.aschreibt fdOpen)
    (hEffGO : gOpen.effG = fdD.agschreibt fdOpen)
    (hEffR : gRead.eff = fdD.aschreibt fdRead)
    (hEffGR : gRead.effG = fdD.agschreibt fdRead)
    (σ : World fdD) (ρo : Env fdD (fdD.aparams fdOpen))
    (ρr : Env fdD (fdD.aparams fdRead))
    (v : ErgVal fdD (fdD.aerg fdOpen)) (w : ErgVal fdD (fdD.aerg fdRead))
    (hfitO : einpassenErg O.zeiger (fdD.aerg fdOpen) (O.wirkt fdOpen σ ρo).2 = some v)
    (hfitR : einpassenErg O.zeiger (fdD.aerg fdRead)
      (O.wirkt fdRead (O.wirkt fdOpen σ ρo).1 ρr).2 = some w) :
    Q fdOpen (O.wirkt fdOpen σ ρo).1 v = true ∧
    Rahmen gOpen.eff gOpen.effG σ (O.wirkt fdOpen σ ρo).1 ∧
    Q fdRead (O.wirkt fdRead (O.wirkt fdOpen σ ρo).1 ρr).1 w = true ∧
    Rahmen gRead.eff gRead.effG (O.wirkt fdOpen σ ρo).1
      (O.wirkt fdRead (O.wirkt fdOpen σ ρo).1 ρr).1 := by
  obtain ⟨hQo, hRo⟩ :=
    fremdruf_gate_gilt gOpen fdOpen O Q hO hQ hEffO hEffGO σ ρo v hfitO
  obtain ⟨hQr, hRr⟩ :=
    fremdruf_gate_gilt gRead fdRead O Q hO hQ hEffR hEffGR _ ρr w hfitR
  exact ⟨hQo, hRo, hQr, hRr⟩

/-- The witness oracle ignores the descriptor: `fdO`'s reading gate
    answers the current slot value no matter which descriptor value it
    is passed. A property of this one oracle, not of every oracle and
    not of the language (a real read gate's answer depends on the fd). -/
theorem fd_opak (σ : World fdD) (ρ1 ρ2 : Env fdD (fdD.aparams fdRead)) :
    (fdO.wirkt fdRead σ ρ1).2 = (fdO.wirkt fdRead σ ρ2).2 := by rfl

/-! ## 6. Start memory, the wrong ensures, the program -/

/-- Start memory: every slot reads `0`. -/
def fdSp0 : Speicher fdD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Start world: start memory with an empty trace. -/
def fdWelt0 : World fdD := fdSp0.welt []

/-- A wrong ensures for the handing-out gate: demands descriptor `6`
    while the oracle answers `3`. -/
def fdQfalsch : AxEns fdD
  | true, _, v => decide ((v : Zahl 0 7).n = 6)
  | false, σ', v => decide ((v : Zahl 0 100).n = (σ'.slots () 0 ()).n)

/-- Planted defect, rejected: no oracle answering `3` meets an ensures
    demanding `6`. A proof attempt for `AxVertragO fdQfalsch fdO`
    fails at the `3 = 6` obligation. -/
theorem fremdruf_falsch_abgelehnt : ¬ AxVertragO fdQfalsch fdO := by
  intro hcon
  have hfit3 : einpassenErg fdO.zeiger (fdD.aerg true)
        (fdO.wirkt true fdWelt0 Env.nil).2
        = some (⟨3, by decide, by decide⟩ : Wert fdD (.int 0 7)) := by
    have hred : einpassenErg fdO.zeiger (fdD.aerg true)
          (fdO.wirkt true fdWelt0 Env.nil).2
          = einpassen (D := fdD) fdO.zeiger (.int 0 7) 3 := rfl
    rw [hred]
    simp only [einpassen]
    split
    next hcond => rfl
    next hcond =>
      have hpos : (0 : Int) ≤ (3 : Int) ∧ (3 : Int) ≤ (7 : Int) := by decide
      exact absurd hpos hcond
  have h3 := hcon true fdWelt0 Env.nil _ hfit3
  have h3d : decide (((⟨3, by decide, by decide⟩ : Wert fdD (.int 0 7)) :
      Zahl 0 7).n = 6) = true := h3
  have h6 : (3 : Int) = 6 := of_decide_eq_true h3d
  omega

/-- The program: true everywhere, write-only body below. -/
def fdP : Programm fdD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret .empty (by rfl)

/-- Index `0` into the two-slot table. -/
def fdIdx : Expr fdD [] ([] : List (Res fdD)) (.index (fdD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The stored value `5` in range. -/
def fdVal5 : Expr fdD [] ([] : List (Res fdD)) (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 5)

/-- The write `konto[0] := 5` at empty holdings. -/
def fdWriteSt : Stmt fdD (vertragVon fdD fdArbeit) false [] [] [] :=
  .assignSlot () () fdIdx fdVal5 rfl (fdD_darf ())

/-- The handed-out descriptor value `3` as an answer. -/
def fdV3 : ErgVal fdD (fdD.aerg fdOpen) := ⟨3, by decide, by decide⟩

end Gabbro.Grammatik
