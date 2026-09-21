/-
  File:      Grammatik/FremdRuf.lean
  Subject:   FOREIGN CALLS WITH DESCRIPTOR CARRIERS (lane 233) -- the
             user-declared gate shape: a descriptor as an opaque carrier
             value plus gates as oracle calls whose dispatch labels,
             register bindings, costs and effects are program DATA, with
             answers constrained only by the declared ensures.

  Modelled shape: one gate hands out a descriptor value in a narrow
  carrier range, a second gate takes such a value and answers a count.
  The WITNESS oracle `fdO` ignores the passed descriptor (`fd_opak`, a
  fact about `fdO` only, proved by `rfl`); language-level opacity of the
  carrier is NOT modelled here -- the descriptor is a plain `.int 0 7`
  that expressions may compute on (review G10). Section 9 (fix lane F5)
  splits the gate contract into the caller's argument precondition and
  the hardware premise over well-formed calls, and bridges back to the
  goal theorem's premise (c) without changing it. The goal theorem's
  hardware premise (c) arrives as `GutO` (frame) plus `AxVertragO`
  (declared ensures); the per-gate theorem (`fremdruf_gate_gilt`) and
  the two-gate composition (`fremdruf_offen_lesen`) say exactly that,
  in the gate's own effect terms. Dispatch labels, register bindings
  and costs live only in `GateData` and constrain no answer.

  No dispatch table of any platform is baked in: every label, binding,
  cost and effect below is a field of program data, and the witness
  uses illustration labels only.
-/
import Grammatik.Satz
import Grammatik.AxiomVertrag
import Grammatik.Maschine
import Grammatik.Zielsatz.Spec

namespace Gabbro.Grammatik

/-! ## 1. User-declared gates as data -/

/-- A user-declared gate: the dispatch label, abstract register
    bindings (parameter indices, never platform registers), the cost
    bound, and the declared effects. All DATA of the program; the
    model never consults the label, the bindings or the cost. -/
structure GateData (D : Deklaration) where
  num : Nat
  regs : List Nat
  kosten : Nat
  eff : D.Tab → Bool
  effG : D.Glob → Bool

/-- Gate identity is its data: equal fields give the same gate. -/
theorem gate_daten_gleich {D : Deklaration} {g1 g2 : GateData D}
    (hnum : g1.num = g2.num) (hregs : g1.regs = g2.regs)
    (hkosten : g1.kosten = g2.kosten) (heff : g1.eff = g2.eff)
    (heffG : g1.effG = g2.effG) : g1 = g2 := by
  cases g1
  cases g2
  simp_all

/-! ## 2. The fixture: one table, two gates, one writer -/

/-- Signature of the single function: no parameters, no result, no
    locks, writes the table. -/
def fdSigArbeit : Signatur Unit Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The fixture declaration: one table `konto` of two slots holding
    `0 .. 100`, no locks, no globals; two gates (`true` hands out a
    descriptor in `0 .. 7`, `false` takes one and answers a count in
    `0 .. 100`); both gates may write the table (the managed-state
    analog). One function writes the table. -/
def fdD : Deklaration where
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
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => fdSigArbeit
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Bool
  aparams := fun | true => [] | false => [.int 0 7]
  aerg := fun | true => some (.int 0 7) | false => some (.int 0 100)
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The gate handing out descriptors. -/
def fdOpen : fdD.Ax := true

/-- The gate taking a descriptor and answering a count. -/
def fdRead : fdD.Ax := false

/-- The single function writes the table. -/
def fdArbeit : fdD.Fn := ()

/-- The handing-out gate takes no parameters. -/
theorem fdOpen_params : fdD.aparams fdOpen = [] := rfl

/-- The handing-out gate answers a descriptor in `0 .. 7`. -/
theorem fdOpen_erg : fdD.aerg fdOpen = some (.int 0 7) := rfl

/-- The reading gate takes a descriptor in `0 .. 7`. -/
theorem fdRead_params : fdD.aparams fdRead = [.int 0 7] := rfl

/-- The reading gate answers a count in `0 .. 100`. -/
theorem fdRead_erg : fdD.aerg fdRead = some (.int 0 100) := rfl

/-- Descriptor type flows from answer to parameter: what the first
    gate hands out is what the second gate takes. -/
theorem fd_fluss_typ : fdD.aparams fdRead = [.int 0 7] ∧
    fdD.aerg fdOpen = some (.int 0 7) :=
  ⟨rfl, rfl⟩

/-- The function writes the table (non-degeneracy, first half). -/
theorem fdArbeit_schreibt : fdD.schreibt fdArbeit () = true := rfl

/-! ## 3. Declared ensures and the oracle -/

/-- The declared ensures of the two gates: the handing-out gate
    promises that its answer world carries its marker (slot `1` reads
    `5`) -- any descriptor in `0 .. 7` may come back, `0` included, as
    on a real kernel (review G10 F5: this promised a NONZERO descriptor,
    which is no OS fact); the reading gate promises the count it answers
    is the current slot value. Both read only the answer and the gate's
    own write carrier. -/
def fdQ : AxEns fdD
  | true, σ', _ => decide ((σ'.slots () 1 ()).n = 5)
  | false, σ', v => decide ((v : Zahl 0 100).n = (σ'.slots () 0 ()).n)

/-- The oracle: the handing-out gate stores a marker, records its
    write and answers descriptor value `3`; the reading gate records
    its write, leaves memory alone and answers the current slot
    value. The reading gate never computes on the passed descriptor:
    its answer is independent of the argument (see `fd_opak`). -/
def fdO : Orakel fdD where
  wirkt
    | true, σ, _ => ((σ.storeSlot () 1 () ⟨5, by decide, by decide⟩).merke
        (axiomSpur [()] [] true [] σ.haelt), 3)
    | false, σ, _ => (σ.merke (axiomSpur [()] [] false [] σ.haelt),
        (σ.slots () 0 ()).n)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-! ## 4. The oracle meets frame and ensures -/

/-- The fixture guards nothing, so every access is allowed with no holdings. -/
theorem fdD_darf (t : fdD.Tab) : darf fdD t [] := by
  intro w hw
  have hb : fdD.braucht t = [] := rfl
  rw [hb] at hw
  simp at hw

/-- No holdings are held anywhere: `HeldIn` of the empty list. -/
theorem fdHeldIn_nil (h : List fdD.Lock) : HeldIn ([] : List (Res fdD)) h := by
  intro L hL
  simp at hL

/-- Frame of the handing-out call: the marker write plus the recording. -/
theorem fdO_rahmen_open (σ : World fdD) (ρ : Env fdD (fdD.aparams true)) :
    Rahmen (fdD.aschreibt true) (fdD.agschreibt true) σ (fdO.wirkt true σ ρ).1 := by
  have hss := rahmen_storeSlot (fdD.aschreibt true) (fdD.agschreibt true) σ () 1 ()
    (⟨5, by decide, by decide⟩ : Wert fdD (fdD.typ () ())) rfl
  exact hss.trans (rahmen_gleich rfl rfl)

/-- Frame of the reading call: memory is untouched, only the recording. -/
theorem fdO_rahmen_read (σ : World fdD) (ρ : Env fdD (fdD.aparams false)) :
    Rahmen (fdD.aschreibt false) (fdD.agschreibt false) σ (fdO.wirkt false σ ρ).1 :=
  rahmen_gleich rfl rfl

/-- The handing-out call keeps the held locks: recording only. -/
theorem fdO_haelt_open (σ : World fdD) (ρ : Env fdD (fdD.aparams true)) :
    (fdO.wirkt true σ ρ).1.haelt = σ.haelt := by
  show offen (axiomSpur [()] [] true [] σ.haelt ++ σ.spur) = offen σ.spur
  exact offen_append_zugriffe σ.haelt _ _ (axiomSpur_zugriffMit _ _ _ _ _)

/-- The reading call keeps the held locks: recording only. -/
theorem fdO_haelt_read (σ : World fdD) (ρ : Env fdD (fdD.aparams false)) :
    (fdO.wirkt false σ ρ).1.haelt = σ.haelt := by
  show offen (axiomSpur [()] [] false [] σ.haelt ++ σ.spur) = offen σ.spur
  exact offen_append_zugriffe σ.haelt _ _ (axiomSpur_zugriffMit _ _ _ _ _)

/-- The single table is the complete domain. -/
theorem fdTab_mem (t : fdD.Tab) : t ∈ [()] :=
  List.Mem.head _

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
theorem fdGateOpen_eff : fdGateOpen.eff = fdD.aschreibt fdOpen := rfl

/-- The open gate declares no global writes. -/
theorem fdGateOpen_effG : fdGateOpen.effG = fdD.agschreibt fdOpen := rfl

/-- The read gate declares the frame it runs in. -/
theorem fdGateRead_eff : fdGateRead.eff = fdD.aschreibt fdRead := rfl

/-- The read gate declares no global writes. -/
theorem fdGateRead_effG : fdGateRead.effG = fdD.agschreibt fdRead := rfl

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
    (fdO.wirkt fdRead σ ρ1).2 = (fdO.wirkt fdRead σ ρ2).2 := rfl

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
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := fun _ => .ret .keine (by rfl)

/-- Index `0` into the two-slot table. -/
def fdIdx : Expr fdD [] ([] : List (Res fdD)) (.index (fdD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The stored value `5` in range. -/
def fdVal5 : Expr fdD [] ([] : List (Res fdD)) (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 5)

/-- The write `konto[0] := 5` at empty holdings. -/
def fdWriteSt : Stmt fdD (vertragVon fdD fdArbeit) false [] [] [] :=
  .assignSlot () () fdIdx fdVal5 rfl (fdD_darf ())

/-- The handed-out descriptor value `3` as an answer. -/
def fdV3 : ErgVal fdD (fdD.aerg fdOpen) := ⟨3, by decide, by decide⟩

/-- The read-back count `0` as an answer. -/
def fdW0 : ErgVal fdD (fdD.aerg fdRead) := ⟨0, by decide, by decide⟩

/-- The read call environment, carrying descriptor `3`. -/
def fdRho3 : Env fdD (fdD.aparams fdRead) :=
  Env.cons (⟨3, by decide, by decide⟩ : Wert fdD (.int 0 7)) Env.nil

/-- The open fit at the witness call site. -/
theorem fdFitO : einpassenErg fdO.zeiger (fdD.aerg fdOpen)
    (fdO.wirkt fdOpen fdWelt0 Env.nil).2 = some fdV3 := by
  have hred : einpassenErg fdO.zeiger (fdD.aerg fdOpen)
        (fdO.wirkt fdOpen fdWelt0 Env.nil).2
        = einpassen (D := fdD) fdO.zeiger (.int 0 7) 3 := rfl
  rw [hred]
  simp only [einpassen]
  split
  next hcond => rfl
  next hcond =>
    have hpos : (0 : Int) ≤ (3 : Int) ∧ (3 : Int) ≤ (7 : Int) := by decide
    exact absurd hpos hcond

/-- The read fit at the witness call site: after the open call the
    slot still reads `0`. -/
theorem fdFitR : einpassenErg fdO.zeiger (fdD.aerg fdRead)
    (fdO.wirkt fdRead (fdO.wirkt fdOpen fdWelt0 Env.nil).1 fdRho3).2
    = some fdW0 := by
  have hred : einpassenErg fdO.zeiger (fdD.aerg fdRead)
        (fdO.wirkt fdRead (fdO.wirkt fdOpen fdWelt0 Env.nil).1 fdRho3).2
        = einpassen (D := fdD) fdO.zeiger (.int 0 100) 0 := rfl
  rw [hred]
  simp only [einpassen]
  split
  next hcond => rfl
  next hcond =>
    have hpos : (0 : Int) ≤ (0 : Int) ∧ (0 : Int) ≤ (100 : Int) := by decide
    exact absurd hpos hcond

/-! ## 7. The reached run: one writing leaf -/

/-- Thread program: thread 1 fires the writing leaf, thread 0 rests. -/
def fdProg : PCProg fdD
  | 1 => [.leaf [] [Sum.inl ()]]
  | _ => []

/-- The start machine for the run. -/
def fdPC0 : GenMaschine fdD := GenStart fdSp0

/-- The evaluated index: `0`. -/
def fdK0 : Int := 0

/-- The evaluated value: `5` in range. -/
def fdV5 : Wert fdD (.int 0 100) := ⟨5, by decide, by decide⟩

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
    simp at hm
  have hmark : ∀ e ∈ [Ereignis.zugriff () true ([] : List (Res fdD))
      (fdPC0.weltVon 1).haelt], ∀ (m : fdD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := by
    intro e hm m st hlam
    simp at hm
    subst hm
    simp [Ereignis.lambda] at hlam
  have hcar : ∀ e ∈ [Ereignis.zugriff () true ([] : List (Res fdD))
      (fdPC0.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers
          (PCAtom.leaf ([] : List (Res fdD)) [Sum.inl (())]) := by
    intro e hm o ho
    simp at hm
    subst hm
    simp [Ereignis.traeger] at ho
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
  simp [fdV5] at hn

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
    exact absurd hfit (by simp)

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

/-! ## CUTS: what is not proved.

  - The dispatch labels, register bindings and costs of `GateData`
    are uninterpreted: no theorem connects them to emitted code. That
    is the emitter's stub contract (PLAN-SYSCALL.md S6), not the
    model's. The model shows they constrain no answer and no memory
    step (`fremdruf_gate_gilt`, `fremdruf_offen_lesen` never consult
    `num`, `regs` or `kosten`).
  - The kernel side is a hypothesis, not a verification: there is no
    pairing with a proved dispatch entry (that is `SyscallPaarung`),
    only the oracle-side reading of premise (c) for gates.
  - The reached run fires a plain writing leaf, not a gate call: the
    gate calls appear as oracle answers at concrete call sites
    (`fdFitO`, `fdFitR`), not as machine steps. A run stepping
    through `bindAxiom` would need the F-machine residue shape.
  - The fixture is narrower than lane 226's example 150 (review G10):
    no `opaque type Fd = u32` (the descriptor is `.int 0 7`), no
    `buf : ptr`/`len` parameters, and the witness read gate writes no
    memory. Widening it was not cheap (every environment and fit above
    names the one-parameter read) and was not done in fix lane F5.
  - Argument preconditions (section 9, fix lane F5): the split premise
    (`AxVertragOP` + the caller's `AufruferPflicht`) and the bridge
    (`hardware_aus_vertragP`) are proved; `gabbro_ziel`'s premise (c)
    is UNCHANGED (`AxVertragO` over every argument) and `Spec.lean` is
    untouched. What is NOT proved: that a run in which every gate call
    meets its precondition is the same run under the machine's oracle
    and under the re-dressed one -- only the single call is
    (`mitVorbedingung_gleich`); no Rust exporter produces `AxPre` from a
    gate's `requires`; the bridge needs a raw word outside every declared
    result type (`hraus`), which a gate without a result (`aerg = none`)
    does not have; and the fixture's preconditions (a terminator slot, the
    handed-out descriptor) are analogs of example 149's
    `path_nul_terminated` and example 150's `len <= lenof(buf)`, not
    those clauses.
  - The planted-defect check: `fremdruf_falsch_abgelehnt` proves the
    negation (an ensures demanding `6` is refused); the positive
    attempt `AxVertragO fdQfalsch fdO` fails at the `3 = 6`
    obligation (see MUSE-REPORT-233.md for the failure line).
-/

#print axioms Gabbro.Grammatik.gate_daten_gleich
#print axioms Gabbro.Grammatik.fdO_gut
#print axioms Gabbro.Grammatik.fdQ_vertrag
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt
#print axioms Gabbro.Grammatik.fremdruf_offen_lesen
#print axioms Gabbro.Grammatik.fd_opak
#print axioms Gabbro.Grammatik.fremdruf_falsch_abgelehnt
#print axioms Gabbro.Grammatik.fdPC_erreicht
#print axioms Gabbro.Grammatik.fdPC_schreibt
#print axioms Gabbro.Grammatik.fremdruf_fd_zeuge
#print axioms Gabbro.Grammatik.fremdruf_offen_lesen_zeuge
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt_zeuge
#print axioms Gabbro.Grammatik.axVertragOP_of_O
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt_pre
#print axioms Gabbro.Grammatik.mitVorbedingung_gleich
#print axioms Gabbro.Grammatik.hardware_aus_vertragP
#print axioms Gabbro.Grammatik.fdObad_vertragP
#print axioms Gabbro.Grammatik.fdObad_nicht_voll
#print axioms Gabbro.Grammatik.fremdruf_gate_gilt_pre_zeuge
#print axioms Gabbro.Grammatik.hardware_aus_vertragP_zeuge

end Gabbro.Grammatik
