/-
  File:      Grammatik/FremdRuf.lean
  Subject:   FOREIGN CALLS WITH DESCRIPTOR CARRIERS (lane 233) -- the
             user-declared gate shape: a descriptor as an opaque carrier
             value plus gates as oracle calls whose dispatch labels,
             register bindings, costs and effects are program DATA, with
             answers constrained only by the declared ensures.

  Modelled shape: one gate hands out a descriptor value in a narrow
  carrier range, a second gate takes such a value and answers a count.
  The descriptor is never computed on: the second gate's oracle answer
  is independent of the passed value (`fd_opak`). The goal theorem's
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
    promises a nonzero descriptor; the reading gate promises the
    count it answers is the current slot value. Both read only the
    answer and (for the second) the gate's own write carrier. -/
def fdQ : AxEns fdD
  | true, _, v => decide ((v : Zahl 0 7).n ≠ 0)
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

/-- The oracle meets the declared ensures of both gates. -/
theorem fdQ_vertrag : AxVertragO fdQ fdO := by
  intro a σ ρ v h
  cases a with
  | true =>
    have hred : einpassenErg fdO.zeiger (fdD.aerg true) (fdO.wirkt true σ ρ).2
        = einpassen (D := fdD) fdO.zeiger (.int 0 7) 3 := rfl
    rw [hred] at h
    simp only [einpassen] at h
    split at h
    next hcond =>
      have e : (⟨3, hcond.1, hcond.2⟩ : Wert fdD (.int 0 7)) = v :=
        Option.some_inj.mp h
      subst e
      show decide (((⟨3, hcond.1, hcond.2⟩ : Wert fdD (.int 0 7)) : Zahl 0 7).n ≠ 0) = true
      exact decide_eq_true (by decide : (3 : Int) ≠ 0)
    next hcond =>
      have hpos : (0 : Int) ≤ (3 : Int) ∧ (3 : Int) ≤ (7 : Int) := by decide
      exact absurd hpos hcond
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

/-- The descriptor is opaque: the reading gate answers the current
    slot value no matter which descriptor value it is passed. -/
theorem fd_opak (σ : World fdD) (ρ1 ρ2 : Env fdD (fdD.aparams fdRead)) :
    (fdO.wirkt fdRead σ ρ1).2 = (fdO.wirkt fdRead σ ρ2).2 := rfl

end Gabbro.Grammatik
