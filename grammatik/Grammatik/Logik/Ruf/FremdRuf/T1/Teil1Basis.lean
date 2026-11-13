module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.AxiomVertrag
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Zielsatz.Kern.Spec

@[expose] public section



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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- The gate handing out descriptors. -/
def fdOpen : fdD.Ax := true

/-- The gate taking a descriptor and answering a count. -/
def fdRead : fdD.Ax := false

/-- The single function writes the table. -/
def fdArbeit : fdD.Fn := ()

/-- The handing-out gate takes no parameters. -/
theorem fdOpen_params : fdD.aparams fdOpen = [] := by rfl

/-- The handing-out gate answers a descriptor in `0 .. 7`. -/
theorem fdOpen_erg : fdD.aerg fdOpen = some (.int 0 7) := by rfl

/-- The reading gate takes a descriptor in `0 .. 7`. -/
theorem fdRead_params : fdD.aparams fdRead = [.int 0 7] := by rfl

/-- The reading gate answers a count in `0 .. 100`. -/
theorem fdRead_erg : fdD.aerg fdRead = some (.int 0 100) := by rfl

/-- Descriptor type flows from answer to parameter: what the first
    gate hands out is what the second gate takes. -/
theorem fd_fluss_typ : fdD.aparams fdRead = [.int 0 7] ∧
    fdD.aerg fdOpen = some (.int 0 7) :=
  ⟨rfl, rfl⟩

/-- The function writes the table (non-degeneracy, first half). -/
theorem fdArbeit_schreibt : fdD.schreibt fdArbeit () = true := by rfl

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
  wirktL
    | true, σ, _ => ({ σ.storeSlot () 1 () ⟨5, by decide, by decide⟩ with
        spur := axiomSpur [()] [] true [] σ.haelt }, 3)
    | false, σ, _ => ({ σ with spur := axiomSpur [()] [] false [] σ.haelt },
        (σ.slots () 0 ()).n)
  regLiesL := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g _ => nomatch g

/-! ## 4. The oracle meets frame and ensures -/

/-- The fixture guards nothing, so every access is allowed with no holdings. -/
theorem fdD_darf (t : fdD.Tab) : darf fdD t [] := by
  intro w hw
  have hb : fdD.braucht t = [] := rfl
  rw [hb] at hw
  simp only [List.not_mem_nil] at hw

/-- No holdings are held anywhere: `HeldIn` of the empty list. -/
theorem fdHeldIn_nil (h : List fdD.Lock) : HeldIn ([] : List (Res fdD)) h := by
  intro L hL
  simp only [List.not_mem_nil] at hL

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
  show offen (axiomSpur [()] [] true [] σ.ohneLese.haelt ++ σ.spur) = offen σ.spur
  exact offen_append_zugriffe _ _ _ (axiomSpur_zugriffMit _ _ _ _ _)

/-- The reading call keeps the held locks: recording only. -/
theorem fdO_haelt_read (σ : World fdD) (ρ : Env fdD (fdD.aparams false)) :
    (fdO.wirkt false σ ρ).1.haelt = σ.haelt := by
  show offen (axiomSpur [()] [] false [] σ.ohneLese.haelt ++ σ.spur) = offen σ.spur
  exact offen_append_zugriffe _ _ _ (axiomSpur_zugriffMit _ _ _ _ _)

/-- The single table is the complete domain. -/
theorem fdTab_mem (t : fdD.Tab) : t ∈ [()] :=
  List.Mem.head _

end Gabbro.Grammatik
