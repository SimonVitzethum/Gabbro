/- C16: declared checks beyond a linear Duty -- descriptor, report and evidence types.

   A `check` declaration (SYNTAX.md section 13, `SCheck`) is not itself an execution step.
   Its kernel descriptor is `CheckDecl`: the resolved declaration with its measured places,
   its generated Boolean probe, the typed floors, the unique optional external counterprobe
   and the build mode. The descriptor is stored with the program; the source certificate
   stays with the elaborator (`Parser/Elab/Uebersetze/Pruefung`).

   Duty is evidence, never truth: `CheckExpansion` ties the generated probe to the written
   `can_fail` -- every normal return yields `Bool` and carries the one linear Duty, on
   `false` returns too. The probe threads the Duty (it consumes and produces the same
   mark): a body that forged a Duty from nothing could not be typed, and no `ensures`
   is ever derived from the claim text. The consuming gates discharge that same Duty
   once. What a sample measured is `CheckReport`; the ghost history entry is
   `CheckEvidenz`; the external counterprobe status is `ProbenStand`.

   The admission Bool and the goal leg live on the Zielsatz side
   (`Zielsatz/Kern/Akzeptiert/Teil3`, `Zielsatz/Kern/Spec/Teil4`), where the call-graph
   closure (`reachB`) and the machine are in scope. -/
module

public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm

@[expose] public section

namespace Gabbro.Grammatik

/-- A declared check (`check c claims "..." measures [...] gates [...] can_fail ...
    floors [...] [counterprobe ... expects ...]`): the kernel descriptor. `probe` is
    the generated Boolean producer, `duty` the one linear mark it threads through every
    normal return (A24 `Res.marke`), `gates` the declared consuming gates, `boden` the
    typed floors (gate name with its expected verdict), `sonde` the unique optional
    external counterprobe (name with its exact text), `testbau` the build mode
    (`false` = shipping, `true` = test). -/
structure CheckDecl (D : Deklaration) where
  name : String
  claim : String
  misst : List String
  gates : List D.Fn
  probe : D.Fn
  duty : D.Marke × Nat
  boden : List (String × Bool)
  sonde : Option (String × String)
  testbau : Bool := false

/-- The verdict of one completed probe run: what the generated producer returned.
    `false` is a completed measurement with a negative verdict, never a missing one. -/
abbrev CheckUrteil := Bool

/-- One measured sample: the source place, the observation point, the sampled value
    and whether it was actually observed. A missing value on an early returning path
    is an explicit absent sample (`gelesen = false`), never zero. -/
structure CheckProbe where
  ort : String
  punkt : Nat
  wert : Int
  gelesen : Bool
  deriving DecidableEq, Repr

/-- The report of one completed probe: the samples, the floor outcomes evaluated over
    them, and the verdict. -/
structure CheckReport where
  proben : List CheckProbe
  boeden : List Bool
  urteil : Bool
  deriving DecidableEq, Repr

/-- A report is complete: every sample was actually observed. -/
def CheckReport.vollstaendig (r : CheckReport) : Prop :=
  ∀ p ∈ r.proben, p.gelesen = true

/-- The status of the external counterprobe bound to a check: not run, passed or
    failed, each with its execution provenance. Only a `failed` run on the matching
    artifact is measured acceptance evidence; absence stays unmeasured. -/
inductive ProbenStand where
  | nichtGelaufen
  | bestanden
  | durchgefallen
  deriving DecidableEq, Repr

/-- Ghost evidence of one completed probe in the shared history: the producer
    activation, its actual report, the current token location (`lebt`: the Duty is
    live and owed to a gate; otherwise it was consumed) and the consuming gate. -/
structure CheckEvidenz (D : Deklaration) where
  erzeuger : D.Fn
  bericht : CheckReport
  lebt : Bool
  tor : Option D.Fn

/-- The exact expansion: the generated probe is the written `can_fail`. It returns
    `Bool` on a reason-free channel, threads exactly the Duty (consumed and produced,
    so every normal return -- including `false` -- carries it and no halted path
    synthesizes one), reads but never writes, and every declared gate consumes that
    Duty. The probe is none of its gates, and the gates are pairwise distinct.
    Claim text stays a label: nothing here derives an `ensures` from it. -/
def CheckExpansion (P : Programm D) (c : CheckDecl D) : Prop :=
  D.erg c.probe = some .bool ∧
  (D.signatur c.probe).gruende = 0 ∧
  (D.signatur c.probe).konsumiert = [c.duty] ∧
  (D.signatur c.probe).produziert = [c.duty] ∧
  (∀ t, (D.signatur c.probe).schreibt t = false) ∧
  (∀ g, (D.signatur c.probe).gschreibt g = false) ∧
  (∀ g ∈ c.gates, c.duty ∈ (D.signatur g).konsumiert) ∧
  c.probe ∉ c.gates ∧
  c.gates.Nodup

/-- The probe answers `Bool`. -/
theorem CheckExpansion.erg {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : D.erg c.probe = some .bool :=
  h.1

/-- The probe has no reason channel of its own. -/
theorem CheckExpansion.gruende {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : (D.signatur c.probe).gruende = 0 :=
  h.2.1

/-- The probe consumes exactly the Duty. -/
theorem CheckExpansion.konsumiert {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : (D.signatur c.probe).konsumiert = [c.duty] :=
  h.2.2.1

/-- The probe produces exactly the Duty, on every normal return. -/
theorem CheckExpansion.produziert {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : (D.signatur c.probe).produziert = [c.duty] :=
  h.2.2.2.1

/-- The probe writes no table: the check is read-only on program payload. -/
theorem CheckExpansion.schreibt {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) (t : D.Tab) : (D.signatur c.probe).schreibt t = false :=
  h.2.2.2.2.1 t

/-- The probe writes no static. -/
theorem CheckExpansion.gschreibt {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) (g : D.Glob) : (D.signatur c.probe).gschreibt g = false :=
  h.2.2.2.2.2.1 g

/-- Every declared gate consumes the Duty: a gate called without the producer report
    is refused by ordinary resource admission. -/
theorem CheckExpansion.gate_konsumiert {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) {g : D.Fn} (hg : g ∈ c.gates) :
    c.duty ∈ (D.signatur g).konsumiert :=
  h.2.2.2.2.2.2.1 g hg

/-- The probe is none of its gates: invoking another consumer needs another
    completed producer run. -/
theorem CheckExpansion.probe_frisch {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : c.probe ∉ c.gates :=
  h.2.2.2.2.2.2.2.1

/-- The declared consumers are pairwise distinct: one Duty is never duplicated
    across their list. -/
theorem CheckExpansion.tore_nodup {P : Programm D} {c : CheckDecl D}
    (h : CheckExpansion P c) : c.gates.Nodup :=
  h.2.2.2.2.2.2.2.2

/-! ## The fixture: one Boolean probe, one consuming gate, one threaded Duty -/

/-- The probe signature of the fixture: reason-free, `Bool`, threading the Duty. -/
def pruefProbeSig : Signatur Empty Empty Empty Unit where
  params := []
  erg := some .bool
  gruende := 0
  haelt := []
  schreibt := fun t => t.elim
  gschreibt := fun g => g.elim
  konsumiert := [((), 0)]
  produziert := [((), 0)]

/-- The gate signature of the fixture: it discharges the Duty. -/
def pruefGateSig : Signatur Empty Empty Empty Unit where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => t.elim
  gschreibt := fun g => g.elim
  konsumiert := [((), 0)]
  produziert := []

/-- The signature table of the fixture: `true` is the probe, `false` the gate. -/
def pruefSig : Nat → Signatur Empty Empty Empty Unit
  | 0 => pruefProbeSig
  | _ + 1 => pruefGateSig

/-- The smallest declaration with one Boolean probe and one gate. -/
def pruefD : Deklaration where
  Tab := Empty
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun t => t.elim
  ggeteilt := fun g => g.elim
  Lock := Empty
  rang := fun l => l.elim
  maskiert := fun l => l.elim
  Marke := Unit
  stufen := fun _ => 1
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Bool
  sig := fun
    | true => 0
    | false => 1
  sigNr := pruefSig
  eigner_nie_erzeugt := fun n t m s _ => t.elim
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => t.elim
  invarianten_gehalten := fun n i _ => i.elim
  ggeteilt_bewacht := fun g _ => g.elim

/-- The fixture check: the probe `true` with its gate `false`. -/
def pruefC : CheckDecl pruefD where
  name := "p"
  claim := "c"
  misst := []
  gates := [false]
  probe := true
  duty := ((), 0)
  boden := []
  sonde := none
  testbau := false

/-- The fixture program: the probe returns `true` with the Duty in hand, the gate
    retires the Duty and returns. -/
def pruefP : Programm pruefD where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun
    | true => .var .here
    | false => .tru
  rumpf := fun
    | true => .ret (.val .tru) (List.Perm.refl _)
    | false =>
      .cons (.retires () 0 (List.Mem.head _) ())
        (.ret .empty (List.Perm.refl _))
  unterbricht := fun _ => false

/-- The fixture is a non-degenerate expansion: probe and gate satisfy every premise
    jointly -- `Bool` answer, no reason channel, the threaded Duty, a read-only
    frame, gate consumption, freshness and distinctness. -/
theorem pruef_expansion : CheckExpansion pruefP pruefC := by
  refine ⟨rfl, rfl, rfl, rfl, fun t => t.elim, fun g => g.elim, ?_, ?_, ?_⟩
  · intro g hg
    change Bool at g
    have hf : g = false := List.mem_singleton.mp hg
    subst hf
    exact by decide
  · change ¬ (true : Bool) ∈ ([false] : List Bool)
    decide
  · change ([false] : List Bool).Nodup
    decide

end Gabbro.Grammatik
