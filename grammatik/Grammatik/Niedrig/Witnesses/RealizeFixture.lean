module

public import Grammatik.Niedrig.Authority.RealizeSaetze
public import Grammatik.Niedrig.Witnesses.Joint

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.RealizeWitness

/-- A closed carrier and an OPEN carrier, with distinct nominal spaces.
    The owner ledger is the same small fixture used by Joint. -/
@[reducible] def D : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun t => if t then 0 else 8
  offen := fun t => t
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
  erlaubt := fun _ _ _ _ => false
  tabNr := fun n => if n = 0 then some false else if n = 1 then some true else none
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
  Marke := Bool
  decMarke := inferInstance
  stufen := fun _ => 3
  braucht := fun _ => [.inr (true, 0)]
  gbraucht := fun e => nomatch e
  eigner := fun _ => [true]
  Fn := Fin 3
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := by intros; simp
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => false
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by cases h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e
  dataSpaces := ["normal", "firmware"]
  tableSpace := fun t => if t then 1 else 0

def names : OwnerNamespace D :=
  { key := fun m => if m then 0 else 1
    injective := by intro a b h; cases a <;> cases b <;> simp_all }

def token : OwnerToken D := ⟨true, 0, ⟨0, 0, 0⟩⟩

def owners : OwnerState D :=
  { ledger := OwnerWitness.mintedLedger
    initial := fun m => m
    spent := fun _ => false
    stage := fun _ => 0 }

def space (table : Bool) : Space D :=
  { nominal := if table then 1 else 0
    backing := if table then 9 else 7
    width := 8
    kind := .physical
    declared := by cases table <;> decide
    positiveWidth := by decide }

def span (table : Bool) : Span D :=
  { space := space table
    base := if table then 164 else 66
    length := if table then 20 else 10
    table := table
    number := if table then 1 else 0
    rights := Witness.readWriteRights
    execute := false
    memoryClass := .ordinaryRam
    owner := true
    epoch := 2
    alignment := 1
    mapped := true
    initialized := true }

def authority : Authority D :=
  { names := names
    token := token
    spans := [span false, span true]
    epoch := 2 }

theorem authority_valid : authority.Valid := by
  refine ⟨⟨false, by decide⟩, by decide, ?_, ?_⟩
  · intro s member
    change s ∈ [span false, span true] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · apply List.Pairwise.cons
    · intro s member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst s
      exact .inl (by decide)
    · exact List.Pairwise.cons (fun _ h => absurd h List.not_mem_nil) .nil

def initial : Context D Witness.Privilege Bool :=
  { owners := owners
    frame := OwnerWitness.root
    views := []
    privilege := .firmware
    interrupt := true }

theorem initial_owned : owners.owns names initial.frame token :=
  ⟨rfl, rfl, ⟨⟨rfl, rfl⟩, rfl, rfl⟩⟩

theorem initial_valid : initial.Valid authority := by
  refine ⟨authority_valid, Witness.initial_ledger_valid, ?_, ?_, ?_⟩
  · exact ⟨initial_owned.1, initial_owned.2.1,
      ArenaOwnership.State.owner_access (s := owners.ledger)
        (f := initial.frame) (h := token.handle) initial_owned.2.2⟩
  · intro v member; cases member
  · intro v member; cases member

/-- The entry contract asserts privilege only, never Realizes. -/
def contract : BootContract D Witness.Privilege Bool :=
  { «entry» := fun _ c => c.privilege = .firmware ∧ c.interrupt = true
    transition := fun _ _ _ c => c.privilege = .user
    root := fun _ c => c.privilege = .user }

theorem firmware_entry : FirmwareEntry contract authority initial :=
  { contract := ⟨rfl, rfl⟩
    valid := initial_valid
    initial := rfl
    unspent := rfl
    owned := initial_owned
    noViews := rfl }

def handoff : HandoffResult authority initial :=
  { into := OwnerWitness.child
    privilege := .user
    interrupt := false
    owners := owners.withLedger OwnerWitness.movedLedger
    token := ⟨true, 0, ⟨0, 0, 1⟩⟩
    quiescent := rfl
    moved := rfl }

def layout : AdressLayout D :=
  { raum := fun t => if t then 9 else 7
    basis := fun t => if t then 128 else 64
    breite := fun t => if t then 16 else 8
    versatz := fun _ _ => 0
    groesse := fun _ _ => 1
    gbasis := fun g => g.elim
    ggroesse := fun g => g.elim
    graum := fun g => g.elim
    nominal := fun r => if r = 9 then 1 else 0 }

theorem layout_correct : LayoutOk layout :=
  { tabellenRaum := by intro t; cases t <;> exact ⟨by decide, rfl⟩
    offen := by
      intro t hopen
      cases t with
      | false => cases hopen
      | true =>
          refine ⟨?_, ?_⟩
          · intro t' different
            cases t' with
            | false => decide
            | true => exact False.elim (different rfl)
          · intro g; exact g.elim
    feld := by intro t f; cases t <;> cases f <;> decide
    felder := by intro t f f' different; exact False.elim (different (Subsingleton.elim _ _))
    tabellen := by
      intro t t' byte different inside other
      have same := inside.1.symm.trans other.1
      cases t <;> cases t' <;> simp_all [layout]
    tabGlob := by intro t g; exact g.elim
    globale := by intro g; exact g.elim
    globalerRaum := by intro g; exact g.elim }

end Gabbro.Grammatik.LowLevel.RealizeWitness
