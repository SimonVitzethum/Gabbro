module

public import Grammatik.Niedrig.Konstrukte.Kontext
public import Grammatik.Niedrig.Konstrukte.Schnitt
public import Grammatik.Niedrig.Witnesses.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

/-- Two byte tables in distinct nominal spaces and distinct backings. The
    second carrier is OPEN; both use the existing real owner escrow. -/
@[reducible] def D : Deklaration :=
  {
    Tab := Bool
    decTab := inferInstance
    count := fun _ => 8
    Feld := fun _ => Unit
    decFeld := fun _ => inferInstance
    typ := fun _ _ => .int 0 255
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
    Ax := Fin 3
    aparams := fun _ => []
    aerg := fun _ => none
    aschreibt := fun _ _ => false
    agschreibt := fun _ e => nomatch e
    Reg := Unit
    rtyp := fun _ => .int 0 255
    rklasse := fun _ => .rw
    spiegel := fun _ => none
    rzusage := fun _ value => decide (value.n ≠ 13)
    rtraeger := fun _ => [.inl true]
    Annahme := Fin 3
    a10 := 0
    geteilt_bewacht := fun _ h => by cases h
    invarianten_gehalten := fun _ i => nomatch i
    ggeteilt_bewacht := fun e => nomatch e
    offen := fun table => table
    dataSpaces := ["ram", "other"]
    tableSpace := fun table => if table then 1 else 0
    axHerkunft := fun _ => some .hardware
    axBeleg := fun item => some item }

def names : OwnerNamespace D :=
  { key := fun mark => if mark then 0 else 1
    injective := by intro first second equal; cases first <;> cases second <;> simp_all }

def token : OwnerToken D := ⟨true, 0, ⟨0, 0, 0⟩⟩

def space : Space D :=
  { nominal := 0
    backing := 4
    width := 8
    kind := .physical
    declared := by decide
    positiveWidth := by decide }

noncomputable def span : Span D :=
  { space := space
    base := 100
    length := 8
    table := false
    number := 0
    rights := LowLevel.Witness.readWriteRights
    execute := false
    memoryClass := .ordinaryRam
    owner := true
    epoch := 2
    alignment := 1
    mapped := true
    initialized := true }

def secondSpace : Space D :=
  { space with nominal := 1, backing := 9, declared := by decide }

noncomputable def secondSpan : Span D :=
  { span with space := secondSpace, table := true, number := 1 }

noncomputable def authority : Authority D :=
  { names := names
    token := token
    spans := [span, secondSpan]
    epoch := 2 }

def owners : OwnerState D :=
  { ledger := OwnerWitness.mintedLedger
    initial := fun mark => mark
    spent := fun _ => false
    stage := fun _ => 0 }

def initial : Context D Unit Bool :=
  { owners := owners
    frame := OwnerWitness.root
    views := []
    privilege := ()
    interrupt := false }

theorem authority_valid : authority.Valid := by
  refine ⟨⟨false, by decide⟩, by decide, ?_, ?_⟩
  · intro candidate member
    change candidate ∈ [span, secondSpan] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨by decide, rfl, by decide⟩
  · apply List.Pairwise.cons
    · intro other member
      have same : other = secondSpan := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
      subst other
      exact .inl (by decide)
    · exact List.Pairwise.cons (fun _ member => absurd member List.not_mem_nil) .nil

theorem owners_valid : owners.ledger.valid := LowLevel.Witness.initial_ledger_valid

theorem initial_owned : owners.owns names initial.frame token :=
  ⟨rfl, rfl, ⟨⟨rfl, rfl⟩, rfl, rfl⟩⟩

theorem initial_valid : initial.Valid authority := by
  refine ⟨authority_valid, owners_valid, ?_, ?_, ?_⟩
  · exact ⟨initial_owned.1, initial_owned.2.1,
      ArenaOwnership.State.owner_access (s := owners.ledger) (f := initial.frame)
        (h := token.handle) initial_owned.2.2⟩
  · intro view member
    cases member
  · intro view member
    cases member

def layout : AdressLayout D :=
  { raum := fun table => if table then 9 else 4
    basis := fun _ => 100
    breite := fun _ => 1
    versatz := fun _ _ => 0
    groesse := fun _ _ => 1
    gbasis := fun global => global.elim
    ggroesse := fun global => global.elim
    graum := fun global => global.elim
    nominal := fun backing => if backing = 9 then 1 else 0 }

theorem layout_correct : LayoutOk layout :=
  { tabellenRaum := by intro table; cases table <;> exact ⟨by decide, rfl⟩
    offen := by
      intro table opened
      cases table with
      | false => cases opened
      | true =>
        exact ⟨by intro other different; cases other <;> simp_all [layout], fun global => global.elim⟩
    feld := by intro table field; cases table <;> cases field <;> decide
    felder := by intro table first second different; exact False.elim (different (Subsingleton.elim _ _))
    tabellen := by
      intro first second byte different inside other
      have a := inside.1
      have b := other.1
      cases first <;> cases second <;> simp_all [layout]
    tabGlob := by intro table global; exact global.elim
    globale := by intro global; exact global.elim
    globalerRaum := by intro global; exact global.elim }

theorem layout_realizes : authority.Realizes layout := by
  intro candidate member
  change candidate ∈ [span, secondSpan] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, by decide, .inr (by decide)⟩
  · exact ⟨rfl, by decide, .inl rfl⟩

def before : World D :=
  { slots := fun _ _ _ => ⟨0, by decide, by decide⟩
    globs := fun global => global.elim
    spur := [] }

def start : Address space := (addrLitStep space 100 (by decide) before).value

noncomputable def view : View D :=
  { span := span
    base := 100
    length := 4
    rights := LowLevel.Witness.readWriteRights
    lender := OwnerWitness.root
    borrower := OwnerWitness.child
    epoch := 2 }

noncomputable def receipt : ViewResult authority initial :=
  { view := view
    admission :=
      { span := List.mem_cons_self ..
        owner := rfl
        epoch := ⟨rfl, rfl⟩
        lender := rfl
        bounds := by decide
        memoryClass := rfl
        permissions := ⟨.inl rfl, fun _ => rfl, fun _ => rfl, rfl⟩
        alignment := by decide
        mapping := rfl
        initialization := rfl
        compatible := by intro other member; cases member }
    owners := owners.withLedger
      (OwnerWitness.mintedLedger.put 0 (some ⟨0, 0, OwnerWitness.root, [OwnerWitness.child]⟩))
    borrowed := rfl }

def resources : List (Res D) := [.marke true 0]

def putChecked : ViewPutOk view layout () 0 resources (fun _ => true) := by decide

def getChecked : ViewGetOk view layout () 0 1 resources := by decide

noncomputable def written : World D := viewPutStep view layout () 0 ⟨42, by decide, by decide⟩
  resources (fun _ => true) putChecked before

def ghost : OwnerBindings D.Marke := [⟨10, true, 0⟩]

def renamedGhost : OwnerBindings D.Marke := [⟨11, true, 0⟩]

def oracle : Orakel D :=
  { wirktL := fun _ world _ => ({ world with spur := [] }, 0)
    regLiesL := fun _ _ => 42
    regSchreib := fun _ _ => ()
    sichtbarL := fun global => global.elim }

end Gabbro.Grammatik.LowLevel.Construct.Witness
