module

public import Grammatik.Niedrig.Konstrukte.Kontext
public import Grammatik.Niedrig.Konstrukte.Schnitt
public import Grammatik.Niedrig.Witnesses.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

/-- A packed byte table, using the existing owner fixture's real escrow. -/
@[reducible] def D : Deklaration :=
  { OwnerWitness.D with
    count := fun _ => 8
    typ := fun _ _ => .int 0 255
    axHerkunft := fun _ => some .hardware
    axBeleg := fun _ => some () }

def names : OwnerNamespace D :=
  { key := fun mark => if mark then 0 else 1
    injective := by intro first second equal; cases first <;> cases second <;> simp_all }

def token : OwnerToken D := ⟨true, 0, ⟨0, 0, 0⟩⟩

def space : Space D :=
  { nominal := 0
    backing := 0
    width := 8
    kind := .physical
    declared := by decide
    positiveWidth := by decide }

def span : Span D :=
  { space := space
    base := 100
    length := 8
    table := ()
    number := 0
    rights := LowLevel.Witness.readWriteRights
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
    spans := [span]
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
  refine ⟨⟨(), by decide⟩, by decide, ?_, ?_⟩
  · intro candidate member
    have equal : candidate = span := by simpa only [authority, List.mem_cons, List.not_mem_nil, or_false] using member
    subst candidate
    exact ⟨by decide, rfl, by decide⟩
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
  { raum := fun _ => 0
    basis := fun _ => 100
    breite := fun _ => 1
    versatz := fun _ _ => 0
    groesse := fun _ _ => 1
    gbasis := fun global => global.elim
    ggroesse := fun global => global.elim
    graum := fun global => global.elim
    nominal := fun _ => 0 }

theorem layout_correct : LayoutOk layout :=
  { tabellenRaum := by intro table; exact ⟨by decide, rfl⟩
    offen := by intro table impossible; cases impossible
    feld := by intro table field; decide
    felder := by intro table first second different; exact False.elim (different (Subsingleton.elim _ _))
    tabellen := by intro first second byte different; exact False.elim (different (Subsingleton.elim _ _))
    tabGlob := by intro table global; exact global.elim
    globale := by intro global; exact global.elim
    globalerRaum := by intro global; exact global.elim }

theorem layout_realizes : authority.Realizes layout := by
  intro candidate member
  have equal : candidate = span := by simpa only [authority, List.mem_cons, List.not_mem_nil, or_false] using member
  subst candidate
  exact ⟨rfl, by decide, .inr (by decide)⟩

def before : World D :=
  { slots := fun _ _ _ => ⟨0, by decide, by decide⟩
    globs := fun global => global.elim
    spur := [] }

def start : Address space := (addrLitStep space 100 (by decide) before).value

def view : View D :=
  { span := span
    base := 100
    length := 4
    rights := LowLevel.Witness.readWriteRights
    lender := OwnerWitness.root
    borrower := OwnerWitness.child
    epoch := 2 }

def receipt : ViewResult authority initial :=
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

def written : World D := viewPutStep view layout () 0 ⟨42, by decide, by decide⟩
  resources (fun _ => true) putChecked before

def ghost : OwnerBindings D.Marke := [⟨10, true, 0⟩]

def renamedGhost : OwnerBindings D.Marke := [⟨11, true, 0⟩]

def oracle : Orakel D :=
  { wirkt := fun _ world _ => (world, 0)
    regLies := fun register => register.elim
    regSchreib := fun register => register.elim
    sichtbar := fun global => global.elim }

end Gabbro.Grammatik.LowLevel.Construct.Witness
