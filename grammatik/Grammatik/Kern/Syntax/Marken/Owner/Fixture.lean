module

public import Grammatik.Kern.Syntax.Marken.Owner.Source
public import Grammatik.Kern.Syntax.Marken.Owner.Conservation
public import Grammatik.Kern.Syntax.Syntax.Teil2

@[expose] public section

namespace Gabbro.Grammatik.OwnerWitness

/-- Two nominal marks, one guarded table, three call-frame depths and one
    resolved software minter. No ordinary signature produces an owner. -/
@[reducible] def D : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => some ()
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
    { params := [], erg := none, gruende := 0, haelt := [], schreibt := fun _ => true, gschreibt := (fun e => (nomatch e)), konsumiert := [], produziert := [] }
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

def names : OwnerNamespace D where
  key := fun m => if m then 0 else 1
  injective := by intro a b h; cases a <;> cases b <;> simp_all

def mint : OwnerMintDecl D where
  mark := true
  minter := ()
  root := 0
  site := 7
  stage := 0
  owner := ⟨(), by decide⟩
  bounded := by decide

def root : ArenaOwnership.Frame := ⟨0, 0⟩
def child : ArenaOwnership.Frame := ⟨0, 1⟩
def grandchild : ArenaOwnership.Frame := ⟨0, 2⟩
def foreignThread : ArenaOwnership.Frame := ⟨1, 1⟩

def token : OwnerToken D := ⟨true, 0, ⟨0, 0, 0⟩⟩

def mintedLedger : ArenaOwnership.State :=
  { (ArenaOwnership.State.empty.put 0 (some ⟨0, 0, root, []⟩)) with next := 1 }

def minted : OwnerState D :=
  { OwnerState.empty with ledger := mintedLedger, spent := fun m => if m = true then true else false, stage := fun m => if m = true then 0 else 0 }

def loaned : OwnerState D := minted.withLedger
  (mintedLedger.put 0 (some ⟨0, 0, root, [child]⟩))

def nested : OwnerState D := minted.withLedger
  (mintedLedger.put 0 (some ⟨0, 0, root, [grandchild, child]⟩))

def movedLedger : ArenaOwnership.State :=
  { (mintedLedger.put 0 (some ⟨0, 1, child, []⟩)) with next := 2 }

def moved : OwnerState D := minted.withLedger movedLedger

def movedToken : OwnerToken D := { token with handle := ⟨0, 0, 1⟩ }

def movedTwiceLedger : ArenaOwnership.State :=
  { (movedLedger.put 0 (some ⟨0, 2, grandchild, []⟩)) with next := 3 }

def movedTwice : OwnerState D := minted.withLedger movedTwiceLedger

def movedTwiceToken : OwnerToken D := { token with handle := ⟨0, 0, 2⟩ }

def retired : OwnerState D := minted.withLedger (mintedLedger.put 0 none)

def stageOne : OwnerState D :=
  { minted with stage := fun m => if m = true then 1 else minted.stage m }

def stageOneToken : OwnerToken D := { token with stage := 1 }

def ghost : OwnerBindings D.Marke := [⟨10, true, 0⟩]
def renamedGhost : OwnerBindings D.Marke := [⟨11, true, 0⟩]

def handoff : OwnerFlow D.Marke := { moves := [⟨true, 0, some 1⟩] }
def scoped : OwnerFlow D.Marke := { loans := [(true, 0)] }

/-- A guard witness is not a mint/source simulation: it only instantiates the
    existing canonical read and write constructors under the interpreted mark. -/
theorem guard : darf D () (OwnerBindings.resources ghost) := by
  intro w hw
  have he : w = Sum.inr (true, 0) := by simpa using hw
  subst w
  decide

def guardedRead : Expr D [] (OwnerBindings.resources ghost) (.int 0 1) :=
  .slot () () (.lit 0) guard

def contract : Vertrag D := Vertrag.vonSig D (D.signatur 0)

def guardedWrite : Stmt D contract false []
    (OwnerBindings.resources ghost) (OwnerBindings.resources ghost) :=
  .assignSlot () () (.lit 0) (.widen (by decide) (by decide) (.lit 1)) rfl guard

end Gabbro.Grammatik.OwnerWitness
