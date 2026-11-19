module

public import Grammatik.Logik.Invarianten.Frag.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Witness

abbrev declaration : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 3
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => none
  Glob := Bool
  decGlob := inferInstance
  gtyp := fun _ => .int 0 10
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun value => nomatch value
  maskiert := fun value => nomatch value
  Marke := Empty
  decMarke := inferInstance
  stufen := fun value => nomatch value
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Empty
  sig := fun value => nomatch value
  sigNr := fun _ => ⟨[], none, 0, [], fun _ => false, fun _ => false, [], [], none, {}⟩
  eigner_nie_erzeugt := fun _ _ _ _ h => nomatch h
  Inv := Unit
  traeger := fun _ => [.inr false, .inr true, .inl ()]
  invs := [()]
  Ax := Empty
  aparams := fun value => nomatch value
  aerg := fun value => nomatch value
  aschreibt := fun value => nomatch value
  agschreibt := fun value => nomatch value
  Reg := Empty
  rtyp := fun value => nomatch value
  rklasse := fun value => nomatch value
  spiegel := fun value => nomatch value
  rzusage := fun value => nomatch value
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => nomatch h
  invarianten_gehalten := fun _ _ h => nomatch h
  ggeteilt_bewacht := fun _ h => nomatch h

theorem globalAccess (name : declaration.Glob) : gdarf declaration name [] :=
  fun _ h => nomatch h

theorem slotAccess : darf declaration () [] := fun _ h => nomatch h

/-- `len <= cap && 0 <= len`, over the two declared scalar globals. -/
def boundedLength : Expr declaration [] [] .bool :=
  .and (.le (.glob false (globalAccess false)) (.glob true (globalAccess true)))
    (.le (.lit 0) (.glob false (globalAccess false)))

def boundedFormula : LProp (Observation declaration) :=
  .and (.le (.var (.glob false)) (.var (.glob true)))
    (.le (.konst 0) (.var (.glob false)))

def program : Programm declaration where
  invariante := fun _ => boundedLength
  requires := fun value => nomatch value
  ensures := fun value => nomatch value
  rumpf := fun value => nomatch value

def initial : World declaration where
  slots := fun _ _ _ => ⟨4, by decide, by decide⟩
  globs := fun (name : Bool) =>
    match name with
    | true => ⟨8, by decide, by decide⟩
    | false => ⟨3, by decide, by decide⟩
  spur := []

def invalidLengthWorld : World declaration :=
  { initial with
    globs := fun (name : Bool) =>
      match name with
      | true => ⟨8, by decide, by decide⟩
      | false => ⟨9, by decide, by decide⟩ }

def product : Expr declaration [] [] .bool :=
  .le (.mul (.glob false (globalAccess false)) (.glob true (globalAccess true))) (.lit 3)

/-- A genuine two-index sortedness condition on a three-entry table. -/
def sorted : Expr declaration [] [] .bool :=
  .forallSlots ()
    (.forallSlots ()
      (.or (.not (.lt (.var (.there .here)) (.var .here)))
        (.le (.slot () () (.var (.there .here)) slotAccess)
          (.slot () () (.var .here) slotAccess))) slotAccess) slotAccess

/-- A nonempty, one-index local invariant is admitted. -/
def localBound : Expr declaration [] [] .bool :=
  .forallSlots () (.le (.slot () () (.var .here) slotAccess) (.lit 10)) slotAccess

def localFormula : LProp (Observation declaration) :=
  .and (.le (.var (.slot () () 0)) (.konst 10))
    (.and (.le (.var (.slot () () 1)) (.konst 10))
      (.and (.le (.var (.slot () () 2)) (.konst 10)) .tru))

/-- String contents never enter the arithmetic problem; their length does. -/
def stringDeclaration : Deklaration :=
  { declaration with
    gtyp := fun (name : Bool) => match name with | true => .int 0 10 | false => .str 10 }

def stringBound : Expr stringDeclaration [] [] .bool :=
  .le (.strLen (Expr.glob (D := stringDeclaration) false (fun _ h => nomatch h)))
    (Expr.glob (D := stringDeclaration) true (fun _ h => nomatch h))

def scaled : Expr declaration [] [] .bool :=
  .le (.mul (.lit 2) (.glob false (globalAccess false))) (.lit 20)

def emptyDeclaration : Deklaration :=
  { declaration with count := fun _ => 0 }

def emptyNonlinear : Expr emptyDeclaration [] [] .bool :=
  .forallSlots ()
    (.le (.mul (Expr.glob (D := emptyDeclaration) false (fun _ h => nomatch h))
      (Expr.glob (D := emptyDeclaration) true (fun _ h => nomatch h))) (.lit 3))
    (fun _ h => nomatch h)

def atomicDeclaration : Deklaration :=
  { declaration with
    atomar := fun _ => true
    ggeteilt_bewacht := fun _ h => nomatch h }

def atomicBound : Expr atomicDeclaration [] [] .bool :=
  .le (Expr.glob (D := atomicDeclaration) false (fun _ h => nomatch h)) (.lit 3)

/-- Boolean memory keeps its value rather than becoming a constant predicate. -/
def booleanDeclaration : Deklaration := { declaration with gtyp := fun _ => .bool }

def booleanMemory : Expr booleanDeclaration [] [] .bool :=
  .glob false (fun _ member => nomatch member)

/-- The standalone QE syntax also has actual integer quantifiers. -/
def quantified : LProp Nat :=
  .all 0 (.ex 1 (.eq (.var 1) (.add (.var 0) (.konst 1))))

end Gabbro.Grammatik.Invarianten.Frag.Witness
