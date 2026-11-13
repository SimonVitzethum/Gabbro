module

public import Grammatik.Logik.Invarianten.Frag.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Witness

def declaration : Deklaration where
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

theorem boundedLength_translated_zeuge :
    translateDeclared program () = .ok boundedFormula := by rfl

theorem boundedLength_admitted_zeuge :
    imFragmentB (declaration.traeger ()) boundedLength = true := by
  have translated : uebersetzeB (declaration.traeger ()) boundedLength = .ok boundedFormula :=
    boundedLength_translated_zeuge
  simp only [imFragmentB, translated]

theorem boundedLength_sound_zeuge (world : World declaration) :
    eval world boundedLength world .nil = true ↔
      boundedFormula.denote (assignment world) :=
  uebersetzeB_sound (declaration.traeger ()) boundedLength boundedFormula
    boundedLength_translated_zeuge world

theorem declared_sound_zeuge (world : World declaration) :
    eval world (program.invariante ()) world .nil = true ↔
      boundedFormula.denote (assignment world) :=
  translateDeclared_sound program () boundedFormula boundedLength_translated_zeuge world

theorem carriers_sound_zeuge :
    ∀ carrier ∈ boundedLength.orte, carrier ∈ declaration.traeger () :=
  checkCarriers_sound (declaration.traeger ()) boundedLength rfl

def initial : World declaration where
  slots := fun _ _ _ => ⟨4, by decide, by decide⟩
  globs := fun (name : Bool) =>
    match name with
    | true => ⟨8, by decide, by decide⟩
    | false => ⟨3, by decide, by decide⟩
  spur := []

theorem boundedLength_true_zeuge : eval initial boundedLength initial .nil = true := by
  apply (boundedLength_sound_zeuge initial).mpr
  change (3 : Int) ≤ 8 ∧ (0 : Int) ≤ 3
  constructor <;> omega

def invalidLengthWorld : World declaration :=
  { initial with
    globs := fun (name : Bool) =>
      match name with
      | true => ⟨8, by decide, by decide⟩
      | false => ⟨9, by decide, by decide⟩ }

theorem boundedLength_false_zeuge :
    eval invalidLengthWorld boundedLength invalidLengthWorld .nil = false := by
  change wahr? (eval invalidLengthWorld boundedLength invalidLengthWorld .nil) = false
  apply Bool.eq_false_iff.mpr
  intro holds
  have impossible := (boundedLength_sound_zeuge invalidLengthWorld).mp holds
  change (9 : Int) ≤ 8 ∧ (0 : Int) ≤ 9 at impossible
  omega

def product : Expr declaration [] [] .bool :=
  .le (.mul (.glob false (globalAccess false)) (.glob true (globalAccess true))) (.lit 3)

theorem product_refused_zeuge :
    uebersetzeB (declaration.traeger ()) product = .error (.within "left" .nonlinear) := by
  rfl

/-- A genuine two-index sortedness condition on a three-entry table. -/
def sorted : Expr declaration [] [] .bool :=
  .forallSlots ()
    (.forallSlots ()
      (.or (.not (.lt (.var (.there .here)) (.var .here)))
        (.le (.slot () () (.var (.there .here)) slotAccess)
          (.slot () () (.var .here) slotAccess))) slotAccess) slotAccess

theorem sorted_refused_zeuge :
    uebersetzeB (declaration.traeger ()) sorted =
      .error (.within "forallSlots.body" .crossEntry) := by rfl

/-- A nonempty, one-index local invariant is admitted. -/
def localBound : Expr declaration [] [] .bool :=
  .forallSlots () (.le (.slot () () (.var .here) slotAccess) (.lit 10)) slotAccess

def localFormula : LProp (Observation declaration) :=
  .and (.le (.var (.slot () () 0)) (.konst 10))
    (.and (.le (.var (.slot () () 1)) (.konst 10))
      (.and (.le (.var (.slot () () 2)) (.konst 10)) .tru))

theorem localBound_translated_zeuge :
    uebersetzeB (declaration.traeger ()) localBound = .ok localFormula := by rfl

theorem localBound_admitted_zeuge :
    imFragmentB (declaration.traeger ()) localBound = true := by
  simp only [imFragmentB, localBound_translated_zeuge]

/-- String contents never enter the arithmetic problem; their length does. -/
def stringDeclaration : Deklaration :=
  { declaration with
    gtyp := fun (name : Bool) => match name with | true => .int 0 10 | false => .str 10 }

def stringBound : Expr stringDeclaration [] [] .bool :=
  .le (.strLen (Expr.glob (D := stringDeclaration) false (fun _ h => nomatch h)))
    (Expr.glob (D := stringDeclaration) true (fun _ h => nomatch h))

theorem stringBound_translated_zeuge :
    uebersetzeB (stringDeclaration.traeger ()) stringBound =
      .ok (.le (.var (.glob false)) (.var (.glob true))) := by rfl

def scaled : Expr declaration [] [] .bool :=
  .le (.mul (.lit 2) (.glob false (globalAccess false))) (.lit 20)

theorem scaled_translated_zeuge :
    uebersetzeB (declaration.traeger ()) scaled =
      .ok (.le (.scale 2 (.var (.glob false))) (.konst 20)) := by rfl

theorem carriers_checked_first_zeuge :
    uebersetzeB [] product = .error .outsideCarriers := by rfl

def emptyDeclaration : Deklaration :=
  { declaration with count := fun _ => 0 }

def emptyNonlinear : Expr emptyDeclaration [] [] .bool :=
  .forallSlots ()
    (.le (.mul (Expr.glob (D := emptyDeclaration) false (fun _ h => nomatch h))
      (Expr.glob (D := emptyDeclaration) true (fun _ h => nomatch h))) (.lit 3))
    (fun _ h => nomatch h)

theorem emptyNonlinear_refused_zeuge :
    uebersetzeB (emptyDeclaration.traeger ()) emptyNonlinear =
      .error (.within "forallSlots.body" (.within "left" .nonlinear)) := by rfl

def atomicDeclaration : Deklaration :=
  { declaration with
    atomar := fun _ => true
    ggeteilt_bewacht := fun _ h => nomatch h }

def atomicBound : Expr atomicDeclaration [] [] .bool :=
  .le (Expr.glob (D := atomicDeclaration) false (fun _ h => nomatch h)) (.lit 3)

theorem atomicBound_refused_zeuge :
    uebersetzeB (atomicDeclaration.traeger ()) atomicBound = .error .atomicCarrier := by rfl

theorem constant_sound_zeuge (values : Assignment Nat) :
    (LTerm.add (.scale (-3) (.konst 2)) (.konst 5)).denote values = -1 :=
  LTerm.constant?_sound rfl values

/-- The standalone QE syntax also has actual integer quantifiers. -/
def quantified : LProp Nat :=
  .all 0 (.ex 1 (.eq (.var 1) (.add (.var 0) (.konst 1))))

theorem quantified_zeuge (values : Assignment Nat) : quantified.denote values := by
  intro value
  refine ⟨value + 1, ?_⟩
  simp [LProp.denote, LTerm.denote, Assignment.bind]

end Gabbro.Grammatik.Invarianten.Frag.Witness
