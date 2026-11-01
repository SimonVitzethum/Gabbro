module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Programme.Export108
public import Grammatik.Korpus.Zeugnis.ZeugnisKorpus.Teil1

@[expose] public section

namespace Gabbro.Grammatik

def D59V_zaehle : Vertrag D59D :=
  { schreibt := fun | .Takte => true | _ => false, gschreibt := fun _ => false,
    erg := none, gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `zaehle` (`beispiele/59-eintritt-nimmt-maskierte-sperre.gab`). -/
def cd59_zaehle : CertEnd2 D59D D59V_zaehle := (.liftE (.cons (.assignSlot D59Tab.Takte D59FeldTakte.stand (.var 0) (.wide 0 18446744073709551615 (.lit 1))) [] .ret))

example : certEnd2Ok D59D D59V_zaehle false [(.int 0 63)] [] cd59_zaehle = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock D59D D59V_zaehle false [(.int 0 63)] [], True :=
  zeugnisStmt2_sound D59D D59V_zaehle false [(.int 0 63)] [] cd59_zaehle (by decide)

/-- Contract for `bearbeite` (`beispiele/59-eintritt-nimmt-maskierte-sperre.gab`): writes Auftraege. -/
def D59V_bearbeite : Vertrag D59D :=
  { schreibt := fun | .Auftraege => true | _ => false, gschreibt := fun _ => false,
    erg := none, gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `bearbeite` (`beispiele/59-eintritt-nimmt-maskierte-sperre.gab`). -/
def cd59_bearbeite : CertEnd2 D59D D59V_bearbeite := (.liftE (.cons (.assignSlot D59Tab.Auftraege D59FeldAuftraege.stand (.var 0) (.wide 0 18446744073709551615 (.lit 1))) [] .ret))

example : certEnd2Ok D59D D59V_bearbeite false [(.int 0 15)] [] cd59_bearbeite = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock D59D D59V_bearbeite false [(.int 0 15)] [], True :=
  zeugnisStmt2_sound D59D D59V_bearbeite false [(.int 0 15)] [] cd59_bearbeite (by decide)

/-! ## Hand declaration for `109-lockfree-entry-roots.gab` (no `lean-g` export) -/

inductive D109Tab where
| T
| U
  deriving DecidableEq

inductive D109FeldT where
  | v
  deriving DecidableEq

inductive D109FeldU where
  | v
  deriving DecidableEq

/-- Dummy signature: this declaration names no functions, but
    `sigNr` still needs a value (no call validity ever reads it). -/
def D109SigDummy : Signatur D109Tab Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev D109D : Deklaration where
  Tab := D109Tab
  decTab := inferInstance
  count := fun
  | .T => 4
  | .U => 4
  Feld := fun | .T => D109FeldT | .U => D109FeldU
  decFeld := fun | .T => inferInstance | .U => inferInstance
  typ := fun
  | .T, .v => (.int 0 4294967295)
  | .U, .v => (.int 0 4294967295)
  erlaubt := fun _ _ _ _ => false
  tabNr := fun
  | 0 => some D109Tab.T
  | 1 => some D109Tab.U
  | _ => none
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
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => D109SigDummy
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => by cases t <;> decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- Contract for `write_a` (`beispiele/109-lockfree-entry-roots.gab`): writes T. -/
def D109V_write_a : Vertrag D109D :=
  { schreibt := fun | .T => true | _ => false, gschreibt := fun _ => false,
    erg := none, gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `write_a` (`beispiele/109-lockfree-entry-roots.gab`). -/
def cd109_write_a : CertEnd2 D109D D109V_write_a := (.liftE (.cons (.assignSlot D109Tab.T D109FeldT.v (.var 0) (.wide 0 4294967295 (.lit 1))) [] .ret))

example : certEnd2Ok D109D D109V_write_a false [(.int 0 3)] [] cd109_write_a = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock D109D D109V_write_a false [(.int 0 3)] [], True :=
  zeugnisStmt2_sound D109D D109V_write_a false [(.int 0 3)] [] cd109_write_a (by decide)

/-- Contract for `write_b` (`beispiele/109-lockfree-entry-roots.gab`): writes U. -/
def D109V_write_b : Vertrag D109D :=
  { schreibt := fun | .U => true | _ => false, gschreibt := fun _ => false,
    erg := none, gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `write_b` (`beispiele/109-lockfree-entry-roots.gab`). -/
def cd109_write_b : CertEnd2 D109D D109V_write_b := (.liftE (.cons (.assignSlot D109Tab.U D109FeldU.v (.var 0) (.wide 0 4294967295 (.lit 2))) [] .ret))

example : certEnd2Ok D109D D109V_write_b false [(.int 0 3)] [] cd109_write_b = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock D109D D109V_write_b false [(.int 0 3)] [], True :=
  zeugnisStmt2_sound D109D D109V_write_b false [(.int 0 3)] [] cd109_write_b (by decide)

/-! ## Hand declaration for `112-register-traeger-bewacht.gab` (no `lean-g` export) -/

inductive D112Tab where
| Zustand
  deriving DecidableEq

inductive D112FeldZustand where
  | bereit
  deriving DecidableEq

/-- Dummy signature: this declaration names no functions, but
    `sigNr` still needs a value (no call validity ever reads it). -/
def D112SigDummy : Signatur D112Tab Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev D112D : Deklaration where
  Tab := D112Tab
  decTab := inferInstance
  count := fun
  | .Zustand => 4
  Feld := fun | .Zustand => D112FeldZustand
  decFeld := fun | .Zustand => inferInstance
  typ := fun
  | .Zustand, .bereit => (.int 0 4294967295)
  erlaubt := fun _ _ _ _ => false
  tabNr := fun
  | 0 => some D112Tab.Zustand
  | _ => none
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
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => D112SigDummy
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => by cases t <;> decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- Contract for `schreiben` (`beispiele/112-register-traeger-bewacht.gab`): writes Zustand. -/
def D112V_schreiben : Vertrag D112D :=
  { schreibt := fun | .Zustand => true, gschreibt := fun _ => false,
    erg := some (.int 0 4294967295), gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `schreiben` (`beispiele/112-register-traeger-bewacht.gab`). -/
def cd112_schreiben : CertEnd2 D112D D112V_schreiben := (.liftE (.cons (.assignSlot D112Tab.Zustand D112FeldZustand.bereit (.var 0) (.var 1)) [] (.retWert (.wide 0 4294967295 (.lit 0)) 0 4294967295)))

example : certEnd2Ok D112D D112V_schreiben false [(.int 0 3), (.int 0 4294967295)] [] cd112_schreiben = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock D112D D112V_schreiben false [(.int 0 3), (.int 0 4294967295)] [], True :=
  zeugnisStmt2_sound D112D D112V_schreiben false [(.int 0 3), (.int 0 4294967295)] [] cd112_schreiben (by decide)

/-! ## Hand declaration for `44-register-einmal-lesen.gab` (no `lean-g` export) -/

inductive D44Tab where
| Auftrag
  deriving DecidableEq

inductive D44FeldAuftrag where
  | gewicht
  deriving DecidableEq

/-- Dummy signature: this declaration names no functions, but
    `sigNr` still needs a value (no call validity ever reads it). -/
def D44SigDummy : Signatur D44Tab Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev D44D : Deklaration where
  Tab := D44Tab
  decTab := inferInstance
  count := fun
  | .Auftrag => 8
  Feld := fun | .Auftrag => D44FeldAuftrag
  decFeld := fun | .Auftrag => inferInstance
  typ := fun
  | .Auftrag, .gewicht => (.int 0 4294967295)
  erlaubt := fun _ _ _ _ => false
  tabNr := fun
  | 0 => some D44Tab.Auftrag
  | _ => none
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
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => D44SigDummy
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => by cases t <;> decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- Contract for `gewicht_bei` (`beispiele/44-register-einmal-lesen.gab`): writes nothing. -/
def D44V_gewicht_bei : Vertrag D44D :=
  { schreibt := fun _ => false, gschreibt := fun _ => false,
    erg := some (.int 0 4294967295), gruende := 0, haelt := [], produziert := [] }

/-- Verbatim printer output for `gewicht_bei` (`beispiele/44-register-einmal-lesen.gab`). -/
def cd44_gewicht_bei : CertEnd2 D44D D44V_gewicht_bei := (.liftE (.retWert (.slot D44Tab.Auftrag D44FeldAuftrag.gewicht (.var 0)) 0 4294967295))

example : certEnd2Ok D44D D44V_gewicht_bei false [(.int 0 7)] [] cd44_gewicht_bei = true := by
  decide

/-- End to end: the valid print YIELDS an accepted body. -/
example : ∃ _ : Endblock D44D D44V_gewicht_bei false [(.int 0 7)] [], True :=
  zeugnisStmt2_sound D44D D44V_gewicht_bei false [(.int 0 7)] [] cd44_gewicht_bei (by decide)

/-
  CUTS: what is not proved here.
  - The pastes cover the 27 pure-int prints, the two 108 slot bodies
    (over the real export) and hand-declaration slot bodies
    (29 plus hand-declared). The two 104 bodies live in
    `ZeugnisStmt104b.lean`. Remaining slot bodies need their own minimal
    declaration after this pattern; pointer/call bodies (13, 14, 16, 25,
    47, 52, 72) need per-body proof terms (`End104Args`: argument lists,
    `RufPasst`, pointers) after lane 155's 104 pattern.
  - The print-to-body link (`print (elab x) = x`) is trust base everywhere
    (the `ZeugnisStmt2.lean` CUTS booking): `decide` accepts the pasted
    term, it does not re-derive it from the source.
  - No named theorems: the checks are `rfl`/`decide` evaluations over
    `certEnd2Gueltig`/`certRange` (axioms those of `Zeugnis.lean` and
    `ZeugnisStmt2.lean`: `propext, Classical.choice, Quot.sound`).
-/

end Gabbro.Grammatik
