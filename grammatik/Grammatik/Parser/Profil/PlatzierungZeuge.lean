module

public import Grammatik.Parser.Profil.Platzierung
public import Grammatik.Kern.Semantik.Semantik
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/PlatzierungZeuge.lean
  Subject:   WITNESSES for static placement (C14): two multiword-aligned statics (one mutable in a
             writable region, one read-only in a read-only region, neutral section labels, no ELF) read off
             source items, admitted against a policy, turned into the model's `PlatzOk` for a layout of two
             globals (JOINT: source, Bool, model, layout); then one negative twin per refusal.
-/

namespace Gabbro.Grammatik.Parser.ProfilBindung

open Gabbro.Grammatik

set_option maxRecDepth 100000

/-- The fixture's items: a constant alignment, a literal alignment, two section labels. -/
def pzItems : List SItemTief :=
  [ .constT "ALIGN" (.atom "u32") (.one (.lit 16)),
    .globT true "buffer" (.atom "u64") (.one (.lit 0)) (some (.variable "ALIGN")) (some "rw_region") false,
    .globT false "table_ro" (.atom "u64") (.one (.lit 0)) (some (.lit 8)) (some "ro_region") false ]

/-- The expected requests. -/
def pzEintraege : List PlatzEintrag :=
  [⟨["buffer"], 16, some "rw_region", true⟩, ⟨["table_ro"], 8, some "ro_region", false⟩]

/-- The policy of the selected image: labels only. -/
def pzPol : List (String × Zugriff) :=
  [("rw_region", ⟨true, true, false⟩), ("ro_region", ⟨true, false, false⟩)]

/-- The source yields the requests, constant and literal alignments evaluated. -/
theorem pz_quelle : (platzierungVon pzItems).toOption = some pzEintraege := by decide

/-- The requests are admitted against the policy. -/
theorem pz_zulaessig : platzB pzPol pzEintraege = true := by decide

/-- The declaration with two globals (`false` and `true`), no tables. -/
def pzSig : Signatur Empty Bool Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun _ => true
  konsumiert := []
  produziert := []

def pzD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Bool
  decGlob := inferInstance
  gtyp := fun _ => .int 0 255
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => t.elim
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => pzSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by simp only [Bool.false_eq_true] at h

/-- `true` is `buffer`, `false` is `table_ro`. -/
def pzGl : pzD.Glob → PlatzEintrag
  | true => ⟨["buffer"], 16, some "rw_region", true⟩
  | false => ⟨["table_ro"], 8, some "ro_region", false⟩

/-- A layout of the two statics: `buffer` at 0 (16 bytes), `table_ro` at 16 (16 bytes). -/
def pzL : AdressLayout pzD where
  raum := fun t => t.elim
  basis := fun t => t.elim
  breite := fun t => t.elim
  versatz := fun t _ => t.elim
  groesse := fun t _ => t.elim
  gbasis := fun g => match g with
    | true => 0
    | false => 16
  ggroesse := fun _ => 16

/-- The layout is correct: the two statics' regions are disjoint. -/
theorem pzL_ok : LayoutOk pzL where
  geschlossen := fun t => t.elim
  offen := fun t => t.elim
  feld := fun t _ => t.elim
  felder := fun t _ _ _ => t.elim
  tabellen := fun t _ _ _ => t.elim
  tabGlob := fun t _ _ _ => t.elim
  globale := by
    intro g g' a hne ha hb
    obtain ⟨_, h1, h2⟩ := ha
    obtain ⟨_, h3, h4⟩ := hb
    cases g <;> cases g' <;>
      first
      | exact absurd rfl hne
      | (simp only [pzL] at h1 h2 h3 h4; omega)

/-- JOINT witness: the admitted source requests, the layout's bases on the alignments, and the model's
    `PlatzOk` -- the whole chain on one fixture. -/
theorem pz_von_quelle :
    PlatzOk pzL (platzVon pzD pzGl) (politikFun pzPol) (fun g => (pzGl g).schreibbar) := by
  refine platzOk_von_platzB pzL pzPol pzEintraege pzGl ?_ pz_zulaessig ?_
  · intro g
    cases g <;> decide
  · intro g
    cases g <;> decide

/-- The consequences: the read-only static is in a non-writable section, the mutable one in a writable. -/
theorem pz_folgen :
    (∃ z, politikFun pzPol "ro_region" = some z ∧ z.schreiben = false) ∧
    (∃ z, politikFun pzPol "rw_region" = some z ∧ z.schreiben = true) :=
  ⟨platz_nur_lesen pz_von_quelle (g := false) (s := "ro_region") rfl rfl,
   platz_schreibbar pz_von_quelle (g := true) (s := "rw_region") rfl rfl⟩

/-! ### Negative twins -/

/-- A policy's one request helper. -/
def pzEin (a : Nat) (s : Option String) (w : Bool) (n : String) : PlatzEintrag := ⟨[n], a, s, w⟩

/-- An alignment that is no power of two. -/
theorem pz_nicht_potenz : platzB pzPol [pzEin 12 none true "x"] = false := by decide

/-- Alignment zero. -/
theorem pz_null : platzB pzPol [pzEin 0 none true "x"] = false := by decide

/-- An unknown section. -/
theorem pz_abschnitt_unbekannt : platzB pzPol [pzEin 8 (some "nowhere") true "x"] = false := by decide

/-- A section both writable and executable. -/
theorem pz_wx :
    platzB [("wx", ⟨true, true, true⟩)] [pzEin 8 (some "wx") true "x"] = false := by decide

/-- A read-only static in a writable section. -/
theorem pz_ro_in_rw : platzB pzPol [pzEin 8 (some "rw_region") false "x"] = false := by decide

/-- A mutable static in a read-only section. -/
theorem pz_rw_in_ro : platzB pzPol [pzEin 8 (some "ro_region") true "x"] = false := by decide

/-- The same object placed twice. -/
theorem pz_doppelt :
    platzB pzPol [pzEin 8 none true "x", pzEin 8 none true "x"] = false := by decide

/-- An alignment that is no constant is refused at extraction. -/
theorem pz_nicht_konstant :
    (platzierungVon [.globT true "g" (.atom "u64") (.one (.lit 0)) (some (.variable "UNKNOWN")) none false]).toOption
      = none := by decide

#print axioms Gabbro.Grammatik.Parser.ProfilBindung.pz_von_quelle

end Gabbro.Grammatik.Parser.ProfilBindung
