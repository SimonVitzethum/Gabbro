/-
  File:      Grammatik/Proben/InvGlobalZeuge.lean
  Subject:   C05 WITNESS (`_zeuge`): an invariant whose carriers are a TABLE and a GLOBAL under TWO locks.
             The declaration `gzD` has one table (guarded by the lock `false`), one global (guarded by the lock
             `true`) and one invariant `()` over both (`traeger () = [inl (), inr ()]`); `nurTab`, `nurGlob`
             hold both locks by signature and write only the table / only the global, `frei` writes nothing.
  * `gz_schuldet_*` -- a writer of the global alone owes the invariant (`schuldet` over `gschreibt`), a writer of
    neither does not;
  * `gz_nurGlob_haelt_tabellensperre` -- U003: the writer of the GLOBAL holds the TABLE's lock
    (`inv_schreiber_sperren` at the table carrier), and `gz_nurTab_haelt_globalsperre` the converse;
  * `gz_invSicht`, `gz_global_wache_sichtbar` -- the invariant's read set holds the guards of BOTH carrier kinds;
  * `gz_mitRuhe_*` -- the idle root keeps the carrier list, owes nothing, and `invSicht` maps.
-/
module
public import Grammatik.Zielsatz.Faeden.RuheNutzer
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
@[expose] public section


namespace Gabbro.Grammatik

/-- A signature holding BOTH locks of the group; it writes the table iff `wt`, the global iff `wg`. -/
def gzSig (wt wg : Bool) : Signatur Unit Unit Bool Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [false, true]
  schreibt := fun _ => wt
  gschreibt := fun _ => wg
  konsumiert := []
  produziert := []

inductive GzFn where
  | nurTab
  | nurGlob
  | frei
  deriving DecidableEq

/-- One table (lock `false`), one global (lock `true`), one invariant over both. -/
def gzD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 10
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => true
  ggeteilt := fun _ => true
  Lock := Bool
  decLock := inferInstance
  rang := fun L => if L then 1 else 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl false]
  gbraucht := fun _ => [.inl true]
  eigner := fun _ => []
  Fn := GzFn
  sig := fun | .nurTab => 0 | .nurGlob => 1 | .frei => 2
  sigNr := fun n => gzSig (decide (n = 0)) (decide (n = 1))
  eigner_nie_erzeugt := fun _ _ m _ _ => Empty.elim m
  Inv := Unit
  traeger := fun _ => [.inl (), .inr ()]
  invs := [()]
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
  geteilt_bewacht := fun _ _ => by decide
  invarianten_gehalten := fun _ _ _ _ _ L _ => by cases L <;> decide
  ggeteilt_bewacht := fun _ _ => Or.inl (by decide)

/-! ## 1. Who owes the invariant -/

theorem gz_schuldet_tab : schuldet (D := gzD) GzFn.nurTab () = true := by decide

/-- The writer of the GLOBAL alone owes the invariant: the global is one of its carriers. -/
theorem gz_schuldet_glob : schuldet (D := gzD) GzFn.nurGlob () = true := by decide

theorem gz_schuldet_frei : schuldet (D := gzD) GzFn.frei () = false := by decide

/-- Non-degenerate: the owed-ness of `nurGlob` is the global's, not the table's. -/
theorem gz_nurGlob_schreibt_nur_global :
    gzD.schreibt GzFn.nurGlob () = false ∧ gzD.gschreibt GzFn.nurGlob () = true := by decide

/-! ## 2. U003 over both carrier kinds -/

/-- The writer of the global holds the TABLE's lock (the group's guard set). -/
theorem gz_nurGlob_haelt_tabellensperre : false ∈ gzD.haelt GzFn.nurGlob :=
  inv_schreiber_sperren GzFn.nurGlob () gz_schuldet_glob (Sum.inl ()) (by decide) false (by decide)

/-- The writer of the table holds the GLOBAL's lock. -/
theorem gz_nurTab_haelt_globalsperre : true ∈ gzD.haelt GzFn.nurTab :=
  inv_schreiber_sperren GzFn.nurTab () gz_schuldet_tab (Sum.inr ()) (by decide) true (by decide)

/-! ## 3. The read set and the idle root -/

theorem gz_invSicht : invSicht gzD () = [Res.held false, Res.held true] := rfl

/-- The guard of the GLOBAL carrier is in the invariant's read set. -/
theorem gz_global_wache_sichtbar :
    ∃ c ∈ gzD.traeger (), Sum.inl true ∈ Sum.elim gzD.braucht gzD.gbraucht c :=
  held_invSicht () true (by decide)

theorem gz_mitRuhe_traeger : gzD.mitRuhe.traeger () = [Sum.inl (), Sum.inr ()] := rfl

theorem gz_mitRuhe_ruhe_schuldet : schuldet (D := gzD.mitRuhe) none () = false := schuldet_ruhe ()

theorem gz_mitRuhe_invSicht :
    (invSicht gzD ()).map resR = invSicht gzD.mitRuhe () := invSicht_map ()

#print axioms Gabbro.Grammatik.gz_nurGlob_haelt_tabellensperre
#print axioms Gabbro.Grammatik.gz_global_wache_sichtbar
#print axioms Gabbro.Grammatik.gz_mitRuhe_invSicht

end Gabbro.Grammatik
