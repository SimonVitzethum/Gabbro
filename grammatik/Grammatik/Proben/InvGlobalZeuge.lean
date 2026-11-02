/-
  File:      Grammatik/Proben/InvGlobalZeuge.lean
  Subject:   C05 WITNESS (`_zeuge`): an invariant whose carriers are a TABLE and a GLOBAL under TWO locks.
             The declaration `cgD` has one table (guarded by the lock `false`), one global (guarded by the lock
             `true`) and one invariant `()` over both (`traeger () = [inl (), inr ()]`); `nurTab`, `nurGlob`
             hold both locks by signature and write only the table / only the global, `frei` writes nothing.
  * `cg_schuldet_*` -- a writer of the global alone owes the invariant (`schuldet` over `gschreibt`), a writer of
    neither does not;
  * `cg_nurGlob_haelt_tabellensperre` -- U003: the writer of the GLOBAL holds the TABLE's lock
    (`inv_schreiber_sperren` at the table carrier), and `cg_nurTab_haelt_globalsperre` the converse;
  * `cg_invSicht`, `cg_global_wache_sichtbar` -- the invariant's read set holds the guards of BOTH carrier kinds;
  * `cg_mitRuhe_*` -- the idle root keeps the carrier list, owes nothing, and `invSicht` maps.
-/
module
public import Grammatik.Zielsatz.Faeden.RuheNutzer
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
@[expose] public section


namespace Gabbro.Grammatik

/-- A signature holding BOTH locks of the group; it writes the table iff `wt`, the global iff `wg`. -/
def cgSig (wt wg : Bool) : Signatur Unit Unit Bool Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [false, true]
  schreibt := fun _ => wt
  gschreibt := fun _ => wg
  konsumiert := []
  produziert := []

inductive CgFn where
  | nurTab
  | nurGlob
  | frei
  deriving DecidableEq

/-- One table (lock `false`), one global (lock `true`), one invariant over both. -/
def cgD : Deklaration where
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
  Fn := CgFn
  sig := fun | .nurTab => 0 | .nurGlob => 1 | .frei => 2
  sigNr := fun n => cgSig (decide (n = 0)) (decide (n = 1))
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
  invarianten_gehalten := fun _ _ _ _ _ L _ => by cases L <;> simp [cgSig]
  ggeteilt_bewacht := fun _ _ => Or.inl (by decide)

/-! ## 1. Who owes the invariant -/

theorem cg_schuldet_tab : schuldet (D := cgD) CgFn.nurTab () = true := by decide

/-- The writer of the GLOBAL alone owes the invariant: the global is one of its carriers. -/
theorem cg_schuldet_glob : schuldet (D := cgD) CgFn.nurGlob () = true := by decide

theorem cg_schuldet_frei : schuldet (D := cgD) CgFn.frei () = false := by decide

/-- Non-degenerate: the owed-ness of `nurGlob` is the global's, not the table's. -/
theorem cg_nurGlob_schreibt_nur_global :
    cgD.schreibt CgFn.nurGlob () = false ∧ cgD.gschreibt CgFn.nurGlob () = true := by decide

/-! ## 2. U003 over both carrier kinds -/

/-- The writer of the global holds the TABLE's lock (the group's guard set). -/
theorem cg_nurGlob_haelt_tabellensperre : false ∈ cgD.haelt CgFn.nurGlob :=
  inv_schreiber_sperren (D := cgD) CgFn.nurGlob () cg_schuldet_glob (Sum.inl ()) (by decide) false (by decide)

/-- The writer of the table holds the GLOBAL's lock. -/
theorem cg_nurTab_haelt_globalsperre : true ∈ cgD.haelt CgFn.nurTab :=
  inv_schreiber_sperren (D := cgD) CgFn.nurTab () cg_schuldet_tab (Sum.inr ()) (by decide) true (by decide)

/-! ## 3. The read set and the idle root -/

theorem cg_invSicht : invSicht cgD () = [Res.held false, Res.held true] := rfl

/-- The guard of the GLOBAL carrier is in the invariant's read set. -/
theorem cg_global_wache_sichtbar :
    ∃ c ∈ cgD.traeger (), Sum.inl true ∈ Sum.elim cgD.braucht cgD.gbraucht c :=
  held_invSicht (D := cgD) () true (by decide)

theorem cg_mitRuhe_traeger : cgD.mitRuhe.traeger () = [Sum.inl (), Sum.inr ()] := rfl

theorem cg_mitRuhe_ruhe_schuldet : schuldet (D := cgD.mitRuhe) none () = false := schuldet_ruhe (D := cgD) ()

theorem cg_mitRuhe_invSicht :
    (invSicht cgD ()).map resR = invSicht cgD.mitRuhe () := invSicht_map ()

#print axioms Gabbro.Grammatik.cg_nurGlob_haelt_tabellensperre
#print axioms Gabbro.Grammatik.cg_global_wache_sichtbar
#print axioms Gabbro.Grammatik.cg_mitRuhe_invSicht

end Gabbro.Grammatik
