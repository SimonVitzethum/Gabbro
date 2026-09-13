/-
  File:      Grammatik/Export108.lean
  Subject:   the mechanical export of
             `beispiele/108-disjoint-start-locks.gab` (two readers under
             disjoint signature locks) and its two decidable checks.

  The `namespace G108_disjoint_start_locks` block below is pasted verbatim
  from the output of `gabbro lean-g beispiele/108-disjoint-start-locks.gab`
  (only its `import` line is left out; this file imports instead). There is
  no hand translation of 108 to hold it against; what is proved here is
  that the export's fragment and footprint checks hold, and the declaration
  data they rest on (counts, ranks, guards, held sets).
-/
import Grammatik.ZielOrtGeraetSem

namespace Gabbro.Grammatik

namespace G108_disjoint_start_locks

inductive GTab where
  | T
  | U
  deriving DecidableEq

inductive GLock where
  | L
  | M
  deriving DecidableEq

inductive GTFeld where
  | v
  deriving DecidableEq

inductive GUFeld where
  | v
  deriving DecidableEq

inductive GFn where
  | read_a
  | read_c
  deriving DecidableEq

def gSig_read_a : Signatur GTab Empty GLock Empty where
  params := []
  erg := some (.int 0 4294967295)
  gruende := 0
  haelt := [GLock.L]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def gSig_read_c : Signatur GTab Empty GLock Empty where
  params := []
  erg := some (.int 0 4294967295)
  gruende := 0
  haelt := [GLock.M]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev gD : Deklaration where
  Tab := GTab
  decTab := inferInstance
  count := fun | .T => 4 | .U => 4
  Feld := fun | .T => GTFeld | .U => GUFeld
  decFeld := fun | .T => inferInstance | .U => inferInstance
  typ := fun | .T, .v => .int 0 4294967295 | .U, .v => .int 0 4294967295
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some GTab.T | 1 => some GTab.U | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun | .T => true | .U => true
  ggeteilt := fun e => nomatch e
  Lock := GLock
  decLock := inferInstance
  rang := fun | .L => 0 | .M => 1
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun | .T => [.inl GLock.L] | .U => [.inl GLock.M]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := GFn
  sig := fun | .read_a => 0 | .read_c => 1
  sigNr := fun | 0 => gSig_read_a | 1 => gSig_read_c | _ => gSig_read_c
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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

abbrev gCtx_read_a : Ctx := []
abbrev gL_read_a : List (Res gD) := [Res.held (D := gD) GLock.L]
def g_read_a : gD.Fn := GFn.read_a
theorem gDarf_read_a_T : darf gD GTab.T gL_read_a := by unfold darf; decide

abbrev gCtx_read_c : Ctx := []
abbrev gL_read_c : List (Res gD) := [Res.held (D := gD) GLock.M]
def g_read_c : gD.Fn := GFn.read_c
theorem gDarf_read_c_U : darf gD GTab.U gL_read_c := by unfold darf; decide

def gBody_read_a : Endblock gD (vertragVon gD g_read_a) false gCtx_read_a gL_read_a :=
  (.ret (.wert (Expr.slot (D := gD) GTab.T GTFeld.v (((.weiter (by decide) (by decide) (.lit 0) : Expr gD gCtx_read_a gL_read_a (.index (gD.count GTab.T))))) gDarf_read_a_T)) (List.Perm.refl _))

def gBody_read_c : Endblock gD (vertragVon gD g_read_c) false gCtx_read_c gL_read_c :=
  (.ret (.wert (Expr.slot (D := gD) GTab.U GUFeld.v (((.weiter (by decide) (by decide) (.lit 0) : Expr gD gCtx_read_c gL_read_c (.index (gD.count GTab.U))))) gDarf_read_c_U)) (List.Perm.refl _))

def gP : Programm gD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .read_a => .wahr
    | .read_c => .wahr
  rumpf
    | .read_a => gBody_read_a
    | .read_c => gBody_read_c

def gFs : List gD.Fn := [g_read_a, g_read_c]

example : programmImFragmentG gP gFs = true := by decide

example : fussOrtGB gP gFs = true := by decide

end G108_disjoint_start_locks

/-! ## The checks and the data they rest on -/

/-- The export's own checks, as theorems (the generated file states them as
    `example`s, which cannot be named). -/
theorem export108_fragment : programmImFragmentG G108_disjoint_start_locks.gP G108_disjoint_start_locks.gFs = true := by decide

theorem export108_fuss : fussOrtGB G108_disjoint_start_locks.gP G108_disjoint_start_locks.gFs = true := by decide

/-- The declaration data: table counts, lock ranks, guards, and the two
    disjoint signature-held sets (`read_a` holds `L`, `read_c` holds `M` --
    the surface `concurrent` pair's `StartExklusiv` side). -/
theorem export108_data :
    G108_disjoint_start_locks.gD.count G108_disjoint_start_locks.GTab.T = 4 ∧
    G108_disjoint_start_locks.gD.count G108_disjoint_start_locks.GTab.U = 4 ∧
    G108_disjoint_start_locks.gD.rang G108_disjoint_start_locks.GLock.L = 0 ∧
    G108_disjoint_start_locks.gD.rang G108_disjoint_start_locks.GLock.M = 1 ∧
    G108_disjoint_start_locks.gD.braucht G108_disjoint_start_locks.GTab.T =
      [.inl G108_disjoint_start_locks.GLock.L] ∧
    G108_disjoint_start_locks.gD.braucht G108_disjoint_start_locks.GTab.U =
      [.inl G108_disjoint_start_locks.GLock.M] ∧
    G108_disjoint_start_locks.gD.haelt G108_disjoint_start_locks.g_read_a =
      [G108_disjoint_start_locks.GLock.L] ∧
    G108_disjoint_start_locks.gD.haelt G108_disjoint_start_locks.g_read_c =
      [G108_disjoint_start_locks.GLock.M] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## CUTS:

  What is proved: the mechanical export of
  `beispiele/108-disjoint-start-locks.gab` checks (`export108_fragment`,
  `export108_fuss`) and its declaration data (`export108_data`).

  What is NOT proved: anything about runs or user obligations -- 108 has
  no contracts beyond `Held` and no hand translation to hold against. The
  surface `concurrent { read_a, read_c }` has no G counterpart (all
  functions travel in `gFs`); its checker side (`StartExklusiv`, N240) is
  not re-proved here. The bare `u32` field type travels as its full range
  `.int 0 4294967295`, the numbers the checker computes with.
-/

#print axioms Gabbro.Grammatik.export108_fragment
#print axioms Gabbro.Grammatik.export108_fuss
#print axioms Gabbro.Grammatik.export108_data

end Gabbro.Grammatik
