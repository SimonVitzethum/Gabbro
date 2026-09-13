/-
  File:      Grammatik/ExportSperre.lean
  Subject:   the mechanical export of `beispiele/118-sperrinvariante-erhaltung.gab`
             (lane 156): the `SperrInv` lock invariant family for a
             conserved-sum invariant over two carriers under one lock.

  The `namespace G118_sperrinvariante_erhaltung` block below is pasted
  verbatim from the output of
  `gabbro lean-g beispiele/118-sperrinvariante-erhaltung.gab` (only its two
  `import` lines are left out; this file imports instead). What follows the
  paste is the correspondence: `gS_orte_K` exhibits the `orte` list as
  exactly the `protects` set, by `rfl`.
-/
import Grammatik.ZielOrtGeraetSem
import Grammatik.SperreSem

namespace Gabbro.Grammatik

namespace G118_sperrinvariante_erhaltung

inductive GTab where
  | A
  | B
  deriving DecidableEq

inductive GLock where
  | K
  deriving DecidableEq

inductive GAFeld where
  | x
  deriving DecidableEq

inductive GBFeld where
  | y
  deriving DecidableEq

inductive GFn where
  | gib
  | nimm
  deriving DecidableEq

def gSig_gib : Signatur GTab Empty GLock Empty where
  params := [.ptr 0 true, .ptr 1 true]
  erg := none
  gruende := 0
  haelt := [GLock.K]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def gSig_nimm : Signatur GTab Empty GLock Empty where
  params := [.ptr 0 true, .ptr 1 true]
  erg := none
  gruende := 0
  haelt := [GLock.K]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev gD : Deklaration where
  Tab := GTab
  decTab := inferInstance
  count := fun | .A => 2 | .B => 2
  Feld := fun | .A => GAFeld | .B => GBFeld
  decFeld := fun | .A => inferInstance | .B => inferInstance
  typ := fun | .A, .x => .int 0 100 | .B, .y => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some GTab.A | 1 => some GTab.B | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun | .A => true | .B => true
  ggeteilt := fun e => nomatch e
  Lock := GLock
  decLock := inferInstance
  rang := fun | .K => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun | .A => [.inl GLock.K] | .B => [.inl GLock.K]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := GFn
  sig := fun | .gib => 0 | .nimm => 1
  sigNr := fun | 0 => gSig_gib | 1 => gSig_nimm | _ => gSig_nimm
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

abbrev gCtx_gib : Ctx := [.ptr 0 true, .ptr 1 true]
abbrev gL_gib : List (Res gD) := [Res.held (D := gD) GLock.K]
def g_gib : gD.Fn := GFn.gib
theorem gDarf_gib_A : darf gD GTab.A gL_gib := by unfold darf; decide
theorem gDarf_gib_B : darf gD GTab.B gL_gib := by unfold darf; decide

abbrev gCtx_nimm : Ctx := [.ptr 0 true, .ptr 1 true]
abbrev gL_nimm : List (Res gD) := [Res.held (D := gD) GLock.K]
def g_nimm : gD.Fn := GFn.nimm
theorem gDarf_nimm_A : darf gD GTab.A gL_nimm := by unfold darf; decide
theorem gDarf_nimm_B : darf gD GTab.B gL_nimm := by unfold darf; decide

def gBody_gib : Endblock gD (vertragVon gD g_gib) false gCtx_gib gL_gib :=
  (.cons (.assignDurch (.var .hier) GTab.A rfl GAFeld.x (((.weiter (by decide) (by decide) (.lit 0) : Expr gD gCtx_gib gL_gib (.index (gD.count GTab.A))))) (.weiter (by decide) (by decide) (.lit 30)) (by decide) gDarf_gib_A) (.cons (.assignDurch (.var (.dort .hier)) GTab.B rfl GBFeld.y (((.weiter (by decide) (by decide) (.lit 0) : Expr gD gCtx_gib gL_gib (.index (gD.count GTab.B))))) (.weiter (by decide) (by decide) (.lit 70)) (by decide) gDarf_gib_B) (.ret .keine (List.Perm.refl _))))

def gBody_nimm : Endblock gD (vertragVon gD g_nimm) false gCtx_nimm gL_nimm :=
  (.cons (.assignDurch (.var .hier) GTab.A rfl GAFeld.x (((.weiter (by decide) (by decide) (.lit 0) : Expr gD gCtx_nimm gL_nimm (.index (gD.count GTab.A))))) (.weiter (by decide) (by decide) (.lit 10)) (by decide) gDarf_nimm_A) (.cons (.assignDurch (.var (.dort .hier)) GTab.B rfl GBFeld.y (((.weiter (by decide) (by decide) (.lit 0) : Expr gD gCtx_nimm gL_nimm (.index (gD.count GTab.B))))) (.weiter (by decide) (by decide) (.lit 90)) (by decide) gDarf_nimm_B) (.ret .keine (List.Perm.refl _))))

def gP : Programm gD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .gib => .wahr
    | .nimm => .wahr
  rumpf
    | .gib => gBody_gib
    | .nimm => gBody_nimm

def gFs : List gD.Fn := [g_gib, g_nimm]

example : programmImFragmentG gP gFs = true := by decide

example : fussOrtGB gP gFs = true := by decide

-- The lock invariant family `gS` (`SperrInv`, `SperreSem.lean`):
-- lock K: invariant below
def gS : SperrInv gD where
  orte := fun | .K => [.inl GTab.A, .inl GTab.B]
  inv := fun | .K => fun s => ((((s.slots GTab.A 0 GAFeld.x).n) + ((s.slots GTab.B 0 GBFeld.y).n)) == (100 : Int))

example : ((gS.orte GLock.K).elem (.inl GTab.A) = true) := by decide
example : ((gD.braucht GTab.A).elem (Sum.inl GLock.K) = true) := by decide
example : ((gS.orte GLock.K).elem (.inl GTab.B) = true) := by decide
example : ((gD.braucht GTab.B).elem (Sum.inl GLock.K) = true) := by decide

/-! ## Correspondence: `orte` is exactly the `protects` set -/

-- The surface `lock K protects { A, B }` resolves both carriers (table
-- names, so no field lookup), and the exporter writes them as the `orte`
-- list. This exhibits the list as written, by `rfl`.
theorem gS_orte_K : gS.orte GLock.K = [.inl GTab.A, .inl GTab.B] := rfl

/-! ## CUTS: what is not proved

  1. `SperrInvOk gS` is NOT proved: the guard half travels as four
     `List.elem … = true` decides above (the decidable content, carrier by
     carrier); the read half (`inv` reads only `orte`, over all memories)
     and the release duty (every `locks K` body re-establishes `inv`) are
     the user's obligations, booked as obligation `L` beside the `ensures`
     duties. A bare `∀ L c, …` guard universal is not stated because
     `Decidable (x ∈ l)` fails over sum carriers in this toolchain
     (measured 2026-09-13: `∈` decides over `Nat` but not over `T ⊕ Empty`,
     while `List.elem … = true` decides over both).
  2. `KoerperGut`-style triples, runs and the goal theorem stay where they
     are for every other export: user obligations are proved about the
     program, not re-proved about the export.
-/

#print axioms G118_sperrinvariante_erhaltung.gS_orte_K

end G118_sperrinvariante_erhaltung

end Gabbro.Grammatik
