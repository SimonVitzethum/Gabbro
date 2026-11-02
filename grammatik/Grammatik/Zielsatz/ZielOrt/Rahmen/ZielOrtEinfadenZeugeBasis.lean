/-
  File:      Grammatik/ZielOrtEinfadenZeuge.lean
  Subject:   WITNESSES for `ziel_ort_einfaden` (one active thread, no
             footprint check).

  1. Corpus 104 (`r4P`, thread 0 the driver, every other thread idle in
     `ruhe`): certified by `ziel_ort_einfaden` WITHOUT `fussOrtGB`.
  2. A sequential program BOTH footprint checks refuse: an UNGUARDED table
     (no lock at all, not shared) written by `setze` and required by
     `pruefe` (`requires konto[0] == 5`); `haupt` calls `setze` then
     `pruefe`, so its caller duty rests on `setze`'s `ensures` across two
     calls. `ePB_fussG_falsch`/`eP_fussS_falsch`: the checks fail;
     `ziel_ort_einfaden_zeuge`: every premise of `ziel_ort_einfaden` holds,
     and on a reached run `pruefe`'s `requires` holds at its logged entry,
     BY THE THEOREM, over the value `setze` wrote.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
@[expose] public section


namespace Gabbro.Grammatik

/-! ## 1. Corpus 104 without the footprint check -/

theorem r4_ruhig : ∀ u, u ≠ 0 → ruhig r4P (r4Init u).1 = true := by
  intro u hu
  unfold r4Init
  rw [if_neg hu]
  decide

/-- **`ziel_ort_einfaden_ref104`**: `beispiele/0104-referenz.gab` certified by
    the one-thread theorem, whose premises contain no footprint check. -/
theorem ziel_ort_einfaden_ref104 :
    ∀ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M →
      VertragAmOrtG r4P M ∧ SperrInvG (SperrInv.leer r4D) M ∧ KeinLogikHaltG r4O 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG r4P r4O 0 M t M' :=
  ziel_ort_einfaden r4P r4O 0 (axWahr r4D) (SperrInv.leer r4D) r4Fs r4Sp r4Init r4O_gut
    r4O_lokal (axVertragO_wahr r4O) axEnsLokal_wahr sperrInvOk_leer r4Fs_voll r4P_fragmentG r4_ruhig
    (fun f => koerperGutS_leer (r4P_koerperZ f)) r4P_start (fun _ => rfl)

/-! ## 2. An unguarded sequential program -/

inductive EFn where
  | setze
  | pruefe
  | haupt
  | ruhe
  deriving DecidableEq

def eSigSetze : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def eSigLeer : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration: one table `konto` (one slot, values `0 .. 100`) with
    NO guard (not shared), no lock used. -/
def eD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := EFn
  sig := fun | .setze => 0 | .haupt => 0 | _ => 1
  sigNr := fun | 0 => eSigSetze | _ => eSigLeer
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
  geteilt_bewacht := fun t h => by cases h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def eSetze : eD.Fn := EFn.setze
def ePruefe : eD.Fn := EFn.pruefe
def eHaupt : eD.Fn := EFn.haupt
def eRuhe : eD.Fn := EFn.ruhe

theorem eDarf (Λ : List (Res eD)) : darf eD () Λ := fun _ h => nomatch h

def eIdx {Γ : Ctx} {Λ : List (Res eD)} : Expr eD Γ Λ (.index (eD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

def eFuenf {Γ : Ctx} {Λ : List (Res eD)} : Expr eD Γ Λ (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 5)

/-- `konto[0] == 5`. -/
def eFuenfGleich {Γ : Ctx} {Λ : List (Res eD)} : Expr eD Γ Λ .bool :=
  .eq (.slot () () eIdx (eDarf Λ)) eFuenf

theorem eHp (caller callee : eD.Fn) (hw : ∀ t, (eD.signatur callee).schreibt t = true →
    (vertragVon eD caller).schreibt t = true) (hh : (eD.signatur callee).haelt = [])
    (hk : (eD.signatur callee).konsumiert = []) :
    RufPasst eD (vertragVon eD caller) (eD.signatur callee) [] where
  hw := hw
  hg := fun g => nomatch g
  hb := fun c hc => by revert hc; cases caller <;> intro hc <;> cases hc
  hk := by
    unfold Signatur.inputMarks
    rw [hk, OwnerFlow.empty_of_empty (eD.signatur callee).owner]
    exact ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl]⟩
  hh := RufPasst.hh_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)
  hx := RufPasst.hx_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)

theorem eHpSetze : RufPasst eD (vertragVon eD eHaupt) (eD.signatur eSetze) [] :=
  eHp eHaupt eSetze (fun _ _ => rfl) rfl rfl

theorem eHpPruefe : RufPasst eD (vertragVon eD eHaupt) (eD.signatur ePruefe) [] :=
  eHp eHaupt ePruefe (fun _ h => by cases h) rfl rfl

/-- `setze`: `konto[0] = 5; return`. -/
def eRumpfSetze : Endblock eD (vertragVon eD eSetze) false [] [] :=
  .cons (.assignSlot () () eIdx eFuenf rfl (eDarf _)) (.ret .empty List.Perm.nil)

/-- `pruefe`: `return` (its `requires` is the point). -/
def eRumpfPruefe : Endblock eD (vertragVon eD ePruefe) false [] [] := .ret .empty List.Perm.nil

/-- `haupt`: `setze(); pruefe(); return`. -/
def eRumpfHaupt : Endblock eD (vertragVon eD eHaupt) false [] [] :=
  .cons (.call eSetze .nil eHpSetze rfl) (.cons (.call ePruefe .nil eHpPruefe rfl)
    (.ret .empty List.Perm.nil))

def eRumpfRuhe : Endblock eD (vertragVon eD eRuhe) false [] [] := .ret .empty List.Perm.nil

/-- The program: `setze` ensures `konto[0] == 5`, `pruefe` REQUIRES it. -/
def eP : Programm eD where
  invariante := fun i => nomatch i
  requires
    | .pruefe => eFuenfGleich
    | _ => .tru
  ensures
    | .setze => eFuenfGleich
    | _ => .tru
  rumpf
    | .setze => eRumpfSetze
    | .pruefe => eRumpfPruefe
    | .haupt => eRumpfHaupt
    | .ruhe => eRumpfRuhe


end Gabbro.Grammatik
