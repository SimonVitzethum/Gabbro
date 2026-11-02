module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtZeuge

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. The declaration and the program -/

inductive GeTab where
  | geraet
  | notiz
  | tafel
  deriving DecidableEq

inductive GeLock where
  | lg
  | lt
  deriving DecidableEq

inductive GeFn where
  | haupt
  | leser
  | schreiber
  | ruhe
  deriving DecidableEq

def geSigHaupt : Signatur GeTab Empty GeLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [.lg]
  schreibt := fun | .notiz => true | _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def geSigLeser : Signatur GeTab Empty GeLock Empty where
  params := []
  erg := some .bool
  gruende := 0
  haelt := [.lg]
  schreibt := fun | .notiz => true | _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def geSigSchreiber : Signatur GeTab Empty GeLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [.lt]
  schreibt := fun | .tafel => true | _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def geSigRuhe : Signatur GeTab Empty GeLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Three guarded tables, two locks, one register with the device carrier
    `geraet`, four functions, no axiom. -/
def geD : Deklaration where
  Tab := GeTab
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some .geraet | 1 => some .notiz | 2 => some .tafel | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := GeLock
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun | .tafel => [.inl .lt] | _ => [.inl .lg]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := GeFn
  sig := fun | .haupt => 0 | .leser => 1 | .schreiber => 2 | .ruhe => 3
  sigNr := fun | 0 => geSigHaupt | 1 => geSigLeser | 2 => geSigSchreiber | _ => geSigRuhe
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Unit
  rtyp := fun _ => .int 0 1
  rklasse := fun _ => .r
  spiegel := fun _ => none
  rzusage := fun _ _ => true
  rtraeger := fun _ => [.inl .geraet]
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by cases t <;> decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def geHaupt : geD.Fn := GeFn.haupt
def geLeser : geD.Fn := GeFn.leser
def geSchreiber : geD.Fn := GeFn.schreiber
def geRuhe : geD.Fn := GeFn.ruhe

/-- The holdings under `lg` (reader side) and under `lt` (writer side). -/
abbrev geLg : List (Res geD) := [Res.held (D := geD) GeLock.lg]
abbrev geLt : List (Res geD) := [Res.held (D := geD) GeLock.lt]

theorem geDarfNotiz : darf geD GeTab.notiz geLg := by
  intro w h
  have e : w = Sum.inl GeLock.lg := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem geDarfTafel : darf geD GeTab.tafel geLt := by
  intro w h
  have e : w = Sum.inl GeLock.lt := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem geLock_ne : (GeLock.lt : GeLock) ≠ GeLock.lg := by decide

theorem geHeld_ne : Res.held (D := geD) GeLock.lt ≠ Res.held GeLock.lg :=
  fun e => geLock_ne (Res.held.inj e)

/-- `haupt` calls `leser`: same writes, same lock. -/
theorem geHpLeser : RufPasst geD (vertragVon geD geHaupt) (geD.signatur geLeser) geLg where
  hw := fun t h => by cases t <;> first | rfl | exact nomatch h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (fun L => by
    cases L
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) geHeld_ne,
        fun h => absurd (List.mem_singleton.mp h) geLock_ne⟩)
  hx := RufPasst.hx_von (fun L => by
    cases L
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) geHeld_ne,
        fun h => absurd (List.mem_singleton.mp h) geLock_ne⟩)

def geIdx {Γ : Ctx} {Λ : List (Res geD)} (t : GeTab) : Expr geD Γ Λ (.index (geD.count t)) :=
  .widen (by show (0 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 1 - 1; decide) (.lit 0)

def geEins {Γ : Ctx} {Λ : List (Res geD)} : Expr geD Γ Λ (.int 0 1) :=
  .widen (by decide) (by decide) (.lit 1)

/-- `notiz[0] := 1` inside `leser`, after the first read. -/
def geNotiz : Stmt geD (vertragVon geD geLeser) false [.int 0 1] geLg geLg :=
  .assignSlot GeTab.notiz () (geIdx GeTab.notiz) geEins rfl geDarfNotiz

/-- `let x = R; notiz[0] := 1; let y = R; return x == y` -/
def geLesBlock : Block geD (vertragVon geD geLeser) false [] geLg geLg :=
  .regRead () rfl (.cons geNotiz (.regRead () rfl
    (.cons (.ret (.val (.eq (.var (.there .here)) (.var .here))) (List.Perm.refl _)) .nil)))

def geRumpfLeser : Endblock geD (vertragVon geD geLeser) false [] geLg :=
  .cons (.ite .tru geLesBlock .nil) (.ret (.val .tru) (List.Perm.refl _))

def geRumpfHaupt : Endblock geD (vertragVon geD geHaupt) false [] geLg :=
  .cons (.call geLeser .nil geHpLeser rfl) (.ret .empty (List.Perm.refl _))

def geRumpfSchreiber : Endblock geD (vertragVon geD geSchreiber) false [] geLt :=
  .cons (.assignSlot GeTab.tafel () (geIdx GeTab.tafel) geEins rfl geDarfTafel)
    (.ret .empty (List.Perm.refl _))

def geRumpfRuhe : Endblock geD (vertragVon geD geRuhe) false [] [] :=
  .ret .empty List.Perm.nil

/-- The program: `ensures result` for `leser`, `true` elsewhere. -/
def geP : Programm geD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | .haupt => .tru
    | .leser => .var .here
    | .schreiber => .tru
    | .ruhe => .tru
  rumpf
    | .haupt => geRumpfHaupt
    | .leser => geRumpfLeser
    | .schreiber => geRumpfSchreiber
    | .ruhe => geRumpfRuhe

def geFs : List geD.Fn := [geHaupt, geLeser, geSchreiber, geRuhe]

theorem geFs_voll : ∀ g : geD.Fn, g ∈ geFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))

theorem geP_fragment : programmImFragmentG geP geFs = true := by decide

/-- The register reads keep `geP` out of the fragment of `ziel_ort_voll`. -/
theorem geP_nicht_fragmentV : programmImFragmentV geP geFs = false := by decide

theorem geP_fuss : fussOrtGB geP geFs = true := by decide


end Gabbro.Grammatik
