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

/-- The device carrier is in the reader's widened footprint (and not in the
    footprint of `ziel_ort_voll`: `leser` never reads `geraet` itself). -/
theorem geLeser_fuss : fussOrteG geP geLeser = [.inl .geraet, .inl .geraet] ∧
    fussOrte geP geLeser = [] := ⟨rfl, rfl⟩

/-! ## 2. Oracle, start, and the user obligations -/

/-- The oracle: the register answers the device's state `geraet[0]`. -/
def geO : Orakel geD where
  wirkt := fun a => nomatch a
  regLies := fun _ σ => (σ.slots GeTab.geraet 0 ()).n
  regSchreib := fun _ _ => ()
  sichtbar := fun g => nomatch g

theorem geO_gut : GutO geO := fun a => nomatch a

/-- **The oracle is register-local**: it reads the device carrier only. -/
theorem geO_lokal : RegLokal geO :=
  ⟨fun _ σ σ' h => by
    show (σ.slots GeTab.geraet 0 ()).n = (σ'.slots GeTab.geraet 0 ()).n
    rw [h.1 GeTab.geraet List.mem_cons_self], fun g => nomatch g⟩

/-- ... and it is not memory-independent: two worlds, two answers. -/
theorem geO_liest_speicher : ∃ σ σ' : World geD, geO.regLies () σ ≠ geO.regLies () σ' :=
  ⟨⟨fun _ _ _ => ⟨0, by decide, by decide⟩, (fun g => nomatch g), []⟩,
   ⟨fun _ _ _ => ⟨1, by decide, by decide⟩, (fun g => nomatch g), []⟩, by
    show (0 : Int) ≠ 1
    decide⟩

def geSp : Speicher geD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread 0 starts in `haupt`, thread 1 in `schreiber`, every other thread
    in `ruhe`. -/
def geInit : Faden → Σ f : geD.Fn, Env geD (geD.params f) :=
  fun t => if t = 0 then ⟨geHaupt, .nil⟩ else if t = 1 then ⟨geSchreiber, .nil⟩
    else ⟨geRuhe, .nil⟩

theorem geP_start : StartGut geP geSp geInit := by
  intro t
  unfold geInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem geInit_haelt (t : Faden) :
    geD.haelt (geInit t).1 = (if t = 0 then [GeLock.lg] else if t = 1 then [GeLock.lt] else []) := by
  unfold geInit
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1, if_pos h1]; rfl
    · rw [if_neg h1, if_neg h1]; rfl

theorem geInit_exklusiv : StartExklusiv (D := geD) geInit := by
  intro t u htu L ht hu
  rw [geInit_haelt] at ht hu
  by_cases h0 : t = 0
  · rw [if_pos h0] at ht
    have hu0 : u ≠ 0 := fun e => htu (h0.trans e.symm)
    rw [if_neg hu0] at hu
    by_cases hu1 : u = 1
    · rw [if_pos hu1] at hu
      have e := (List.mem_singleton.mp ht).symm.trans (List.mem_singleton.mp hu)
      cases e
    · rw [if_neg hu1] at hu
      exact absurd hu List.not_mem_nil
  · rw [if_neg h0] at ht
    by_cases h1 : t = 1
    · rw [if_pos h1] at ht
      have hu1 : u ≠ 1 := fun e => htu (h1.trans e.symm)
      by_cases hu0 : u = 0
      · rw [if_pos hu0] at hu
        have e := (List.mem_singleton.mp ht).symm.trans (List.mem_singleton.mp hu)
        cases e
      · rw [if_neg hu0, if_neg hu1] at hu
        exact absurd hu List.not_mem_nil
    · rw [if_neg h1] at ht
      exact absurd ht List.not_mem_nil

/-- A write to `notiz` leaves the device carrier alone. -/
theorem geNotiz_geraet (σ : World geD) (Λ : List (Res geD)) (k : Int)
    (v : Wert geD (geD.typ GeTab.notiz ())) :
    GleichAuf (geD.rtraeger ()) (σ.schreibSlot GeTab.notiz Λ k () v) σ := by
  refine ⟨fun t ht => ?_, fun g => nomatch g⟩
  have e : t = GeTab.geraet := by
    have := List.mem_singleton.mp ht
    cases this
    rfl
  subst e
  funext k' f'
  simp only [World.schreibSlot, World.merke, World.storeSlot, List.cons_append, List.nil_append, reduceCtorEq,
  ↓reduceDIte]

/-- **What `leser`'s body does for every register-local oracle**: a return
    of `true`, or a hardware outcome. The reader's own write between the
    two reads changes the sequential world; locality gives the same answer. -/
theorem geLeser_lauf (O' : Orakel geD) (hRL : RegLokal O') (passes : Nat)
    (R : ∀ f : geD.Fn, World geD → Env geD (geD.params f) → RufAusgang f) (σ : World geD)
    (ρ : Env geD (geD.params geLeser)) :
    (∃ σ', execEnd O' passes R (geP.rumpf geLeser) σ ρ = .zurueck σ' true) ∨
      ∃ e, execEnd O' passes R (geP.rumpf geLeser) σ ρ = .hardware e := by
  show (∃ σ', execEnd O' passes R geRumpfLeser σ ρ = .zurueck σ' true) ∨
    ∃ e, execEnd O' passes R geRumpfLeser σ ρ = .hardware e
  simp only [geRumpfLeser, geLesBlock, geNotiz, execEnd, execStmt, execBlock]
  generalize hσ1 : σ.lese geLg (Expr.tru : Expr geD [] geLg .bool).orte = σ1
  simp only [eval, wahr?, if_true]
  cases hv : einpassen O'.zeiger (geD.rtyp ()) (O'.regLies () (σ1.fragt (.inr (.inl ())))) with
  | none =>
      right
      exact ⟨_, rfl⟩
  | some v =>
      left
      have hz : geD.rzusage () v = true := rfl
      simp only [hz, if_true]
      generalize hσ3 : ((σ1.fragt (Sum.inr (Sum.inl (() : geD.Reg)))).lese geLg _).schreibSlot GeTab.notiz geLg _ () _ = σ3
      have hloc : O'.regLies () (σ3.fragt (.inr (.inl ()))) = O'.regLies () (σ1.fragt (.inr (.inl ()))) := by
        rw [← hσ3]
        exact hRL.1 () _ _ (geNotiz_geraet ((σ1.fragt (Sum.inr (Sum.inl (() : geD.Reg)))).lese geLg _) geLg _ _)
      rw [hloc, hv]
      simp only [hz, if_true, Ausgang.schrumpf, evalErg, eval]
      exact ⟨_, congrArg (EndAusgang.zurueck _) (decide_eq_true rfl)⟩

/-- The gate of a `requires true` callee lets every call through. -/
theorem geTor (R : ∀ f : geD.Fn, World geD → Env geD (geD.params f) → RufAusgang f) (g : geD.Fn)
    (σ : World geD) (ρ : Env geD (geD.params g)) : torRuf geP R g σ ρ = R g σ ρ := if_pos rfl

theorem geP_koerper_leser : KoerperGutG geP 0 geLeser := by
  intro O' _ hRL R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rcases geLeser_lauf O' hRL 0 R σ ρ with ⟨σ'', h⟩ | ⟨e, h⟩
    · rw [h] at hrun
      cases hrun
      rfl
    · rw [h] at hrun
      cases hrun
  · rcases geLeser_lauf O' hRL 0 (torRuf geP R) σ ρ with ⟨σ'', h⟩ | ⟨e, h⟩
    · rw [h] at hrun
      cases hrun
    · rw [h] at hrun
      cases hrun

theorem geP_koerper_haupt : KoerperGutG geP 0 geHaupt := by
  intro O' _ _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : geP.rumpf geHaupt = geRumpfHaupt := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [execStmt, geTor] at h1
    split at h1
    · cases h1
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h1
      exact hOV _ _ _ _ hR g rfl
    · cases h1
  · simp only [execEnd] at h1
    cases h1

theorem geP_koerper_schreiber : KoerperGutG geP 0 geSchreiber := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : geP.rumpf geSchreiber = geRumpfSchreiber := rfl
  rw [hr] at hrun
  simp only [geRumpfSchreiber, execEnd, execStmt] at hrun
  cases hrun

theorem geP_koerper_ruhe : KoerperGutG geP 0 geRuhe := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : geP.rumpf geRuhe = geRumpfRuhe := rfl
  rw [hr] at hrun
  simp only [geRumpfRuhe, execEnd] at hrun
  cases hrun

theorem geP_koerper : ∀ f, KoerperGutG geP 0 f := by
  intro f
  cases f
  · exact geP_koerper_haupt
  · exact geP_koerper_leser
  · exact geP_koerper_schreiber
  · exact geP_koerper_ruhe

/-- An event of the declaration (a release of `lg`). -/
def geE0 : Ereignis geD := .gibt GeLock.lg

/-- **All premises of `ziel_ort_geraet` hold jointly on `geP`.** -/
theorem geP_vertragAmOrt : ∀ M : RufMaschineG geD,
    RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M → VertragAmOrtG geP M :=
  ziel_ort_geraet geP geO 0 geFs geSp geInit geE0 geO_gut geO_lokal geFs_voll geP_fragment
    geP_fuss geP_koerper geP_start geInit_exklusiv

/-! ## 3. The run -/

def geZ0 : RufFadenG geD :=
  ⟨[], ⟨geHaupt, .nil, geSp.welt [], ⟨false, [], geLg, .nil, .ende geRumpfHaupt⟩⟩,
    startSpur geHaupt, [RufEreignisF.eintritt geHaupt .nil (geSp.welt [])]⟩

def geZ1 : RufFadenG geD :=
  ⟨[], ⟨geSchreiber, .nil, geSp.welt [], ⟨false, [], geLt, .nil, .ende geRumpfSchreiber⟩⟩,
    startSpur geSchreiber, [RufEreignisF.eintritt geSchreiber .nil (geSp.welt [])]⟩

theorem geM0_faden0 : (RufStartG geP geSp geInit).faeden 0 = geZ0 := by rfl

theorem geM0_faden1 : (RufStartG geP geSp geInit).faeden 1 = geZ1 := by rfl

theorem geHgLg {s : List (Ereignis geD)} (h : offen s = [GeLock.lg]) :
    HeldGenau geLg (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) geHeld_ne,
      fun h => absurd (List.mem_singleton.mp h) geLock_ne⟩

end Gabbro.Grammatik
