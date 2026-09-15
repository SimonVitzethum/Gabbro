/-
  File:      Grammatik/ZielOrtGeraetZeuge.lean
  Subject:   WITNESS FOR `ziel_ort_geraet` -- a two-thread program in which one
             thread reads a device register twice inside its lock-guarded
             section while the other thread writes an unrelated table; a
             register-local oracle; every premise jointly; a reached run with
             memory changes between the two reads; the double-read contract
             holds.

  The declaration `geD`: three tables of one slot (`0 .. 1`) --
  `geraet` (the device's state, guarded by `lg`), `notiz` (the reader's
  scratch table, guarded by `lg`), `tafel` (guarded by `lt`); one readable
  register `R` whose device carrier is `geraet`; four functions:

  * `leser` (holds `lg` by signature, writes `notiz`, `ensures result`):
      `if true { let x = R; notiz[0] := 1; let y = R; return x == y };
       return true`
    The two reads are separated by the reader's OWN write to `notiz`: the
    sequential world changes between them, and only register locality (the
    register's device carrier is `geraet`, not `notiz`) makes `x == y`
    provable -- the user obligation `KoerperGutG` uses `RegLokal`.
  * `haupt` (holds `lg`, thread 0's entry): `leser(); return`;
  * `schreiber` (holds `lt`, thread 1's entry): `tafel[0] := 1; return`;
  * `ruhe` (every other thread): `return`.

  The oracle `geO` answers the register from the device carrier:
  `R = geraet[0]` -- register-local, but NOT memory-independent.

  The run: thread 0 calls `leser`, reads `R` (`0`), writes `notiz`; thread 1
  writes `tafel`; thread 0 reads `R` again (`0`) and returns `0 == 0`. Both
  memory changes lie between the two reads.
-/
import Grammatik.ZielOrtGeraet
import Grammatik.ZielOrtVollZeuge
import Grammatik.ZielOrtZeuge

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  hk := ⟨[], List.Perm.refl [], by simp⟩
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
  .weiter (by show (0 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 1 - 1; decide) (.lit 0)

def geEins {Γ : Ctx} {Λ : List (Res geD)} : Expr geD Γ Λ (.int 0 1) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- `notiz[0] := 1` inside `leser`, after the first read. -/
def geNotiz : Stmt geD (vertragVon geD geLeser) false [.int 0 1] geLg geLg :=
  .assignSlot GeTab.notiz () (geIdx GeTab.notiz) geEins rfl geDarfNotiz

/-- `let x = R; notiz[0] := 1; let y = R; return x == y` -/
def geLesBlock : Block geD (vertragVon geD geLeser) false [] geLg geLg :=
  .regLies () rfl (.cons geNotiz (.regLies () rfl
    (.cons (.ret (.wert (.eq (.var (.dort .hier)) (.var .hier))) (List.Perm.refl _)) .nil)))

def geRumpfLeser : Endblock geD (vertragVon geD geLeser) false [] geLg :=
  .cons (.ite .wahr geLesBlock .nil) (.ret (.wert .wahr) (List.Perm.refl _))

def geRumpfHaupt : Endblock geD (vertragVon geD geHaupt) false [] geLg :=
  .cons (.call geLeser .nil geHpLeser rfl) (.ret .keine (List.Perm.refl _))

def geRumpfSchreiber : Endblock geD (vertragVon geD geSchreiber) false [] geLt :=
  .cons (.assignSlot GeTab.tafel () (geIdx GeTab.tafel) geEins rfl geDarfTafel)
    (.ret .keine (List.Perm.refl _))

def geRumpfRuhe : Endblock geD (vertragVon geD geRuhe) false [] [] :=
  .ret .keine List.Perm.nil

/-- The program: `ensures result` for `leser`, `true` elsewhere. -/
def geP : Programm geD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .haupt => .wahr
    | .leser => .var .hier
    | .schreiber => .wahr
    | .ruhe => .wahr
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
  simp [World.schreibSlot, World.merke, World.storeSlot]

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
  generalize hσ1 : σ.lese geLg (Expr.wahr : Expr geD [] geLg .bool).orte = σ1
  simp only [eval, wahr?, if_true]
  cases hv : einpassen O'.zeiger (geD.rtyp ()) (O'.regLies () σ1) with
  | none =>
      right
      exact ⟨_, rfl⟩
  | some v =>
      left
      have hz : geD.rzusage () v = true := rfl
      simp only [hz, if_true]
      generalize hσ3 : (σ1.lese geLg _).schreibSlot GeTab.notiz geLg _ () _ = σ3
      have hloc : O'.regLies () σ3 = O'.regLies () σ1 := by
        rw [← hσ3]
        exact hRL.1 () _ _ (geNotiz_geraet _ _ _ _)
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

theorem geM0_faden0 : (RufStartG geP geSp geInit).faeden 0 = geZ0 := rfl

theorem geM0_faden1 : (RufStartG geP geSp geInit).faeden 1 = geZ1 := rfl

theorem geHgLg {s : List (Ereignis geD)} (h : offen s = [GeLock.lg]) :
    HeldGenau geLg (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) geHeld_ne,
      fun h => absurd (List.mem_singleton.mp h) geLock_ne⟩

theorem geHgLt {s : List (Ereignis geD)} (h : offen s = [GeLock.lt]) :
    HeldGenau geLt (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm geHeld_ne),
      fun h => absurd (List.mem_singleton.mp h) (Ne.symm geLock_ne)⟩
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem geOffen_weltVon (M : RufMaschineG geD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := rfl

theorem geHoff_e {M : RufMaschineG geD} {f : Faden} {z : RufFadenG geD} {x : List geD.Lock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

def geNull : Wert geD (.int 0 1) := ⟨0, by decide, by decide⟩

/-- **The run.** Thread 0 calls `leser`, unfolds its `if`, reads the
    register (`0`), writes `notiz`; thread 1 writes `tafel`; thread 0 reads
    the register again (`0`) and returns `0 == 0`. The log of thread 0 ends
    in the return of `leser`; between the two reads memory changed twice
    (`notiz` and `tafel` from `0` to `1`), the device carrier did not. -/
theorem geLauf : ∃ M : RufMaschineG geD,
    RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M ∧
    (M.speicher.slots GeTab.tafel 0 ()).n = 1 ∧ (M.speicher.slots GeTab.notiz 0 ()).n = 1 ∧
    (M.speicher.slots GeTab.geraet 0 ()).n = 0 ∧
    ∃ (rho : Env geD (geD.params geLeser)) (s0 s1 : World geD),
      RufEreignisF.rueck geLeser rho true s0 s1 ∈ (M.faeden 0).log := by
  have h0 := geM0_faden0
  have hoff0 : offen ((RufStartG geP geSp geInit).faeden 0).spur = [GeLock.lg] := rfl
  -- `haupt` calls `leser`
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := geP) (O := geO) (passes := 0) h0 geLeser .nil geHpLeser
    rfl (.ret .keine (List.Perm.refl _)) .nil rfl (geHgLg hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [GeLock.lg] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen, geOffen_weltVon]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- `leser`: unfold the `if`, take its true branch
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := geP) (O := geO) (passes := 0) e1
    (.ite .wahr geLesBlock .nil) (.ret (.wert .wahr) (List.Perm.refl _)) .nil rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [GeLock.lg] := by
    rw [hZ2.spur, geOffen_weltVon]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  obtain ⟨M3, s3, hZ3⟩ := w_iteWahr (P := geP) (O := geO) (passes := 0) e2 .wahr geLesBlock .nil
    .nil (.ende (.ret (.wert .wahr) (List.Perm.refl _))) .nil rfl rfl
    (geHgLg (geHoff_e e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [GeLock.lg] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, geOffen_weltVon]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  have hsp3 : M3.speicher = geSp := by
    rw [hZ3.2]
    show M2.speicher = geSp
    rw [hZ2.2]
    show M1.speicher = geSp
    rw [hZ1.2]
    rfl
  -- first read: 0
  obtain ⟨M4, s4, hZ4⟩ := w_regLies (P := geP) (O := geO) (passes := 0) e3 () rfl _ _ .nil rfl
    geNull
    (by show einpassen geO.zeiger (.int 0 1) ((M3.speicher.slots GeTab.geraet 0 ()).n) = some geNull
        rw [hsp3]; rfl)
    rfl (geHgLg (geHoff_e e3 hoff3)).heldIn
  have e4 := hZ4.1
  try dsimp only at e4
  have hoff4 : offen (M4.faeden 0).spur = [GeLock.lg] := by
    rw [hZ4.spur, geOffen_weltVon]; exact hoff3
  -- the reader writes `notiz`
  obtain ⟨M5, s5, hZ5⟩ := w_dannBlatt (P := geP) (O := geO) (passes := 0) e4 geNotiz _ _ _
    rfl rfl (geHgLg (geHoff_e e4 hoff4)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have e5 := hZ5.1
  try dsimp only at e5
  have hoff5 : offen (M5.faeden 0).spur = [GeLock.lg] := by
    rw [hZ5.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans
      (((Erw.lese _ _ _).offen).trans ((geOffen_weltVon _ _).trans hoff4))
  -- thread 1 writes `tafel`
  have h51 : M5.faeden 1 = geZ1 := by
    rw [rufSchrittG_fremd s5 1 (by decide), rufSchrittG_fremd s4 1 (by decide),
      rufSchrittG_fremd s3 1 (by decide), rufSchrittG_fremd s2 1 (by decide),
      rufSchrittG_fremd s1 1 (by decide), geM0_faden1]
  obtain ⟨M6, s6, hZ6⟩ := w_blatt (P := geP) (O := geO) (passes := 0) h51
    (.assignSlot GeTab.tafel () (geIdx GeTab.tafel) geEins rfl geDarfTafel)
    (.ret .keine (List.Perm.refl _)) .nil rfl rfl (geHgLt rfl).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have h60 : M6.faeden 0 = M5.faeden 0 := rufSchrittG_fremd s6 0 (by decide)
  have e5' : M6.faeden 0 = _ := h60.trans e5
  have hsp6g : (M6.speicher.slots GeTab.geraet 0 ()).n = 0 := by
    rw [hZ6.2]
    show (M5.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hZ5.2]
    show (M4.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hZ4.2]
    show (M3.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hsp3]
    rfl
  -- second read: 0
  obtain ⟨M7, s7, hZ7⟩ := w_regLies (P := geP) (O := geO) (passes := 0) e5' () rfl _ _ _ rfl geNull
    (by show einpassen geO.zeiger (.int 0 1) ((M6.speicher.slots GeTab.geraet 0 ()).n) = some geNull
        rw [hsp6g]; rfl)
    rfl (geHgLg (geHoff_e e5' (by rw [h60]; exact hoff5))).heldIn
  have e7 := hZ7.1
  try dsimp only at e7
  have hoff7 : offen (M7.faeden 0).spur = [GeLock.lg] := by
    rw [hZ7.spur, geOffen_weltVon, h60]; exact hoff5
  -- return `x == y`, which is `true`
  obtain ⟨M8, s8, hG8⟩ := w_dannRetP (P := geP) (O := geO) (passes := 0) e7 _ _ rfl
    (PopArt.wie rfl) _ (List.Perm.refl _) .nil _ _ rfl (geHgLg (geHoff_e e7 hoff7)).heldIn
  have hr8 : RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M8 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7) s8
  refine ⟨M8, hr8, ?_, ?_, ?_, _, _, _, by rw [hG8.1]; exact List.mem_cons_self⟩
  · rw [hG8.2]
    show (M7.speicher.slots GeTab.tafel 0 ()).n = 1
    rw [hZ7.2]
    show (M6.speicher.slots GeTab.tafel 0 ()).n = 1
    rw [hZ6.2]
    rfl
  · rw [hG8.2]
    show (M7.speicher.slots GeTab.notiz 0 ()).n = 1
    rw [hZ7.2]
    show (M6.speicher.slots GeTab.notiz 0 ()).n = 1
    rw [hZ6.2]
    show (M5.speicher.slots GeTab.notiz 0 ()).n = 1
    rw [hZ5.2]
    rfl
  · rw [hG8.2]
    show (M7.speicher.slots GeTab.geraet 0 ()).n = 0
    rw [hZ7.2]
    exact hsp6g

/-! ## 4. The witness -/

/-- **`ziel_ort_geraet_zeuge`.** On the two-thread program `geP` -- thread
    0 reads the device register `R` twice inside `leser`, which holds the
    device's lock `lg` by signature, with its own write to `notiz` between
    the reads; thread 1 writes the unrelated table `tafel` -- every premise
    of `ziel_ort_geraet` holds jointly: the hardware assumptions `GutO` and
    `RegLokal` for an oracle that answers the register from the device
    carrier (and so depends on memory), the complete member list, the
    widened fragment (outside the fragment of `ziel_ort_voll`), the widened
    footprint check, the user obligation `KoerperGutG` for all four
    functions (the reader's through register locality), the start
    obligation and the exclusive start. On a machine reached by eight steps
    -- with `tafel` and `notiz` changed between the two reads, `geraet`
    unchanged -- the return of `leser` with result `true` is logged, and
    the contracts hold at every logged entry and return. -/
theorem ziel_ort_geraet_zeuge :
    GutO geO ∧ RegLokal geO ∧ (∃ σ σ' : World geD, geO.regLies () σ ≠ geO.regLies () σ') ∧
    (∀ g : geD.Fn, g ∈ geFs) ∧ programmImFragmentG geP geFs = true ∧
    programmImFragmentV geP geFs = false ∧ fussOrtGB geP geFs = true ∧
    (∀ f : geD.Fn, KoerperGutG geP 0 f) ∧ StartGut geP geSp geInit ∧
    StartExklusiv (D := geD) geInit ∧
    ∃ M : RufMaschineG geD, RufErreichbarG geP geO 0 (RufStartG geP geSp geInit) M ∧
      (geSp.slots GeTab.tafel 0 ()).n = 0 ∧ (M.speicher.slots GeTab.tafel 0 ()).n = 1 ∧
      (geSp.slots GeTab.notiz 0 ()).n = 0 ∧ (M.speicher.slots GeTab.notiz 0 ()).n = 1 ∧
      (M.speicher.slots GeTab.geraet 0 ()).n = 0 ∧
      (∃ (rho : Env geD (geD.params geLeser)) (s0 s1 : World geD),
        RufEreignisF.rueck geLeser rho true s0 s1 ∈ (M.faeden 0).log) ∧
      VertragAmOrtG geP M := by
  obtain ⟨M, hr, ht, hn, hg, hlog⟩ := geLauf
  exact ⟨geO_gut, geO_lokal, geO_liest_speicher, geFs_voll, geP_fragment, geP_nicht_fragmentV,
    geP_fuss, geP_koerper, geP_start, geInit_exklusiv, M, hr, rfl, ht, rfl, hn, hg, hlog,
    geP_vertragAmOrt M hr⟩

/-! ## CUTS:

  What is proved: all premises of `ziel_ort_geraet` hold jointly on `geP`
  (`geP_vertragAmOrt` is the instance); the oracle is register-local and
  reads memory (`geO_lokal`, `geO_liest_speicher`); the reader's user
  obligation needs locality, since its own write lies between the two reads
  (`geLeser_lauf`); `geP` is outside the fragment of `ziel_ort_voll`
  (`geP_nicht_fragmentV`); a reached run of eight steps with both memory
  changes between the two reads and the logged return `true`
  (`geLauf`, `ziel_ort_geraet_zeuge`).

  What is NOT covered: no device-driven change of `geraet` in the run (the
  device carrier changes only through a declared write, and the witness has
  none); no `awaits` in the witness (the declaration has no global).
-/

#print axioms Gabbro.Grammatik.geO_lokal
#print axioms Gabbro.Grammatik.geP_koerper
#print axioms Gabbro.Grammatik.geP_vertragAmOrt
#print axioms Gabbro.Grammatik.geLauf
#print axioms Gabbro.Grammatik.ziel_ort_geraet_zeuge

end Gabbro.Grammatik
