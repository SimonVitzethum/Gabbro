module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis

@[expose] public section



namespace Gabbro.Grammatik

/-! ## 1. The declaration and the program -/

/-- The four functions. -/
inductive ZFn where
  | ein
  | lies
  | wrap
  | haupt
  deriving DecidableEq

def zSigEin : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def zSigLies : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def zSigWrap : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def zSigHaupt : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The declaration: `refD`'s table and lock, four functions. -/
def zD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
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
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := ZFn
  sig := fun | .ein => 0 | .lies => 1 | .wrap => 2 | .haupt => 3
  sigNr := fun | 0 => zSigEin | 1 => zSigLies | 2 => zSigWrap | _ => zSigHaupt
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
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def zEin : zD.Fn := ZFn.ein
def zLies : zD.Fn := ZFn.lies
def zWrap : zD.Fn := ZFn.wrap
def zHaupt : zD.Fn := ZFn.haupt

/-- The lock holdings. -/
abbrev zL : List (Res zD) := [Res.held (D := zD) ()]

theorem zDarf : darf zD () zL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- Index `0`. -/
def zIdx {Γ : Ctx} {Λ : List (Res zD)} : Expr zD Γ Λ (.index (zD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The cap `100`. -/
def zHundert {Γ : Ctx} {Λ : List (Res zD)} : Expr zD Γ Λ (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

theorem zEin_ende : (vertragVon zD zEin).ende = zL := by rfl
theorem zLies_ende : (vertragVon zD zLies).ende = zL := by rfl
theorem zEin_start : Signatur.anfang zD (zD.signatur zEin) = zL := by rfl
theorem zLies_start : Signatur.anfang zD (zD.signatur zLies) = zL := by rfl
theorem zWrap_start : Signatur.anfang zD (zD.signatur zWrap) = zL := by rfl
theorem zHaupt_start : Signatur.anfang zD (zD.signatur zHaupt) = [] := by rfl

/-- `einzahlen` ensures the slot did not decrease. -/
def zEnsEin : Expr zD (ErgCtx (zD.params zEin) (zD.erg zEin)) (vertragVon zD zEin).ende .bool :=
  .le (.oldS () () zIdx zDarf) (.slot () () zIdx zDarf)

/-- `lies` ensures `result = konto[0]`. -/
def zEnsLies : Expr zD (ErgCtx (zD.params zLies) (zD.erg zLies)) (vertragVon zD zLies).ende .bool :=
  .eq (.var .here) (.slot () () zIdx zDarf)

/-- `einzahlen`: `konto[0] := 100; return`. -/
def zRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL :=
  .cons (.assignSlot () () zIdx zHundert rfl zDarf) (.ret .empty (by rfl))

/-- `lies`: `let x = konto[0]; return x`. -/
def zRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .bind (.slot () () zIdx zDarf) (.ret (.val (.var .here)) (by rfl))

/-- A call between lock holders: the callee holds exactly the lock. -/
theorem zHp (caller callee : zD.Fn) (hw : ∀ t, (zD.signatur callee).schreibt t = true →
    (vertragVon zD caller).schreibt t = true)
    (hh : (zD.signatur callee).haelt = [()]) (hk : (zD.signatur callee).konsumiert = []) :
    RufPasst zD (vertragVon zD caller) (zD.signatur callee) zL where
  hw := hw
  hg := fun g => nomatch g
  ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _
    (OwnerFlow.empty_of_empty (zD.signatur callee).owner)
  hb := fun c hc => by revert hc; cases caller <;> intro hc <;> cases hc
  hk := by
    unfold Signatur.inputMarks
    rw [hk, OwnerFlow.empty_of_empty (zD.signatur callee).owner]
    exact ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (by
    intro L
    cases L
    rw [hh]
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)
  hx := RufPasst.hx_von (by
    intro L
    cases L
    rw [hh]
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)

theorem zHpLies : RufPasst zD (vertragVon zD zWrap) (zD.signatur zLies) zL :=
  zHp zWrap zLies (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

theorem zHpEin : RufPasst zD (vertragVon zD zWrap) (zD.signatur zEin) zL :=
  zHp zWrap zEin (fun t _ => by cases t; rfl) rfl rfl

theorem zHpWrap : RufPasst zD (vertragVon zD zHaupt) (zD.signatur zWrap) zL :=
  zHp zHaupt zWrap (fun t _ => by cases t; rfl) rfl rfl

/-- `wrap`: `lies(); einzahlen(); return`. -/
def zRumpfWrap : Endblock zD (vertragVon zD zWrap) false [] zL :=
  .cons (.call zLies .nil zHpLies rfl) (.cons (.call zEin .nil zHpEin rfl) (.ret .empty (by rfl)))

/-- The `locks` body of `haupt`: `wrap()`. -/
def zLocksBody : Block zD (vertragVon zD zHaupt) false [] zL zL :=
  .cons (.call zWrap .nil zHpWrap rfl) .nil

/-- `haupt`: `locks { wrap() }; return`. -/
def zRumpfHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] :=
  .cons (.locks () (fun _ h => nomatch h) zLocksBody) (.ret .empty List.Perm.nil)

/-- The witness program. -/
def zP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | .ein => zEnsEin
    | .lies => zEnsLies
    | .wrap => .tru
    | .haupt => .tru
  rumpf
    | .ein => zRumpfEin
    | .lies => zRumpfLies
    | .wrap => zRumpfWrap
    | .haupt => zRumpfHaupt

/-- The complete member list. -/
def zFs : List zD.Fn := [zEin, zLies, zWrap, zHaupt]

theorem zFs_voll : ∀ g : zD.Fn, g ∈ zFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))

theorem zP_fragment : programmImFragment zP zFs = true := by decide

theorem zP_fuss : fussOrtB zP zFs = true := by decide

/-! ## 2. Oracle, start, and the user obligations -/

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def zO : Orakel zD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem zO_gut : GutO zO := by
  intro a
  exact nomatch a

/-- The start memory: `konto` all zero. -/
def zSp : Speicher zD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Every thread starts in `haupt`. -/
def zInit : Faden → Σ f : zD.Fn, Env zD (zD.params f) :=
  fun _ => ⟨zHaupt, .nil⟩

theorem zP_start : StartGut zP zSp zInit := fun _ => rfl

/-- `haupt` holds no lock: the start is exclusive. -/
theorem zInit_exklusiv : StartExklusiv (D := zD) zInit :=
  fun _ _ _ _ h => nomatch h

theorem zP_fragmentF : ∀ f, (zP.rumpf f).kOk = true :=
  fun f => (List.all_eq_true.mp zP_fragment) f (zFs_voll f)

/-- An `end` block that starts with a statement ends in a logic outcome only
    through that statement or its rest. -/
theorem execEnd_cons_logik {V : Vertrag zD} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res zD)}
    (O : Orakel zD) (passes : Nat)
    (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (s : Stmt zD V l Γ Λ Λ') (rest : Endblock zD V l Γ Λ') (σ : World zD) (ρ : Env zD Γ)
    (e : Logik zD) (h : execEnd O passes R (.cons s rest) σ ρ = .logik e) :
    execStmt O passes R s σ ρ = .logik e ∨
      ∃ σ' ρ', execStmt O passes R s σ ρ = .ok σ' ρ' ∧ execEnd O passes R rest σ' ρ' = .logik e := by
  simp only [execEnd] at h
  revert h
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => intro h; exact Or.inr ⟨σ', ρ', rfl, h⟩
  | logik e' => intro h; cases h; exact Or.inl rfl
  | _ => intro h; cases h

/-- A call of a function with `requires true`, through the gate, never
    fails the gate: its logic outcome is the handler's, and a handler that
    never blames a caller answers no `vorbedingung`. -/
theorem call_tor_ok {V : Vertrag zD} {l : Bool} {Γ : Ctx} {Λ : List (Res zD)}
    (O : Orakel zD) (passes : Nat)
    (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : zD.Fn) (args : Args zD Γ Λ (zD.params g)) (hp : RufPasst zD V (zD.signatur g) Λ)
    (hr : zD.gruende g = 0) (σ : World zD) (ρ : Env zD Γ) (g' : zD.Fn) :
    execStmt O passes (torRuf zP R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf zP R g σ1 ρ1 = R g σ1 ρ1 := fun _ _ => if_pos rfl
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

theorem mapWelt_logik {V : Vertrag zD} {l : Bool} {Γ : Ctx} {o : Ausgang V l Γ}
    {f : World zD → World zD} {e : Logik zD} (h : o.mapWelt f = .logik e) : o = .logik e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem execBlock_eins_logik {V : Vertrag zD} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res zD)}
    (O : Orakel zD) (passes : Nat)
    (R : ∀ f : zD.Fn, World zD → Env zD (zD.params f) → RufAusgang f)
    (s : Stmt zD V l Γ Λ Λ') (σ : World zD) (ρ : Env zD Γ) {e : Logik zD}
    (h : execBlock O passes R (.cons s .nil) σ ρ = .logik e) :
    execStmt O passes R s σ ρ = .logik e := by
  simp only [execBlock] at h
  revert h
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => intro h; simp only [reduceCtorEq] at h
  | _ => intro h; exact h

theorem zP_koerper_lies : KoerperGut zP zO 0 zLies := by
  intro R _ _ σ ρ _
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    have hr : zP.rumpf zLies = zRumpfLies := rfl
    rw [hr] at hrun
    simp only [zRumpfLies, execEnd, EndAusgang.schrumpf] at hrun
    cases hrun
    exact (decide_eq_true_eq).mpr rfl
  · intro g hrun
    have hr : zP.rumpf zLies = zRumpfLies := rfl
    rw [hr] at hrun
    simp only [zRumpfLies, execEnd, EndAusgang.schrumpf] at hrun
    cases hrun

theorem zP_koerper_ein : KoerperGut zP zO 0 zEin := by
  intro R _ _ σ ρ _
  refine ⟨?_, ?_⟩
  · intro σ' v hrun
    have hr : zP.rumpf zEin = zRumpfEin := rfl
    rw [hr] at hrun
    simp only [zRumpfEin, execEnd, execStmt] at hrun
    cases hrun
    show decide ((σ.slots () 0 ()).n ≤ 100) = true
    exact decide_eq_true_eq.mpr (σ.slots () 0 ()).le_hi
  · intro g hrun
    have hr : zP.rumpf zEin = zRumpfEin := rfl
    rw [hr] at hrun
    simp only [zRumpfEin, execEnd, execStmt] at hrun
    cases hrun

theorem zP_koerper_wrap : KoerperGut zP zO 0 zWrap := by
  intro R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : zP.rumpf zWrap = zRumpfWrap := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logik _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · exact call_tor_ok _ _ R hOV _ _ _ _ _ _ _ h1
  · rcases execEnd_cons_logik _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
    · exact call_tor_ok _ _ R hOV _ _ _ _ _ _ _ h2
    · simp only [execEnd] at h2
      cases h2

theorem zP_koerper_haupt : KoerperGut zP zO 0 zHaupt := by
  intro R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : zP.rumpf zHaupt = zRumpfHaupt := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logik _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [execStmt] at h1
    generalize hb : execBlock zO 0 (torRuf zP R) zLocksBody (σ.nimmt ()) ρ = outcome
    erw [hb] at h1
    cases outcome <;> simp only [Ausgang.mapWelt] at h1 <;> try cases h1
    exact call_tor_ok _ _ R hOV _ _ _ _ _ _ _ (execBlock_eins_logik _ _ _ _ _ _ hb)
  · simp only [execEnd] at h1
    cases h1

theorem zP_koerper : ∀ f, KoerperGut zP zO 0 f := by
  intro f
  cases f
  · exact zP_koerper_ein
  · exact zP_koerper_lies
  · exact zP_koerper_wrap
  · exact zP_koerper_haupt

/-- An event of the declaration (a release of the lock). -/
def zE0 : Ereignis zD := .gibt ()

/-- **All premises of `ziel_ort` hold jointly on `zP`, and so does its
    conclusion.** -/
theorem zP_vertragAmOrt : ∀ M : RufMaschineG zD,
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M → VertragAmOrtG zP M :=
  ziel_ort zP zO 0 zFs zSp zInit zE0 zO_gut zFs_voll zP_fragment zP_fuss zP_koerper zP_start
    zInit_exklusiv

/-! ## 3. The runs -/

/-- The start thread state (every thread): `haupt`, no lock held. -/
def zZ0 : RufFadenG zD :=
  ⟨[], ⟨zHaupt, .nil, zSp.welt [], ⟨false, [], [], .nil, .ende zRumpfHaupt⟩⟩, [],
    [RufEreignisF.eintritt zHaupt .nil (zSp.welt [])]⟩

theorem zM0_faden (t : Faden) : (RufStartG zP zSp zInit).faeden t = zZ0 := by rfl

theorem hgL {s : List (Ereignis zD)} (h : offen s = [()]) : HeldGenau zL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem hg0 {s : List (Ereignis zD)} (h : offen s = []) :
    HeldGenau ([] : List (Res zD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem offen_weltVon (M : RufMaschineG zD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := by rfl

theorem hoff_z {M : RufMaschineG zD} {f : Faden} {stapel : List (RufRahmenG zD)} {fn : zD.Fn}
    {rho : Env zD (zD.params fn)} {s0 : World zD} {log : List (RufEreignisF zD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res zD)} {ρ : Env zD Γ} {r : GRest zD (vertragVon zD fn) l Γ Λ}
    {σ : World zD} {x : List zD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem hoff_g {M : RufMaschineG zD} {f : Faden} {caller : RufRahmenG zD}
    {rst : List (RufRahmenG zD)} {fn : zD.Fn} {rho : Env zD (zD.params fn)} {s0 : World zD}
    {log : List (RufEreignisF zD)} {v : ErgVal zD (zD.erg fn)} {σ : World zD} {x : List zD.Lock}
    (h : GepopptG M f caller rst fn rho s0 log v σ) (ho : offen (M.faeden f).spur = x) :
    offen σ.spur = x := by
  rw [h.1] at ho; exact ho

/-- A slot assignment, unfolded once (stated for variables, so the unfolding
    is cheap wherever it is used). -/
theorem execStmt_assignSlot {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true)
    (hL : darf D t Λ) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e.orte)) e (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := by rfl

/-- The `locks` statement of `haupt`. -/
def zLocks : Stmt zD (vertragVon zD zHaupt) false [] [] [] :=
  .locks () (fun _ h => nomatch h) zLocksBody

/-- The rest of `haupt` after its `locks`. -/
def zHauptRet : Endblock zD (vertragVon zD zHaupt) false [] [] := .ret .empty List.Perm.nil

end Gabbro.Grammatik
