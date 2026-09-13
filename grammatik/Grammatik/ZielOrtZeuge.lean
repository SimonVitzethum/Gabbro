/-
  File:      Grammatik/ZielOrtZeuge.lean
  Subject:   WITNESSES FOR `ziel_ort` -- the reference account with a
             lock-free thread entry: every premise jointly, a reached run
             that writes, calls and returns, and a run in which ANOTHER
             thread writes the contract's carrier under the common lock.

  The declaration `zD` is the reference declaration `refD` (one table
  `konto`, two slots of `.int 0 100`, guarded by the one lock) with four
  functions:

  * `einzahlen` (holds the lock): `konto[0] := 100; return`,
    `ensures old(konto[0]) ≤ konto[0]`;
  * `lies` (holds the lock): `let x = konto[0]; return x`,
    `ensures result = konto[0]`;
  * `wrap` (holds the lock, contract `true`): `lies(); einzahlen(); return`;
  * `haupt` (holds NO lock, contract `true`): `locks { wrap() }; return` --
    the entry of every thread.

  Why not `refP` itself: every thread of G starts in some function, and
  both functions of `refD` hold the lock by signature, so no start
  assignment of `refD` is exclusive (`StartExklusiv`) -- a thread entry that
  holds no lock is needed. And why the wrapper: `haupt` takes the lock in a
  `locks` block, so it may not rely on contracts over `konto` (the footprint
  check: callee contract carriers must be guarded by a SIGNATURE lock of the
  caller); `wrap` holds the lock by signature and calls the two functions
  whose contracts mention `konto`. (Also `refP`'s `einzahlen`, "write, then
  call `lies`", is not sequentially correct: `ensures lies` does not promise
  to leave `konto` alone, so a contract-respecting handler may answer with
  `konto[0] = 0`; `einzahlen` here writes last.)
-/
import Grammatik.ZielOrtBeweis

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
  .weiter (by decide) (by decide) (.lit 0)

/-- The cap `100`. -/
def zHundert {Γ : Ctx} {Λ : List (Res zD)} : Expr zD Γ Λ (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 100)

theorem zEin_ende : (vertragVon zD zEin).ende = zL := rfl
theorem zLies_ende : (vertragVon zD zLies).ende = zL := rfl
theorem zEin_start : Signatur.anfang zD (zD.signatur zEin) = zL := rfl
theorem zLies_start : Signatur.anfang zD (zD.signatur zLies) = zL := rfl
theorem zWrap_start : Signatur.anfang zD (zD.signatur zWrap) = zL := rfl
theorem zHaupt_start : Signatur.anfang zD (zD.signatur zHaupt) = [] := rfl

/-- `einzahlen` ensures the slot did not decrease. -/
def zEnsEin : Expr zD (ErgCtx (zD.params zEin) (zD.erg zEin)) (vertragVon zD zEin).ende .bool :=
  .le (.altSlot () () zIdx zDarf) (.slot () () zIdx zDarf)

/-- `lies` ensures `result = konto[0]`. -/
def zEnsLies : Expr zD (ErgCtx (zD.params zLies) (zD.erg zLies)) (vertragVon zD zLies).ende .bool :=
  .eq (.var .hier) (.slot () () zIdx zDarf)

/-- `einzahlen`: `konto[0] := 100; return`. -/
def zRumpfEin : Endblock zD (vertragVon zD zEin) false [] zL :=
  .cons (.assignSlot () () zIdx zHundert rfl zDarf) (.ret .keine (by rfl))

/-- `lies`: `let x = konto[0]; return x`. -/
def zRumpfLies : Endblock zD (vertragVon zD zLies) false [] zL :=
  .bind (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl))

/-- A call between lock holders: the callee holds exactly the lock. -/
theorem zHp (caller callee : zD.Fn) (hw : ∀ t, (zD.signatur callee).schreibt t = true →
    (vertragVon zD caller).schreibt t = true)
    (hh : (zD.signatur callee).haelt = [()]) (hk : (zD.signatur callee).konsumiert = []) :
    RufPasst zD (vertragVon zD caller) (zD.signatur callee) zL where
  hw := hw
  hg := fun g => nomatch g
  hb := fun c hc => by revert hc; cases caller <;> intro hc <;> cases hc
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp⟩
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
  .cons (.call zLies .nil zHpLies rfl) (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl)))

/-- The `locks` body of `haupt`: `wrap()`. -/
def zLocksBody : Block zD (vertragVon zD zHaupt) false [] zL zL :=
  .cons (.call zWrap .nil zHpWrap rfl) .nil

/-- `haupt`: `locks { wrap() }; return`. -/
def zRumpfHaupt : Endblock zD (vertragVon zD zHaupt) false [] [] :=
  .cons (.locks () (fun _ h => nomatch h) zLocksBody) (.ret .keine List.Perm.nil)

/-- The witness program. -/
def zP : Programm zD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .ein => zEnsEin
    | .lies => zEnsLies
    | .wrap => .wahr
    | .haupt => .wahr
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
  | grund σ' r => exact (Fin.cast hr r).elim0
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
  | ok σ' ρ' => intro h; simp [execBlock] at h
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
    exact call_tor_ok _ _ R hOV _ _ _ _ _ _ _ (execBlock_eins_logik _ _ _ _ _ _ (mapWelt_logik h1))
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

theorem zM0_faden (t : Faden) : (RufStartG zP zSp zInit).faeden t = zZ0 := rfl

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
    offen (M.weltVon t).spur = offen (M.faeden t).spur := rfl

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
        (eval (σ.lese Λ (i.orte ++ e.orte)) e (σ.lese Λ (i.orte ++ e.orte)) ρ)) ρ := rfl

/-- The `locks` statement of `haupt`. -/
def zLocks : Stmt zD (vertragVon zD zHaupt) false [] [] [] :=
  .locks () (fun _ h => nomatch h) zLocksBody

/-- The rest of `haupt` after its `locks`. -/
def zHauptRet : Endblock zD (vertragVon zD zHaupt) false [] [] := .ret .keine List.Perm.nil

/-- **The run.** Eighteen steps of the repaired G from the start machine of
    `zP` (every thread in `haupt`, `konto` all zero): thread 1 takes the lock,
    enters `wrap`, calls `lies` (reads 0) and `einzahlen` (writes 100),
    returns to `haupt` and releases the lock (twelve steps, the machine `M9`
    after the ninth: the write done, both calls logged and returned); then
    thread 0 takes the lock, enters `wrap` and `lies`, reads `konto[0]` --
    the 100 thread 1 wrote -- and returns it. -/
theorem zLauf : ∃ M9 M17 M18 : RufMaschineG zD,
    RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 ∧
    RufErreichbarG zP zO 0 M9 M17 ∧ RufErreichbarG zP zO 0 M17 M18 ∧
    -- after the ninth step: memory moved, `lies` and `einzahlen` called and returned
    (M9.speicher.slots () 0 ()).n = 100 ∧
    (∃ rho s0, RufEreignisF.eintritt zEin rho s0 ∈ (M9.faeden 1).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck zEin rho v s0 s1 ∈ (M9.faeden 1).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck zLies rho v s0 s1 ∈ (M9.faeden 1).log) ∧
    -- thread 0 inside `lies` holds the lock, thread 1 does not
    (M17.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M17.faeden 0).spur ∧
    (() : zD.Lock) ∉ offen (M17.faeden 1).spur ∧
    -- thread 0's `lies` returns 100, the value thread 1 wrote under the lock
    (∃ (rho : Env zD (zD.params zLies)) (v : ErgVal zD (zD.erg zLies)) (s0 s1 : World zD),
      RufEreignisF.rueck zLies rho v s0 s1 ∈ (M18.faeden 0).log ∧
      (show Zahl 0 100 from v).n = 100 ∧ (s1.slots () 0 ()).n = 100) ∧
    -- thread 0 has not moved before thread 1's write
    M9.faeden 0 = (RufStartG zP zSp zInit).faeden 0 ∧
    -- thread 0's head frame names the lock statically
    Res.held (() : zD.Lock) ∈ (M17.faeden 0).kopf.rest.2.2.1 := by
  have h01 := zM0_faden (1 : Faden)
  have hoff0 : offen ((RufStartG zP zSp zInit).faeden 1).spur = [] := rfl
  -- thread 1: `endeEntf`, `locks`, call `wrap`, call `lies`, bind
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h01 zLocks zHauptRet
    .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ1.1 ()
    _ _ _ _ .nil rfl (hg0 hoff0)
    (fun u hu h => by rw [rufSchrittG_fremd s1 u hu, zM0_faden] at h; exact List.not_mem_nil h)
  have hoff2 : offen (M2.faeden 1).spur = [()] := by
    rw [hZ2.spur]
    show offen (Ereignis.nimmt () (offen (M1.weltVon 1).spur) :: (M1.weltVon 1).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ1.spur]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ2.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 1).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ3.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl))) .nil rfl
    (hgL (hoff_z hZ3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 1).spur = [()] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff3
  obtain ⟨M5, s5, hZ5⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ4.1
    (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 1).spur = [()] := by
    rw [hZ5.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff4
  -- return from `lies`, call `einzahlen`, write, return
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ5.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 1).spur = [()] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  obtain ⟨M7, s7, hZ7⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hG6.1 zEin .nil zHpEin rfl
    (.ret .keine (by rfl)) .nil rfl
    (hgL (hoff_g hG6 hoff6)).heldIn
  have hoff7 : offen (M7.faeden 1).spur = [()] := by
    rw [hZ7.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff6
  obtain ⟨M8, s8, hZ8⟩ := w_blatt (P := zP) (O := zO) (passes := 0) hZ7.1
    _ _ _ rfl rfl
    (hgL (hoff_z hZ7 hoff7)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff8 : offen (M8.faeden 1).spur = [()] := by
    rw [hZ8.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff7
  obtain ⟨M9, s9, hG9⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ8.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_z hZ8 hoff8)).heldIn
  have hoff9 : offen (M9.faeden 1).spur = [()] := by
    rw [hG9.1]
    exact ((Erw.lese _ _ _).offen).trans hoff8
  have hr9 : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7) s8) s9
  have hsp9 : (M9.speicher.slots () 0 ()).n = 100 := by
    rw [hG9.2]
    show (M8.speicher.slots () 0 ()).n = 100
    rw [hZ8.2]
    rfl
  -- return from `wrap`, leave the `locks`
  obtain ⟨M10, s10, hG10⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hG9.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (hgL (hoff_g hG9 hoff9)).heldIn
  have hoff10 : offen (M10.faeden 1).spur = [()] := by
    rw [hG10.1]
    exact ((Erw.lese _ _ _).offen).trans hoff9
  obtain ⟨M11, s11, hZ11⟩ := w_dannLeer (P := zP) (O := zO) (passes := 0) hG10.1 _ .nil rfl
  obtain ⟨M12, s12, hZ12⟩ := w_freiGib (P := zP) (O := zO) (passes := 0) hZ11.1 () _ .nil rfl
  have hoff12 : offen (M12.faeden 1).spur = [] := by
    rw [hZ12.spur]
    show (offen (M11.weltVon 1).spur).erase () = []
    rw [offen_weltVon, hZ11.spur, offen_weltVon, hoff10]
    rfl
  -- thread 0: the same prefix, reading what thread 1 wrote
  have hfremd12 : ∀ u, u ≠ 1 → M12.faeden u = zZ0 := by
    intro u hu
    rw [rufSchrittG_fremd s12 u hu, rufSchrittG_fremd s11 u hu, rufSchrittG_fremd s10 u hu,
      rufSchrittG_fremd s9 u hu, rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu,
      rufSchrittG_fremd s6 u hu, rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu,
      rufSchrittG_fremd s3 u hu, rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu, zM0_faden]
  have h00 : M12.faeden 0 = zZ0 := hfremd12 0 (by decide)
  obtain ⟨M13, s13, hZ13⟩ := w_endeEntf (P := zP) (O := zO) (passes := 0) h00 zLocks zHauptRet
    .nil rfl rfl
  have hfrei13 : RufFreiG M13 0 () := by
    intro u hu
    rw [rufSchrittG_fremd s13 u hu]
    by_cases hu1 : u = 1
    · subst hu1; rw [hoff12]; exact List.not_mem_nil
    · rw [hfremd12 u hu1]; exact List.not_mem_nil
  obtain ⟨M14, s14, hZ14⟩ := w_locks (P := zP) (O := zO) (passes := 0) hZ13.1 ()
    _ _ _ _ .nil rfl (hg0 (by show offen (M12.faeden 0).spur = []; rw [h00]; rfl)) hfrei13
  have hoff14 : offen (M14.faeden 0).spur = [()] := by
    rw [hZ14.spur]
    show offen (Ereignis.nimmt () (offen (M13.weltVon 0).spur) :: (M13.weltVon 0).spur) = [()]
    simp only [offen]
    rw [offen_weltVon, hZ13.spur]
    show () :: offen (M12.faeden 0).spur = [()]
    rw [h00]
    rfl
  obtain ⟨M15, s15, hZ15⟩ := w_rufDann (P := zP) (O := zO) (passes := 0) hZ14.1 zWrap .nil zHpWrap
    rfl _ _ .nil rfl
    (hgL (hoff_z hZ14 hoff14)).heldIn
  have hoff15 : offen (M15.faeden 0).spur = [()] := by
    rw [hZ15.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff14
  obtain ⟨M16, s16, hZ16⟩ := w_rufEnde (P := zP) (O := zO) (passes := 0) hZ15.1 zLies .nil zHpLies
    rfl (.cons (.call zEin .nil zHpEin rfl) (.ret .keine (by rfl))) .nil rfl
    (hgL (hoff_z hZ15 hoff15)).heldIn
  have hoff16 : offen (M16.faeden 0).spur = [()] := by
    rw [hZ16.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff15
  obtain ⟨M17, s17, hZ17⟩ := w_endeBind (P := zP) (O := zO) (passes := 0) hZ16.1
    (.slot () () zIdx zDarf) (.ret (.wert (.var .hier)) (by rfl)) .nil rfl
    (hgL (hoff_z hZ16 hoff16)).heldIn
  have hoff17 : offen (M17.faeden 0).spur = [()] := by
    rw [hZ17.spur, (Erw.lese _ _ _).offen, offen_weltVon]; exact hoff16
  obtain ⟨M18, s18, hG18⟩ := w_rueckP (P := zP) (O := zO) (passes := 0) hZ17.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl
    (hgL (hoff_z hZ17 hoff17)).heldIn
  have e9 : M9.speicher = M8.speicher := by rw [hG9.2]; rfl
  have e10 : M10.speicher = M9.speicher := by rw [hG10.2]; rfl
  have e11 : M11.speicher = M10.speicher := by rw [hZ11.2]; rfl
  have e12 : M12.speicher = M11.speicher := by rw [hZ12.2]; rfl
  have e13 : M13.speicher = M12.speicher := by rw [hZ13.2]; rfl
  have e14 : M14.speicher = M13.speicher := by rw [hZ14.2]; rfl
  have e15 : M15.speicher = M14.speicher := by rw [hZ15.2]; rfl
  have e16 : M16.speicher = M15.speicher := by rw [hZ16.2]; rfl
  have e17 : M17.speicher = M16.speicher := by rw [hZ17.2]; rfl
  have hsp16 : M16.speicher = M8.speicher := by
    rw [e16, e15, e14, e13, e12, e11, e10, e9]
  have h90 : M9.faeden 0 = (RufStartG zP zSp zInit).faeden 0 := by
    rw [rufSchrittG_fremd s9 0 (by decide), rufSchrittG_fremd s8 0 (by decide),
      rufSchrittG_fremd s7 0 (by decide), rufSchrittG_fremd s6 0 (by decide),
      rufSchrittG_fremd s5 0 (by decide), rufSchrittG_fremd s4 0 (by decide),
      rufSchrittG_fremd s3 0 (by decide), rufSchrittG_fremd s2 0 (by decide),
      rufSchrittG_fremd s1 0 (by decide)]
  have h17_1 : M17.faeden 1 = M12.faeden 1 := by
    rw [rufSchrittG_fremd s17 1 (by decide), rufSchrittG_fremd s16 1 (by decide),
      rufSchrittG_fremd s15 1 (by decide), rufSchrittG_fremd s14 1 (by decide),
      rufSchrittG_fremd s13 1 (by decide)]
  refine ⟨M9, M17, M18, hr9,
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ .start s10) s11) s12) s13) s14) s15) s16) s17,
    .schritt _ _ _ .start s18, hsp9, ?_, ?_, ?_, by rw [hZ17.1], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG9.1]
    exact ⟨_, _, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · rw [hG9.1]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  · rw [hG9.1]
    exact ⟨_, _, _, _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · rw [hoff17]; exact List.mem_cons_self
  · rw [h17_1, hoff12]; exact List.not_mem_nil
  · refine ⟨_, _, _, _, by rw [hG18.1]; exact List.mem_cons_self, ?_, ?_⟩
    · show (M16.speicher.slots () 0 ()).n = 100
      rw [hsp16, hZ8.2]
      rfl
    · show (M17.speicher.slots () 0 ()).n = 100
      rw [e17, hsp16, hZ8.2]
      rfl
  · exact h90
  · rw [hZ17.1]; exact List.mem_cons_self


/-! ## 4. The witnesses -/

/-- **`ziel_ort_zeuge`.** Every premise of `ziel_ort` holds jointly on the
    non-degenerate program `zP` (user obligations for all four functions,
    start, exclusive start, good oracle, the two decidable checks on the
    complete function list), and on a reached run of nine steps, in which
    memory moved from `0` to `100` (thread 1's `einzahlen` wrote `konto[0]`
    under its signature lock) and `einzahlen` and `lies` were entered and
    returned, the contract holds at every logged entry and return. -/
theorem ziel_ort_zeuge :
    GutO zO ∧ (∀ g : zD.Fn, g ∈ zFs) ∧ programmImFragment zP zFs = true ∧
    fussOrtB zP zFs = true ∧ (∀ f : zD.Fn, KoerperGut zP zO 0 f) ∧ StartGut zP zSp zInit ∧
    StartExklusiv (D := zD) zInit ∧
    ∃ M : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
      (zSp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ rho s0, RufEreignisF.eintritt zEin rho s0 ∈ (M.faeden 1).log) ∧
      (∃ rho v s0 s1, RufEreignisF.rueck zEin rho v s0 s1 ∈ (M.faeden 1).log) ∧
      (∃ rho v s0 s1, RufEreignisF.rueck zLies rho v s0 s1 ∈ (M.faeden 1).log) ∧
      VertragAmOrtG zP M := by
  obtain ⟨M9, _, _, h9, _, _, hsp, he, hr, hl, _⟩ := zLauf
  exact ⟨zO_gut, zFs_voll, zP_fragment, zP_fuss, zP_koerper, zP_start, zInit_exklusiv,
    M9, h9, rfl, hsp, he, hr, hl, zP_vertragAmOrt M9 h9⟩

/-- **The interference witness.** Thread 1 writes `konto[0] := 100`
    (the carrier of `lies`' contract) in `einzahlen`, which holds the
    common lock by signature, while thread 0 has logged nothing but its own
    start; afterwards thread 0 enters `lies` and holds the lock
    throughout (at the step before its return it holds it and thread 1 does
    not). Thread 0's `lies` returns `100` -- a value no step of its own
    wrote -- in a return world whose `konto[0]` is `100`, and its contract
    `result = konto[0]` holds there: at the logged return, by `ziel_ort`. -/
theorem ziel_ort_zeuge_interferenz :
    ∃ M9 M17 M18 : RufMaschineG zD,
      RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M9 ∧
      RufErreichbarG zP zO 0 M9 M17 ∧ RufErreichbarG zP zO 0 M17 M18 ∧
      (zSp.slots () 0 ()).n = 0 ∧ (M9.speicher.slots () 0 ()).n = 100 ∧
      (∃ rho v s0 s1, RufEreignisF.rueck zEin rho v s0 s1 ∈ (M9.faeden 1).log) ∧
      (M9.faeden 0).log = [RufEreignisF.eintritt zHaupt .nil (zSp.welt [])] ∧
      (M17.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M17.faeden 0).spur ∧
      (() : zD.Lock) ∉ offen (M17.faeden 1).spur ∧
      (∃ (rho : Env zD (zD.params zLies)) (v : ErgVal zD (zD.erg zLies)) (s0 s1 : World zD),
        RufEreignisF.rueck zLies rho v s0 s1 ∈ (M18.faeden 0).log ∧
        (show Zahl 0 100 from v).n = 100 ∧ (s1.slots () 0 ()).n = 100 ∧
        EnsAmRueck zP zLies s0 s1 rho v) := by
  obtain ⟨M9, M17, M18, h9, h17, h18, hsp, _, hr, _, hf, hin, hout,
    ⟨rho, v, s0, s1, hm, hv, hs⟩, h90, _⟩ := zLauf
  have h18' : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M18 :=
    rufErreichbarG_trans (rufErreichbarG_trans h9 h17) h18
  exact ⟨M9, M17, M18, h9, h17, h18, rfl, hsp, hr, by rw [h90]; rfl, hf, hin, hout, rho, v, s0, s1,
    hm, hv, hs, (zP_vertragAmOrt M18 h18' 0 _ hm).2 _ _ _ _ _ rfl⟩

/-- **`rufG_haelt_statisch_zeuge`** (and the signature companion): on a
    reached machine of `zP` with two running threads, thread 0's head
    frame (in `lies`) names the lock statically and by signature, and the
    theorems give that thread 0 holds it -- while thread 1, whose `locks`
    block has ended, does not. -/
theorem rufG_haelt_statisch_zeuge :
    ∃ M : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
      Res.held (() : zD.Lock) ∈ (M.faeden 0).kopf.rest.2.2.1 ∧
      (() : zD.Lock) ∈ zD.haelt (M.faeden 0).kopf.f ∧
      (() : zD.Lock) ∈ offen (M.faeden 0).spur ∧ (() : zD.Lock) ∉ offen (M.faeden 1).spur := by
  obtain ⟨M9, M17, _, h9, h17, _, _, _, _, _, hf, _, hout, _, _, hheld⟩ := zLauf
  have h : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M17 := rufErreichbarG_trans h9 h17
  have hsig : (() : zD.Lock) ∈ zD.haelt (M17.faeden 0).kopf.f := by
    rw [hf]; exact List.mem_cons_self
  exact ⟨M17, h, hheld, hsig,
    rufG_haelt_statisch zO_gut zSp zInit h 0 _ List.mem_cons_self () hheld, hout⟩

theorem rufG_haelt_signatur_zeuge :
    ∃ M : RufMaschineG zD, RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M ∧
      (M.faeden 0).kopf.f = zLies ∧ (() : zD.Lock) ∈ offen (M.faeden 0).spur ∧
      (() : zD.Lock) ∉ offen (M.faeden 1).spur := by
  obtain ⟨M9, M17, _, h9, h17, _, _, _, _, _, hf, _, hout, _, _, _⟩ := zLauf
  have h : RufErreichbarG zP zO 0 (RufStartG zP zSp zInit) M17 := rufErreichbarG_trans h9 h17
  have hsig : (() : zD.Lock) ∈ zD.haelt (M17.faeden 0).kopf.f := by
    rw [hf]; exact List.mem_cons_self
  exact ⟨M17, h, hf, rufG_haelt_signatur zO_gut zSp zInit h 0 _ List.mem_cons_self () hsig, hout⟩

/-! ## CUTS:

  What is proved: all premises of `ziel_ort` hold jointly on `zP`
  (`zP_vertragAmOrt` is the instance), and two reached runs of the
  machine: `ziel_ort_zeuge` (nine steps of thread 1: memory `0 -> 100`,
  `einzahlen` and `lies` entered and returned, contracts at every logged
  event) and `ziel_ort_zeuge_interferenz` (thread 1 writes the carrier of
  `lies`' contract, thread 0 then runs `lies` holding the lock and returns
  the other thread's value `100`, and `EnsAmRueck` holds at that return).
  The same run witnesses `rufG_haelt_statisch` and `rufG_haelt_signatur`
  (`rufG_haelt_statisch_zeuge`, `rufG_haelt_signatur_zeuge`: a frame naming
  the lock on a two-thread machine where the other thread does not hold
  it).

  What is NOT covered: runs with interleaving INSIDE a critical section
  (the lock forbids them; the rely of `ziel_ort` is what makes that
  exclusion usable), loops, the error channel, costs.
-/

#print axioms Gabbro.Grammatik.zP_vertragAmOrt
#print axioms Gabbro.Grammatik.zLauf
#print axioms Gabbro.Grammatik.ziel_ort_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_zeuge_interferenz
#print axioms Gabbro.Grammatik.rufG_haelt_statisch_zeuge
#print axioms Gabbro.Grammatik.rufG_haelt_signatur_zeuge

end Gabbro.Grammatik
