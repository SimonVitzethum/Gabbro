/-
  File:      Grammatik/ZielOrtVollZeuge.lean
  Subject:   WITNESS FOR `ziel_ort_voll` -- a two-thread program whose bodies
             use an indirect call, a loop with `leave`, a reason return caught by
             `let … else`, and an axiom call writing a guarded table under
             its lock; every premise jointly, and a reached run of G with a
             memory change.

  The declaration `vD`: one table (one boolean slot, guarded by the one
  lock), one axiom writing that table, three functions:

  * `ferr` (`or R`, one reason): `return R` -- the error return;
  * `mid`: `if true { let x = ferr() else r => { return } }; return` --
    the reason is caught by the `else` block;
  * `haupt` (holds no lock; every thread's entry):
    `(&mid)(); retry 1 until false { leave } on_exceeded { };
     locks L { ax() }; return` -- an indirect call of `mid` through a
    function pointer, a loop left by `leave`, then the axiom call under the
    table's lock.

  All contracts are `true`: the witness is about the premises and the run,
  not about a clever contract. The oracle `vO` sets the slot to `true` and
  records its write (`GutO`).
-/
import Grammatik.ZielOrtVoll

namespace Gabbro.Grammatik

/-! ## 1. The declaration and the program -/

/-- The three functions. -/
inductive VFn where
  | haupt
  | mid
  | ferr
  deriving DecidableEq

def vSigHaupt : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def vSigMid : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def vSigErr : Signatur Unit Empty Unit Empty where
  params := []
  erg := some .bool
  gruende := 1
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One guarded boolean table, one lock, one axiom writing the table, three
    functions. -/
def vD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
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
  Fn := VFn
  sig := fun | .haupt => 0 | .mid => 1 | .ferr => 2
  sigNr := fun | 0 => vSigHaupt | 1 => vSigMid | _ => vSigErr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
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

def vHaupt : vD.Fn := VFn.haupt
def vMid : vD.Fn := VFn.mid
def vErr : vD.Fn := VFn.ferr

/-- The lock holdings inside the `locks` block. -/
abbrev vL : List (Res vD) := [Res.held (D := vD) ()]

theorem vDarf : darf vD () vL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-- A call between lock-free functions. -/
theorem vHp (caller callee : vD.Fn) (hw : ∀ t, (vD.signatur callee).schreibt t = true →
    (vertragVon vD caller).schreibt t = true)
    (hh : (vD.signatur callee).haelt = []) (hk : (vD.signatur callee).konsumiert = []) :
    RufPasst vD (vertragVon vD caller) (vD.signatur callee) [] where
  hw := hw
  hg := fun g => nomatch g
  hk := by rw [hk]; exact ⟨[], List.Perm.refl [], by simp⟩
  hh := by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem vHpErr : RufPasst vD (vertragVon vD vMid) (vD.signatur vErr) [] :=
  vHp vMid vErr (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

theorem vHpMid : RufPasst vD (vertragVon vD vHaupt) (vD.signatur vMid) [] :=
  vHp vHaupt vMid (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

/-- The one reason of `ferr`. -/
def vR0 : Fin (vertragVon vD vErr).gruende := ⟨0, by decide⟩

/-- `ferr`: the reason return. -/
def vRumpfErr : Endblock vD (vertragVon vD vErr) false [] [] :=
  .retGrund vR0 List.Perm.nil

/-- The `else` block of `mid`: `return`. -/
def vErrBlock : Endblock vD (vertragVon vD vMid) false (.grund (vD.gruende vErr) :: [])
    (nach vD vErr []) :=
  .ret .keine List.Perm.nil

/-- `let x = ferr() else r => { return }` -/
def vLetElse : Block vD (vertragVon vD vMid) false [] [] [] :=
  .bindCallElse vErr .nil rfl vHpErr (by decide) vErrBlock .nil

/-- `if true { let x = ferr() else … }` -/
def vIte : Stmt vD (vertragVon vD vMid) false [] [] [] := .ite .wahr vLetElse .nil

/-- `mid`: `if true { let x = ferr() else r => { return } }; return`. -/
def vRumpfMid : Endblock vD (vertragVon vD vMid) false [] [] :=
  .cons vIte (.ret .keine List.Perm.nil)

/-- The loop body: `leave`. -/
def vLeave : Block vD (vertragVon vD vHaupt) true [] [] [] := .cons (.leave rfl) .nil

/-- `retry 1 until false { leave } on_exceeded { }` -/
def vRetry : Stmt vD (vertragVon vD vHaupt) false [] [] [] := .retry 1 .falsch vLeave .nil

/-- The axiom call `ax()`, under the lock. -/
def vAx : Stmt vD (vertragVon vD vHaupt) false [] vL vL :=
  .axiomCall () .nil rfl (fun _ _ => rfl) (fun e => nomatch e) (fun _ _ => vDarf)
    (fun e => nomatch e)

/-- `locks L { ax() }` -/
def vLocks : Stmt vD (vertragVon vD vHaupt) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons vAx .nil)

/-- `haupt` after its call. -/
def vRestHaupt : Endblock vD (vertragVon vD vHaupt) false [] (nach vD vMid []) :=
  .cons vRetry (.cons vLocks (.ret .keine List.Perm.nil))

/-- The pointer `&mid`. -/
def vZeigerMid {Γ : Ctx} {Λ : List (Res vD)} : Expr vD Γ Λ (.fnptr 1) := .fnref vMid 1 rfl

/-- `(&mid)()` -- an indirect call. -/
def vRufMid : Stmt vD (vertragVon vD vHaupt) false [] [] (nach vD vMid []) :=
  .callInd vZeigerMid .nil vHpMid rfl

/-- `haupt`: `(&mid)(); retry …; locks L { ax() }; return`. -/
def vRumpfHaupt : Endblock vD (vertragVon vD vHaupt) false [] [] :=
  .cons vRufMid vRestHaupt

/-- The witness program: all contracts `true`. -/
def vP : Programm vD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .haupt => vRumpfHaupt
    | .mid => vRumpfMid
    | .ferr => vRumpfErr

def vFs : List vD.Fn := [vHaupt, vMid, vErr]

theorem vFs_voll : ∀ g : vD.Fn, g ∈ vFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem vP_fragment : programmImFragmentV vP vFs = true := by decide

/-- The program is NOT in the old fragment: it uses the loop, the exit, the
    error channel and the axiom. -/
theorem vP_nicht_alt : programmImFragment vP vFs = false := by decide

theorem vP_fuss : fussOrtB vP vFs = true := by decide

/-! ## 2. Oracle, start, and the user obligations -/

/-- The oracle: sets the slot to `true`, records the write. -/
def vO : Orakel vD where
  wirkt := fun _ σ _ =>
    ({ slots := fun _ _ _ => true
       globs := fun g => nomatch g
       spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem vO_gut : GutO vO := by
  intro a σ ρ
  cases a
  have hW : vO.wirkt () σ ρ =
      ({ slots := fun _ _ _ => true
         globs := fun g => nomatch g
         spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0) := rfl
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro t ht
      cases t
      exact absurd ht (by decide)
    · intro g
      exact nomatch g
  · rw [hW]
    show offen (axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur) = offen σ.spur
    exact offen_nurZugriff _ _ (fun e he => by
      simp only [axiomSpur, List.mem_append, List.mem_map, List.mem_filter] at he
      rcases he with ⟨t, _, rfl⟩ | ⟨g, _, _⟩
      · rfl
      · exact nomatch g)
  · intro hgt _
    refine ⟨[()], [], [Res.held ()], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t _
      cases t
      exact List.Mem.head _
    · intro g
      exact nomatch g
    · intro t _
      cases t
      exact vDarf
    · intro g
      exact nomatch g
    · intro m st hm
      simp at hm
    · intro L hL
      have eL : L = () := rfl
      rw [eL]
      exact hgt () rfl () (List.Mem.head _)
    · rw [hW]

/-- The start memory: the slot `false`. -/
def vSp : Speicher vD := ⟨fun _ _ _ => false, fun g => nomatch g⟩

/-- Every thread starts in `haupt`. -/
def vInit : Faden → Σ f : vD.Fn, Env vD (vD.params f) :=
  fun _ => ⟨vHaupt, .nil⟩

theorem vP_start : StartGut vP vSp vInit := fun _ => rfl

theorem vInit_exklusiv : StartExklusiv (D := vD) vInit :=
  fun _ _ _ _ h => nomatch h

/-- An `end` block that starts with a statement ends in a logic outcome only
    through that statement or its rest. -/
theorem execEnd_cons_logikV {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (e : Logik D) (h : execEnd O passes R (.cons s rest) σ ρ = .logik e) :
    execStmt O passes R s σ ρ = .logik e ∨
      ∃ σ' ρ', execStmt O passes R s σ ρ = .ok σ' ρ' ∧ execEnd O passes R rest σ' ρ' = .logik e := by
  simp only [execEnd] at h
  revert h
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => intro h; exact Or.inr ⟨σ', ρ', rfl, h⟩
  | logik e' => intro h; cases h; exact Or.inl rfl
  | _ => intro h; cases h

/-- The gate of a `requires true` callee lets every call through. -/
theorem vTor (R : ∀ f : vD.Fn, World vD → Env vD (vD.params f) → RufAusgang f) (g : vD.Fn)
    (σ : World vD) (ρ : Env vD (vD.params g)) : torRuf vP R g σ ρ = R g σ ρ := if_pos rfl

theorem vP_koerper_err : KoerperGutV vP 0 vErr := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : vP.rumpf vErr = vRumpfErr := rfl
  rw [hr] at hrun
  simp only [vRumpfErr, execEnd] at hrun
  cases hrun

theorem mapWelt_logikV {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {o : Ausgang V l Γ} {f : World D → World D} {e : Logik D} (h : o.mapWelt f = .logik e) :
    o = .logik e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem execBlock_eins_logikV {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) {e : Logik D}
    (h : execBlock O passes R (.cons s .nil) σ ρ = .logik e) :
    execStmt O passes R s σ ρ = .logik e := by
  simp only [execBlock] at h
  revert h
  cases execStmt O passes R s σ ρ with
  | ok σ' ρ' => intro h; simp [execBlock] at h
  | _ => intro h; exact h

/-- An axiom call never ends in a logic failure (only in `ok` or in the
    hardware outcome of an answer outside its type). -/
theorem execStmt_axiomCall_logik {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (σ : World D) (ρ : Env D Γ)
    (e : Logik D) :
    execStmt O passes R (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ ≠
      .logik e := by
  simp only [execStmt]
  split <;> simp

theorem vP_koerper_mid : KoerperGutV vP 0 vMid := by
  intro O' _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : vP.rumpf vMid = vRumpfMid := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [vIte, vLetElse, vErrBlock, execStmt, execBlock, vTor] at h1
    split at h1
    · split at h1
      · simp [Ausgang.schrumpf] at h1
      · simp [execEnd, EndAusgang.schrumpf, EndAusgang.zuAusgang] at h1
      · rename_i e hR
        cases h1
        exact hOV _ _ _ _ hR g rfl
      · cases h1
    · cases h1
  · simp only [execEnd] at h1
    cases h1

theorem vP_koerper_haupt : KoerperGutV vP 0 vHaupt := by
  intro O' _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro g hrun
  have hr : vP.rumpf vHaupt = vRumpfHaupt := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [vRufMid, vZeigerMid, execStmt, eval, vTor] at h1
    split at h1
    · cases h1
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h1
      exact hOV _ _ _ _ hR g rfl
    · cases h1
  · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
    · simp [vRetry, vLeave, execStmt, retryLauf, execBlock, eval, wahr?] at h2
    · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h2 with h3 | ⟨σ3, ρ3, _, h3⟩
      · simp only [vLocks] at h3
        simp only [execStmt] at h3
        exact execStmt_axiomCall_logik _ _ _ _ _ _ _ _ _ _ _ _ _
          (execBlock_eins_logikV _ _ _ vAx _ _ (mapWelt_logikV h3))
      · simp only [execEnd] at h3
        cases h3

theorem vP_koerper : ∀ f, KoerperGutV vP 0 f := by
  intro f
  cases f
  · exact vP_koerper_haupt
  · exact vP_koerper_mid
  · exact vP_koerper_err

/-- An event of the declaration (a release of the lock). -/
def vE0 : Ereignis vD := .gibt ()

/-- **All premises of `ziel_ort_voll` hold jointly on `vP`.** -/
theorem vP_vertragAmOrt : ∀ M : RufMaschineG vD,
    RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M → VertragAmOrtG vP M :=
  ziel_ort_voll vP vO 0 vFs vSp vInit vE0 vO_gut vFs_voll vP_fragment vP_fuss vP_koerper
    vP_start vInit_exklusiv

/-! ## 3. The run -/

/-- The start thread state (every thread): `haupt`, no lock held. -/
def vZ0 : RufFadenG vD :=
  ⟨[], ⟨vHaupt, .nil, vSp.welt [], ⟨false, [], [], .nil, .ende vRumpfHaupt⟩⟩, [],
    [RufEreignisF.eintritt vHaupt .nil (vSp.welt [])]⟩

theorem vM0_faden (t : Faden) : (RufStartG vP vSp vInit).faeden t = vZ0 := rfl

theorem vHg0 {s : List (Ereignis vD)} (h : offen s = []) :
    HeldGenau ([] : List (Res vD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem vHgL {s : List (Ereignis vD)} (h : offen s = [()]) : HeldGenau vL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem vOffen_weltVon (M : RufMaschineG vD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := rfl

theorem vHoff_z {M : RufMaschineG vD} {f : Faden} {stapel : List (RufRahmenG vD)} {fn : vD.Fn}
    {rho : Env vD (vD.params fn)} {s0 : World vD} {log : List (RufEreignisF vD)} {l : Bool}
    {Γ : Ctx} {Λ : List (Res vD)} {ρ : Env vD Γ} {r : GRest vD (vertragVon vD fn) l Γ Λ}
    {σ : World vD} {x : List vD.Lock} (h : ZustandG M f stapel fn rho s0 log ρ r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [← h.spur]; exact ho

theorem vHoff_g {M : RufMaschineG vD} {f : Faden} {caller : RufRahmenG vD}
    {rst : List (RufRahmenG vD)} {fn : vD.Fn} {rho : Env vD (vD.params fn)} {s0 : World vD}
    {log : List (RufEreignisF vD)} {v : ErgVal vD (vD.erg fn)} {σ : World vD}
    {x : List vD.Lock} (h : GepopptG M f caller rst fn rho s0 log v σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [h.1] at ho; exact ho

theorem vHoff_gg {M : RufMaschineG vD} {f : Faden} {caller : RufRahmenG vD}
    {rst : List (RufRahmenG vD)} {fn : vD.Fn} {rho : Env vD (vD.params fn)} {s0 : World vD}
    {log : List (RufEreignisF vD)} {r : Fin (vD.gruende fn)} {σ : World vD}
    {x : List vD.Lock} (h : GepopptGrundG M f caller rst fn rho s0 log r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [h.1] at ho; exact ho

theorem vHoff_e {M : RufMaschineG vD} {f : Faden} {z : RufFadenG vD} {x : List vD.Lock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

/-- `rufCallInd` over a thread state (as `w_rufEnde`): the pointer read at
    the key names the callee `g`. -/
theorem w_rufCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ (nachSig D (D.sigNr n) Λ)) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.callInd p args hp hr) rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (g : D.Fn) (hg : D.sig g = n)
    (hv : eval ((M.weltVon f).lese Λ (p.orte ++ args.orte)) p
      ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
          ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩ :: z.stapel) g
        (umsig hg (evalArgs ((M.weltVon f).lese Λ (p.orte ++ args.orte)) args
          ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ))
        ((M.weltVon f).lese Λ (p.orte ++ args.orte))
        (RufEreignisF.eintritt g
          (umsig hg (evalArgs ((M.weltVon f).lese Λ (p.orte ++ args.orte)) args
            ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ))
          ((M.weltVon f).lese Λ (p.orte ++ args.orte)) :: z.log)
        (umsig hg (evalArgs ((M.weltVon f).lese Λ (p.orte ++ args.orte)) args
          ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ))
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ (p.orte ++ args.orte)) := by
  subst hz
  exact ⟨_, RufSchrittG.rufCallInd M f l Γ Λ n p args hp hr rest ρ hhead hΛ _ rfl g hg hv _ rfl
    _ rfl, zustandG_neu rfl rfl⟩

/-- The axiom's answer world appends only access events. -/
theorem vO_erw (σ : World vD) (ρ : Env vD (vD.aparams ())) :
    Erw σ (vO.wirkt () σ ρ).1 :=
  ⟨_, rfl, fun e he => by
    simp only [axiomSpur, List.mem_append, List.mem_map, List.mem_filter] at he
    rcases he with ⟨t, _, rfl⟩ | ⟨g, _, _⟩
    · rfl
    · exact nomatch g⟩

/-- **The run.** Fourteen steps of thread 0 of G from the start machine of
    `vP` (every thread in `haupt`, the slot `false`): `haupt` calls `mid`
    through the pointer `&mid`,
    `mid` unfolds its `if` and calls `ferr` in `let … else`; `ferr` returns
    its reason, which pops into `mid`'s `else` block (logged `grund`);
    `mid` returns to `haupt` (logged `rueck`); `haupt` enters the `retry`
    loop, whose body is left by `leave`; `haupt` takes the lock and calls
    the axiom, which writes the slot `true`. -/
theorem vLauf : ∃ M : RufMaschineG vD,
    RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M ∧
    M.speicher.slots () 0 () = true ∧
    (∃ rho r s0 s1, RufEreignisF.grund vErr rho r s0 s1 ∈ (M.faeden 0).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck vMid rho v s0 s1 ∈ (M.faeden 0).log) ∧
    (M.faeden 0).kopf.f = vHaupt ∧ (() : vD.Lock) ∈ offen (M.faeden 0).spur ∧
    M.faeden 1 = (RufStartG vP vSp vInit).faeden 1 := by
  have h0 := vM0_faden (0 : Faden)
  have hoff0 : offen ((RufStartG vP vSp vInit).faeden 0).spur = [] := rfl
  -- `haupt` calls `mid`
  obtain ⟨M1, s1, hZ1⟩ := w_rufCallInd (P := vP) (O := vO) (passes := 0) h0 vZeigerMid .nil vHpMid
    rfl vRestHaupt .nil rfl (vHg0 hoff0) vMid rfl rfl
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- `mid`: unfold the `if`, take its true branch, call `ferr` in `let … else`
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := vP) (O := vO) (passes := 0) e1 vIte
    (.ret .keine List.Perm.nil) .nil rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur, vOffen_weltVon]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  obtain ⟨M3, s3, hZ3⟩ := w_iteWahr (P := vP) (O := vO) (passes := 0) e2 .wahr vLetElse .nil
    .nil (.ende (.ret .keine List.Perm.nil)) .nil rfl rfl (vHg0 (vHoff_e e2 hoff2))
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  obtain ⟨M4, s4, hZ4⟩ := w_bindCallElse (P := vP) (O := vO) (passes := 0) e3 vErr .nil rfl
    vHpErr (by decide) vErrBlock .nil (.dann .nil (.ende (.ret .keine List.Perm.nil))) .nil rfl
    (vHg0 (vHoff_e e3 hoff3))
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff3
  have e4 := hZ4.1
  try dsimp only at e4
  -- `ferr` returns its reason; `mid` runs its `else` block
  obtain ⟨M5, s5, hG5⟩ := w_rueckGrundP (P := vP) (O := vO) (passes := 0) e4 _ _ rfl
    (PopGrund.sonst vErrBlock .nil (.dann .nil (.ende (.ret .keine List.Perm.nil))) .nil rfl)
    vR0 List.Perm.nil .nil rfl (vHg0 (vHoff_e e4 hoff4))
  have hoff5 : offen (M5.faeden 0).spur = [] := by
    rw [hG5.1]; exact hoff4
  have e5 := hG5.1
  try dsimp only at e5
  -- `mid` returns to `haupt`
  obtain ⟨M6, s6, hG6⟩ := w_rueckP (P := vP) (O := vO) (passes := 0) e5 _ _ rfl
    (PopArt.wie rfl) .keine List.Perm.nil _ rfl (vHg0 (vHoff_e e5 hoff5))
  have hoff6 : offen (M6.faeden 0).spur = [] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  have e6 := hG6.1
  try dsimp only at e6
  -- `haupt`: the loop, left by `leave`
  obtain ⟨M7, s7, hZ7⟩ := w_endeEntf (P := vP) (O := vO) (passes := 0) e6 vRetry
    (.cons vLocks (.ret .keine List.Perm.nil)) .nil rfl rfl
  have hoff7 : offen (M7.faeden 0).spur = [] := by
    rw [hZ7.spur, vOffen_weltVon]; exact hoff6
  have e7 := hZ7.1
  try dsimp only at e7
  obtain ⟨M8, s8, hZ8⟩ := w_dannRetry (P := vP) (O := vO) (passes := 0) e7 1 .falsch vLeave
    .nil .nil (.ende (.cons vLocks (.ret .keine List.Perm.nil))) .nil rfl
  have hoff8 : offen (M8.faeden 0).spur = [] := by
    rw [hZ8.spur, vOffen_weltVon]; exact hoff7
  have e8 := hZ8.1
  try dsimp only at e8
  obtain ⟨M9, s9, hZ9⟩ := w_wiederSchritt (P := vP) (O := vO) (passes := 0) e8 0 .falsch vLeave
    .nil (.dann .nil (.ende (.cons vLocks (.ret .keine List.Perm.nil)))) .nil rfl rfl
    (vHg0 (vHoff_e e8 hoff8))
  have hoff9 : offen (M9.faeden 0).spur = [] := by
    rw [hZ9.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff8
  have e9 := hZ9.1
  try dsimp only at e9
  obtain ⟨M10, s10, hZ10⟩ := w_abbWieder (P := vP) (O := vO) (passes := 0) e9 true 0 .falsch
    vLeave .nil (.dann .nil (.ende (.cons vLocks (.ret .keine List.Perm.nil)))) .nil .nil rfl
    (vHg0 (vHoff_e e9 hoff9))
  have hoff10 : offen (M10.faeden 0).spur = [] := by
    rw [hZ10.spur, vOffen_weltVon]; exact hoff9
  have e10 := hZ10.1
  try dsimp only at e10
  obtain ⟨M11, s11, hZ11⟩ := w_dannLeer (P := vP) (O := vO) (passes := 0) e10
    (.ende (.cons vLocks (.ret .keine List.Perm.nil))) .nil rfl
  have hoff11 : offen (M11.faeden 0).spur = [] := by
    rw [hZ11.spur, vOffen_weltVon]; exact hoff10
  have e11 := hZ11.1
  try dsimp only at e11
  -- `haupt`: take the lock, call the axiom
  obtain ⟨M12, s12, hZ12⟩ := w_endeEntf (P := vP) (O := vO) (passes := 0) e11 vLocks
    (.ret .keine List.Perm.nil) .nil rfl rfl
  have hoff12 : offen (M12.faeden 0).spur = [] := by
    rw [hZ12.spur, vOffen_weltVon]; exact hoff11
  have e12 := hZ12.1
  try dsimp only at e12
  have hfremd12 : ∀ u, u ≠ 0 → M12.faeden u = vZ0 := by
    intro u hu
    rw [rufSchrittG_fremd s12 u hu, rufSchrittG_fremd s11 u hu, rufSchrittG_fremd s10 u hu,
      rufSchrittG_fremd s9 u hu, rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu,
      rufSchrittG_fremd s6 u hu, rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu,
      rufSchrittG_fremd s3 u hu, rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu, vM0_faden]
  obtain ⟨M13, s13, hZ13⟩ := w_locks (P := vP) (O := vO) (passes := 0) e12 ()
    (fun _ h => by cases h) (.cons vAx .nil) .nil (.ende (.ret .keine List.Perm.nil)) .nil rfl
    (vHg0 (vHoff_e e12 hoff12))
    (fun u hu h => by rw [hfremd12 u hu] at h; exact List.not_mem_nil h)
  have hoff13 : offen (M13.faeden 0).spur = [()] := by
    rw [hZ13.spur]
    show offen (Ereignis.nimmt () (offen (M12.weltVon 0).spur) :: (M12.weltVon 0).spur) = [()]
    simp only [offen]
    rw [vOffen_weltVon, hoff12]
    rfl
  have e13 := hZ13.1
  try dsimp only at e13
  obtain ⟨M14, s14, hZ14⟩ := w_dannBlatt (P := vP) (O := vO) (passes := 0) e13 vAx .nil
    _ .nil rfl rfl
    (vHgL (vHoff_e e13 hoff13)) _ _ rfl (vO_erw _ .nil)
  have hr14 : RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M14 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7) s8) s9)
      s10) s11) s12) s13) s14
  have e14 := hZ14.1
  try dsimp only at e14
  refine ⟨M14, hr14, ?_, ?_, ?_, by rw [e14]; rfl, ?_, ?_⟩
  · rw [hZ14.2]
    rfl
  · rw [e14]
    exact ⟨_, _, _, _, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · rw [e14]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  · have hoff14 : offen (M14.faeden 0).spur = [()] := by
      rw [hZ14.spur]
      exact ((vO_erw ((M13.weltVon 0).lese vL []) .nil).offen).trans
        (((Erw.lese _ _ _).offen).trans hoff13)
    rw [hoff14]
    exact List.mem_cons_self
  · rw [rufSchrittG_fremd s14 1 (by decide), rufSchrittG_fremd s13 1 (by decide), hfremd12 1
      (by decide)]
    rfl

/-! ## 4. The witness -/

/-- **`ziel_ort_voll_zeuge`.** On the two-thread program `vP` (every thread
    starts in `haupt`), whose bodies use an indirect call (`haupt` calls
    `mid` through `&mid`), a `retry` loop left by `leave`, a reason return
    (`ferr`) caught by `let … else` (`mid`) and an axiom call writing the
    guarded table under its lock (`haupt`) -- a program OUTSIDE
    the fragment of `ziel_ort` -- every premise of `ziel_ort_voll` holds
    jointly: the hardware assumption for the writing oracle, the complete
    member list, both decidable checks, the user obligation `KoerperGutV`
    for all three functions, the start obligation and the exclusive start.
    On a machine reached by fourteen steps of thread 0, the axiom has
    changed memory (the slot from `false` to `true`), the reason return and
    `mid`'s normal return after catching it are logged, the loop is behind
    (thread 0 is in `haupt`, holding the lock after the axiom), thread 1 has
    not moved, and the contracts hold at every logged entry and return. -/
theorem ziel_ort_voll_zeuge :
    GutO vO ∧ (∀ g : vD.Fn, g ∈ vFs) ∧ programmImFragmentV vP vFs = true ∧
    programmImFragment vP vFs = false ∧ fussOrtB vP vFs = true ∧
    (∀ f : vD.Fn, KoerperGutV vP 0 f) ∧ StartGut vP vSp vInit ∧
    StartExklusiv (D := vD) vInit ∧
    ∃ M : RufMaschineG vD, RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M ∧
      vSp.slots () 0 () = false ∧ M.speicher.slots () 0 () = true ∧
      (∃ rho r s0 s1, RufEreignisF.grund vErr rho r s0 s1 ∈ (M.faeden 0).log) ∧
      (∃ rho v s0 s1, RufEreignisF.rueck vMid rho v s0 s1 ∈ (M.faeden 0).log) ∧
      (M.faeden 0).kopf.f = vHaupt ∧ (() : vD.Lock) ∈ offen (M.faeden 0).spur ∧
      M.faeden 1 = (RufStartG vP vSp vInit).faeden 1 ∧
      VertragAmOrtG vP M := by
  obtain ⟨M, hr, hsp, hg, hru, hf, hL, h1⟩ := vLauf
  exact ⟨vO_gut, vFs_voll, vP_fragment, vP_nicht_alt, vP_fuss, vP_koerper, vP_start,
    vInit_exklusiv, M, hr, rfl, hsp, hg, hru, hf, hL, h1, vP_vertragAmOrt M hr⟩

/-! ## CUTS:

  What is proved: all premises of `ziel_ort_voll` hold jointly on `vP`
  (`vP_vertragAmOrt` is the instance), `vP` is outside the old fragment
  (`vP_nicht_alt`), and a reached run of fourteen steps of G through an
  indirect push (`rufCallInd`), a `let … else` push, a reason pop into the `else` block, a normal
  pop, the `retry` unfold, a failed bound, the `leave` exit, the `locks`
  take and the axiom leaf (`vLauf`), with the memory change done by the
  axiom (`ziel_ort_voll_zeuge`).

  What is NOT covered: the run moves thread 0 only (thread 1 is started
  in `haupt` and stays there); the contracts are `true`, so the witness
  shows the premises jointly satisfiable and the run real, not a
  contract whose proof needs the new obligation's frame reasoning.
-/

#print axioms Gabbro.Grammatik.vO_gut
#print axioms Gabbro.Grammatik.vP_koerper
#print axioms Gabbro.Grammatik.vP_vertragAmOrt
#print axioms Gabbro.Grammatik.vLauf
#print axioms Gabbro.Grammatik.ziel_ort_voll_zeuge

end Gabbro.Grammatik
