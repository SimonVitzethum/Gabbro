module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll

@[expose] public section



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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  hb := fun c hc => by revert hc; cases caller <;> intro hc <;> cases hc
  hk := by
    unfold Signatur.inputMarks
    rw [hk, OwnerFlow.empty_of_empty (vD.signatur callee).owner]
    exact ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl]⟩
  hh := RufPasst.hh_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)
  hx := RufPasst.hx_von (by
    intro L
    rw [hh]
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)

theorem vHpErr : RufPasst vD (vertragVon vD vMid) (vD.signatur vErr) [] :=
  vHp vMid vErr (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

theorem vHpMid : RufPasst vD (vertragVon vD vHaupt) (vD.signatur vMid) [] :=
  vHp vHaupt vMid (fun t h => by cases t; exact absurd h (by decide)) rfl rfl

/-- The one reason of `ferr`. -/
def vR0 : Fin (vertragVon vD vErr).gruende := ⟨0, by decide⟩

/-- `ferr`: the reason return. -/
def vRumpfErr : Endblock vD (vertragVon vD vErr) false [] [] :=
  .retWhy vR0 List.Perm.nil

/-- The `else` block of `mid`: `return`. -/
def vErrBlock : Endblock vD (vertragVon vD vMid) false (.why (vD.gruende vErr) :: [])
    (nach vD vErr []) :=
  .ret .empty List.Perm.nil

/-- `let x = ferr() else r => { return }` -/
def vLetElse : Block vD (vertragVon vD vMid) false [] [] [] :=
  .bindCallElse vErr .nil rfl vHpErr (by decide) vErrBlock .nil

/-- `if true { let x = ferr() else … }` -/
def vIte : Stmt vD (vertragVon vD vMid) false [] [] [] := .ite .tru vLetElse .nil

/-- `mid`: `if true { let x = ferr() else r => { return } }; return`. -/
def vRumpfMid : Endblock vD (vertragVon vD vMid) false [] [] :=
  .cons vIte (.ret .empty List.Perm.nil)

/-- The loop body: `leave`. -/
def vLeave : Block vD (vertragVon vD vHaupt) true [] [] [] := .cons (.leave rfl) .nil

/-- `retry 1 until false { leave } on_exceeded { }` -/
def vRetry : Stmt vD (vertragVon vD vHaupt) false [] [] [] := .retry 1 .fls vLeave .nil

/-- The axiom call `ax()`, under the lock. -/
def vAx : Stmt vD (vertragVon vD vHaupt) false [] vL vL :=
  .axiomCall () .nil rfl (fun _ _ => rfl) (fun e => nomatch e) (fun _ _ => vDarf)
    (fun e => nomatch e)

/-- `locks L { ax() }` -/
def vLocks : Stmt vD (vertragVon vD vHaupt) false [] [] [] :=
  .locks () (fun _ h => nomatch h) (.cons vAx .nil)

/-- `haupt` after its call. -/
def vRestHaupt : Endblock vD (vertragVon vD vHaupt) false [] (nach vD vMid []) :=
  .cons vRetry (.cons vLocks (.ret .empty List.Perm.nil))

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
  requires := fun _ => .tru
  ensures := fun _ => .tru
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
    ({ slots := fun _ _ _ => true, globs := (fun g => (nomatch g)), spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem vO_gut : GutO vO := by
  intro a σ ρ
  cases a
  have hW : vO.wirkt () σ ρ =
      ({ slots := fun _ _ _ => true, globs := (fun g => (nomatch g)), spur := axiomSpur [()] [] () [Res.held ()] σ.haelt ++ σ.spur }, 0) := rfl
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
      simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm
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
  | ok σ' ρ' => intro h; simp only [reduceCtorEq] at h
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
  split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]

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
      · simp only [Ausgang.schrumpf, reduceCtorEq] at h1
      · simp only [EndAusgang.zuAusgang, EndAusgang.schrumpf, execEnd, reduceCtorEq] at h1
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
    · simp only [vRetry, vLeave, execStmt, retryLauf, wahr?, eval, Bool.false_eq_true, ↓reduceIte, execBlock,
  reduceCtorEq] at h2
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

theorem vM0_faden (t : Faden) : (RufStartG vP vSp vInit).faeden t = vZ0 := by rfl

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
    offen (M.weltVon t).spur = offen (M.faeden t).spur := by rfl

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

end Gabbro.Grammatik
