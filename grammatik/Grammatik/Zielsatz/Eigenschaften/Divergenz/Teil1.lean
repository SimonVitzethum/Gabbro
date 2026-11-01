module

public import Grammatik.Zielsatz.Eigenschaften.NeverAsm
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz

@[expose] public section



namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

/-! ## 1. Exit evidence: a body that cannot leave, an invariant that holds -/

/-- **No exit**: the loop body answers only `ok` or `next` -- never `leave`,
    never a return, a reason, or a `logik`/`hardware` outcome. At the
    accepted `forever` shape this is what "un-leavable" means in the model:
    the body either passes or spins, so the loop can only diverge. -/
def NoExit {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (body : Block D V true Γ Λ Λ) : Prop :=
  ∀ σ ρ, (∃ σ' ρ', execBlock O passes R body σ ρ = .ok σ' ρ') ∨
    (∃ h σ' ρ', execBlock O passes R body σ ρ = .next h σ' ρ')

/-- **The invariant holds everywhere**: the loop guard passes at every world
    the run can present. At the accepted shape this is the writer's own
    invariant (here `.tru`); THAT it holds is proved per program, never
    assumed in general. -/
def InvWahr {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (inv : Expr D Γ Λ .bool) (Hold : List (Res D)) : Prop :=
  ∀ σ ρ, wahr? (eval ((σ : World D).lese Hold inv.orte) inv
    ((σ : World D).lese Hold inv.orte) ρ) = true

/-! ## 2. `forever` with exit evidence diverges as declared -/

/-- **The fuel argument, syntax-free**: with an exit-free step and a true
    guard, `foreverLauf` answers the named assumption at every fuel. No
    program syntax in the premises, so no witness is owed here; the
    syntax-facing corollary below carries the joint witness instead. -/
theorem foreverLauf_noexit {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (invcl : World D → Env D Γ → World D × Bool)
    (hNo : ∀ σ ρ, (∃ σ' ρ', schritt σ ρ = .ok σ' ρ') ∨
      (∃ h σ' ρ', schritt σ ρ = .next h σ' ρ'))
    (hInv : ∀ σ ρ, (invcl σ ρ).2 = true) :
    ∀ n σ ρ, foreverLauf (l := l) a schritt invcl n σ ρ = .hardware (.fortschritt a) := by
  intro n
  induction n with
  | zero => intro σ ρ; rfl
  | succ n ih =>
      intro σ ρ
      have hI : (invcl σ ρ).2 = true := hInv σ ρ
      simp only [foreverLauf]
      rw [if_neg (by simp only [hI, Bool.true_eq_false, not_false_eq_true])]
      rcases hNo (invcl σ ρ).1 ρ with ⟨σ', ρ', h⟩ | ⟨h, σ', ρ', h⟩
      · rw [h]; exact ih _ _
      · rw [h]; exact ih _ _

/-- **Divergence as declared**: a `forever` whose body cannot exit and whose
    invariant holds ends in `hardware (fortschritt a)` at every budget --
    the `progress` assumption the writer named. The C runs the loop without
    end; the model records the granted passes as fuel and the exhaustion as
    the named exit. Proved, never asserted. -/
theorem forever_noexit_divergiert {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hNo : NoExit O passes R body) (hInv : InvWahr inv Λ) :
    execStmt O passes R ((.forever a inv body : Stmt D V l Γ Λ Λ)) σ ρ =
      .hardware (.fortschritt a) := by
  simp only [execStmt]
  exact foreverLauf_noexit a _ _ (fun σ ρ => hNo σ ρ) (fun σ ρ => hInv σ ρ) passes σ ρ

/-- ... and never in a `logik` outcome: the divergence is the declared
    assumption's, not the writer's failed check -- consistent with
    `KeinLogikHaltG` (§4 bridges it at the machine). -/
theorem forever_noexit_kein_logik {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hNo : NoExit O passes R body) (hInv : InvWahr inv Λ) (e : Logik D) :
    execStmt O passes R ((.forever a inv body : Stmt D V l Γ Λ Λ)) σ ρ ≠ .logik e := by
  have hE := forever_noexit_divergiert (l := l) O passes R a inv body σ ρ hNo hInv
  rw [hE]
  intro hcon
  cases hcon

/-- ... and never a return: a diverging `forever` delivers no value, at any
    budget. For a `-> never` body this is the point: nothing comes back. -/
theorem forever_noexit_kein_zurueck {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hNo : NoExit O passes R body) (hInv : InvWahr inv Λ) (σ' : World D)
    (v : ErgVal D V.erg) :
    execStmt O passes R ((.forever a inv body : Stmt D V l Γ Λ Λ)) σ ρ ≠
      .zurueck σ' v := by
  have hE := forever_noexit_divergiert (l := l) O passes R a inv body σ ρ hNo hInv
  rw [hE]
  intro hcon
  cases hcon

/-- **The empty spin**: `forever a invariant true {}` diverges at every
    budget with no evidence premises at all -- the body answers `ok` and the
    guard is `true` by computation. -/
theorem forever_leer_divergiert {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R ((.forever a .tru .nil : Stmt D V l Γ Λ Λ)) σ ρ =
      .hardware (.fortschritt a) := by
  have hNo : NoExit (D := D) (V := V) (Γ := Γ) (Λ := Λ) O passes R
      (.nil : Block D V true Γ Λ Λ) :=
    fun σ ρ => Or.inl ⟨_, _, rfl⟩
  have hInv : InvWahr (D := D) (Γ := Γ) (Λ := Λ) (.tru : Expr D Γ Λ .bool) Λ :=
    fun _ _ => rfl
  exact forever_noexit_divergiert O passes R a .tru .nil σ ρ hNo hInv

/-! ## 3. `asm`: a `-> never` foreign body never comes back -/

/-- **The exit evidence for `asm`**: a `-> never` axiom's answer class is
    empty -- no raw word of any oracle image fits the declared result. A
    `-> never` foreign body with an `out` has no fitting answer in the
    model; whatever the machine says, the call is the foreign code breaking
    its declaration. (Per-axiom form of `axNeverGut_gilt`, NeverAsm.lean.) -/
theorem asm_never_antwort_leer {D : Deklaration} (a : D.Ax)
    (h : D.aerg a = some .never) : AntwortLeer D (D.aerg a) := by
  rw [h]
  exact antwortLeer_never

/-- **The call never continues**: running a `bindAxiom` whose declared
    result is `never` never answers `ok` -- the continuation never runs.
    The outcome is `hardware (annahme a)` (`execBlock_bindAxiom_never`), the
    named assumption that owns the foreign effects, so divergence holds per
    the declared effects and never by assertion. -/
theorem asm_never_kein_ok {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (hne : τ = .never)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ) :
    execBlock O passes R ((.bindAxiom a args he hw hg hd hgd rest : Block D V l Γ Λ Λ'))
      σ ρ ≠ .ok σ' ρ' := by
  have hE := execBlock_bindAxiom_never O passes R a args he hw hg hd hgd rest hne σ ρ
  rw [hE]
  intro hcon
  cases hcon

/-! ## 4. `KeinLogikHaltG` at the spin: per-thread checks, one step -/

/-- The spin heads of `forever a invariant true {}`. -/
def SpinKopf {D : Deklaration} (M : RufMaschineG D) (t : Faden) : Prop :=
  ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a n .tru .nil k⟩ ∨
    (M.faeden t).kopf.rest = ⟨true, Γ, Λ, ρ, .dann .nil (.ewigRest a n .tru .nil k)⟩ ∨
    (M.faeden t).kopf.rest = ⟨true, Γ, Λ, ρ, .ewigRest a n .tru .nil k⟩

theorem spin_prueft {D : Deklaration} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {t : Faden} (h : SpinKopf M t) : PrueftG O passes M t := by
  obtain ⟨l0, Γ0, Λ0, ρ0, a0, n0, k0, h | h | h⟩ := h
  all_goals
    refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
      fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
      fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
    all_goals (rw [h] at hr; first | (cases hr; done) | skip)
  · cases hr
    simp only [wahr?, eval]

/-- A thread at a bare `return` passes every check vacuously. -/
theorem ret_prueft {D : Deklaration} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {t : Faden} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg}
    {hΛ : Λ.Perm (vertragVon D (M.faeden t).kopf.f).ende}
    (h : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.ret e hΛ)⟩) : PrueftG O passes M t := by
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩ <;>
  (rw [h] at hr; cases hr)

/-- **One step, `forever`**: a thread standing at a true-invariant `forever`
    head with budget `n + 1` and the empty body takes its G step
    (`ewigWeiter`, RufMaschineG.lean) -- given the lock-bookkeeping side
    conditions every reading rule of G carries (`HeldIn` of the head
    holdings, the read-world spur equation). A progress fact about ONE
    head shape (the empty spin, guard `true`); the check side is
    `spin_prueft`, the reached-machine witness `ewig_spin_zeuge` (§8). -/
theorem ewig_wahr_schreitet {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {t : Faden}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {a : D.Annahme} {n : Nat}
    {k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ}
    (hhead : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) (.tru : Expr D Γ Λ .bool)
      (.nil : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ) k⟩)
    (hspur : ((M.weltVon t).lese Λ ((.tru : Expr D Γ Λ .bool)).orte).spur =
      (M.faeden t).spur)
    (hHeld : HeldIn Λ (offen (M.faeden t).spur)) :
    ∃ M', RufSchrittG P O passes M t M' := by
  refine ⟨_, RufSchrittG.ewigWeiter M t l Γ Λ a n (.tru : Expr D Γ Λ .bool)
    (.nil : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ) k ρ hhead
    ((M.weltVon t).lese Λ ((.tru : Expr D Γ Λ .bool)).orte) rfl rfl [] ?_ hHeld⟩
  simp only [hspur, List.nil_append]

/-- **A `bindAxiom` head is no leaf head** (review G10 F3: a
    discrimination fact, vacuous -- the two leaf clauses of `PrueftG` never
    fire at a call head, whatever the axiom). It says nothing specific about
    `-> never` axioms; their stop is `nieZurueck` (`kopf_nieZurueck_never`,
    NeverAsm.lean), never `hardware` (`kein_hardware_an_never`). -/
theorem bindAxiom_kein_blatt {D : Deklaration} {M : RufMaschineG D} {t : Faden}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {a : D.Ax} {τ : Ty} {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ}
    {hw : ∀ t2, D.aschreibt a t2 = true →
      (vertragVon D (M.faeden t).kopf.f).schreibt t2 = true}
    {hg : ∀ g, D.agschreibt a g = true →
      (vertragVon D (M.faeden t).kopf.f).gschreibt g = true}
    {hd : ∀ t2, D.aschreibt a t2 = true → darf D t2 Λ}
    {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    {rest : Block D (vertragVon D (M.faeden t).kopf.f) l (τ :: Γ) Λ Λ}
    {k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ}
    (O : Orakel D) (passes : Nat)
    (hhead : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann
      (.bindAxiom a args he hw hg hd hgd rest) k⟩) :
    (∀ (l' : Bool) (Γ' : Ctx) (Λx Λ'' : List (Res D)) (ρ' : Env D Γ')
      (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l' Γ' Λx Λ'')
      (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l' Γ' Λ''),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l', Γ', Λx, ρ', .ende (.cons s K)⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ' ≠ .logik e) ∧
    (∀ (l' : Bool) (Γ' : Ctx) (Λx Λ' Λ'' : List (Res D)) (ρ' : Env D Γ')
      (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l' Γ' Λx Λ')
      (rst : Block D (vertragVon D (M.faeden t).kopf.f) l' Γ' Λ' Λ'')
      (k' : GRest D (vertragVon D (M.faeden t).kopf.f) l' Γ' Λ''),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l', Γ', Λx, ρ', .dann (.cons s rst) k'⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ' ≠ .logik e) := by
  constructor
  · intro l' Γ' Λx Λ'' ρ' s K hb heq e he
    rw [hhead] at heq
    cases heq
  · intro l' Γ' Λx Λ' Λ'' ρ' s rst k' hb heq e he
    rw [hhead] at heq
    cases heq

/-! ## 5. Witness declaration: one table, a writer that diverges, a `-> never` axiom -/

/-- Signature of `schreib`: one `.int 0 10` parameter, no result, holds
    the lock, may write the table. -/
def divSigW : Signatur Unit Empty Unit Empty where
  params := [.int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Signature of `lies`: no parameters, one `.int 0 100` result, holds the
    lock, writes nothing. -/
def divSigR : Signatur Unit Empty Unit Empty where
  params := []
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The witness declaration: one table `konto` of 2 slots with one
    `.int 0 100` field, guarded by the single lock `m`; `schreib` is
    `true`, `lies` is `false`; and one axiom -- the accepted `asm` shape of
    a `-> never` routine (`aerg = some .never`, writes nothing). -/
def divD : Deklaration where
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
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => divSigW | _ => divSigR
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => some .never
  aschreibt := fun _ _ => false
  agschreibt := fun _ g => nomatch g
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

/-- The two function ids: `schreib` (`true`) and `lies` (`false`). -/
def divSchreib : divD.Fn := show divD.Fn from true

def divLies : divD.Fn := show divD.Fn from false

/-- The axiom IS `-> never`: the accepted `asm` shape. -/
theorem divAx_never : divD.aerg () = some .never := by rfl

/-- End holdings of `schreib`: the lock. -/
theorem divSchreib_ende :
    (vertragVon divD divSchreib).ende = [Res.held (D := divD) ()] := by rfl

/-- The table access is allowed holding the lock. -/
theorem divDarf : darf divD () [Res.held (D := divD) ()] := by
  intro w h
  simp only [divD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ divD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- Parameters of `schreib`, by computation. -/
theorem divSchreib_params : divD.params divSchreib = [.int 0 10] := by rfl

/-- The argument of the witness run: 7 in `.int 0 10`. -/
def divRho7 : Env divD (divD.params divSchreib) :=
  divSchreib_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env divD [.int 0 10])

/-- `schreib` holds the lock: start equals end. -/
theorem divSchreib_start : Signatur.anfang divD (divD.signatur divSchreib) =
    [Res.held (D := divD) ()] := by rfl

/-- Same access right at the `schreib` end holdings. -/
theorem divDarfSchreib : darf divD () (vertragVon divD divSchreib).ende := by
  rw [divSchreib_ende]
  exact divDarf

/-- Index `0` into the two-slot table, in the `schreib` context. -/
def divIdx : Expr divD [.int 0 10] [Res.held (D := divD) ()]
    (.index (divD.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def divHundert : Expr divD [.int 0 10] [Res.held (D := divD) ()] (.int 0 100) :=
  .widen (by decide) (by decide) (.lit 100)

/-- The `schreib` write: `konto[0] := 100`. -/
def divWriteSt : Stmt divD (vertragVon divD divSchreib) false [.int 0 10]
    (vertragVon divD divSchreib).ende (vertragVon divD divSchreib).ende :=
  .assignSlot () () divIdx divHundert (by decide) divDarfSchreib

/-- The write at the lock holdings. -/
def divWriteStAt : Stmt divD (vertragVon divD divSchreib) false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()] :=
  divSchreib_ende ▸ divWriteSt

/-- The accepted diverging loop: `forever () invariant true {}` -- the
    model shape of lane 225's `never-forever` acceptance (un-leavable body,
    named `progress` assumption `()` as the exit evidence). -/
def divSchleife : Stmt divD (vertragVon divD divSchreib) false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()] :=
  .forever () .tru .nil

/-- `schreib` body: write the cap, then diverge. The `ret` is unreachable
    but well-typed -- exactly the accepted `-> never`-shaped body. -/
def divRumpfW :
    Endblock divD (vertragVon divD divSchreib) false [.int 0 10]
      [Res.held (D := divD) ()] :=
  .cons divWriteStAt (.cons divSchleife (.ret .empty (by rfl)))

/-- `lies` holds the lock: start equals end. -/
theorem divLies_start : Signatur.anfang divD (divD.signatur divLies) =
    [Res.held (D := divD) ()] := by rfl

/-- Index `0` in the `lies` body context, at the start holdings. -/
def divIdxBodyR : Expr divD [] (Signatur.anfang divD (divD.signatur divLies))
    (.index (divD.count ())) :=
  divLies_start ▸
    (.widen (by decide) (by decide) (.lit 0) :
      Expr divD [] [Res.held (D := divD) ()] (.index (divD.count ())))

/-- `lies` locks the table in its body context. -/
theorem divDarfBodyR :
    darf divD () (Signatur.anfang divD (divD.signatur divLies)) := by
  rw [divLies_start]
  exact divDarf

/-- `lies` body: return `konto[0]`. -/
def divRumpfR :
    Endblock divD (vertragVon divD divLies) false []
      (Signatur.anfang divD (divD.signatur divLies)) :=
  .ret (.val (.slot () () divIdxBodyR divDarfBodyR)) (by rfl)

/-- The program: `schreib` writes then diverges, `lies` reads; every
    contract `true` (nothing is claimed beyond the divergence shapes). -/
def divP : Programm divD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | true => divSchreib_start ▸ divRumpfW
    | false => divLies_start ▸ divRumpfR

/-- The witness oracle: the never-axiom keeps the world, answers raw `0`
    (which never fits `never`); no registers, nothing visible. -/
def divO : Orakel divD where
  wirkt := fun _ σ _ => (σ, 0)
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- The start memory: both slots read `0`. -/
def divSp0 : Speicher divD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Start slot value: `0`. -/
end Gabbro.Grammatik.Zielsatz
