/-
  File:    Grammatik/Zielsatz/Divergenz.lean -- divergence of accepted never-bodies.

  SCOPE (lane 231, TODO §-1 wave B, pure Lean). Lane 225 pinned the CHECKER
  acceptance of `-> never` bodies (asm with no `out`, un-leavable `forever`
  with `per_pass bounded` + diverging `on_exceeded`, tail calls) with zero
  behavior change. This file is the MODEL half for exactly those shapes,
  nothing wider: divergence PROVED from the declaration, never asserted.

  * §1 `forever`: a loop whose body cannot leave or return (`NoExit`) and
    whose invariant holds everywhere (`InvWahr`) ends in
    `hardware (fortschritt a)` at every budget -- the named `progress`
    assumption `a` the writer declared (the model's `on_exceeded` exit).
    Never `logik`, never a return value: it terminates-or-diverges as
    declared, and the divergence leg is proved.
  * §2 `asm`: a `-> never` foreign body (an axiom with `aerg = some .never`,
    Syntax.lean §14) has an empty answer class (`antwortLeer_never`), so no
    oracle answer fits and the call never continues: `hardware (annahme a)`
    with the oracle's declared-effects world. Never `logik`, never `ok`.
  * §3 bridge to `KeinLogikHaltG` (ZielOrtGanz.lean): a thread at a
    true-invariant `forever` head passes the loop check G performs there,
    and a thread at a never-axiom head passes the leaf checks (it is no
    leaf). The leg is EXTENDED, never weakened: `Spec.lean` untouched.
  * §4 witness: `divD`/`divP` (one table `konto`, one lock, a writer that
    writes then diverges in `forever`, a reader, a `-> never` axiom) with a
    reached F-machine run that changes memory and stands at the `forever`,
    and `divergent_body_zeuge` instantiating every premise JOINTLY.
    Non-degenerate: `konto[0]` goes `0 -> 100` on the run.

  No `sorry`, no `axiom`, no `native_decide`, no `unsafe`. No premise whose
  type is `Prop` itself. Every premise is used by its proof.
-/
import Grammatik.Zielsatz.NeverAsm
import Grammatik.RufMaschineF
import Grammatik.ZielOrtGanz

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
    invariant (here `.wahr`); THAT it holds is proved per program, never
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
      rw [if_neg (by simp [hI])]
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
    execStmt O passes R ((.forever a .wahr .nil : Stmt D V l Γ Λ Λ)) σ ρ =
      .hardware (.fortschritt a) := by
  have hNo : NoExit (D := D) (V := V) (Γ := Γ) (Λ := Λ) O passes R
      (.nil : Block D V true Γ Λ Λ) :=
    fun σ ρ => Or.inl ⟨_, _, rfl⟩
  have hInv : InvWahr (D := D) (Γ := Γ) (Λ := Λ) (.wahr : Expr D Γ Λ .bool) Λ :=
    fun _ _ => rfl
  exact forever_noexit_divergiert O passes R a .wahr .nil σ ρ hNo hInv

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

/-! ## 4. Bridge to `KeinLogikHaltG`: divergence serves the leg -/

/-- **Bridge, `forever`**: a thread standing at a true-invariant `forever`
    head takes its G step (`ewigWeiter`, RufMaschineG.lean) -- given the
    lock-bookkeeping side conditions every reading rule of G carries
    (`HeldIn` of the head holdings, the read-world spur equation). The
    `hw` premise of that rule is `PrueftG`'s loop clause at this head, and
    for `.wahr` it holds by computation: the diverging loop of §2 is
    therefore no `logik` stop -- it extends the leg `keinLogikHalt`, never
    weakens it (`Spec.lean` untouched). -/
theorem ewig_wahr_schreitet {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {t : Faden}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ} {a : D.Annahme} {n : Nat}
    {k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ}
    (hhead : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) (.wahr : Expr D Γ Λ .bool)
      (.nil : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ) k⟩)
    (hspur : ((M.weltVon t).lese Λ ((.wahr : Expr D Γ Λ .bool)).orte).spur =
      (M.faeden t).spur)
    (hHeld : HeldIn Λ (offen (M.faeden t).spur)) :
    ∃ M', RufSchrittG P O passes M t M' := by
  refine ⟨_, RufSchrittG.ewigWeiter M t l Γ Λ a n (.wahr : Expr D Γ Λ .bool)
    (.nil : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ) k ρ hhead
    ((M.weltVon t).lese Λ ((.wahr : Expr D Γ Λ .bool)).orte) rfl rfl [] ?_ hHeld⟩
  simp [hspur]

/-- **Bridge, never-axiom heads**: a thread at a `bindAxiom` head passes
    both leaf checks of `PrueftG` (clauses 4-5, ZielOrtGanz.lean, restated)
    -- vacuously, since a call is no leaf (`istBlatt` holds only of `Stmt`
    leaves, and `bindAxiom` is a `Block` constructor, so the rival head
    equation discriminates). For a `-> never` axiom this head is
    additionally the named stop `nieZurueck` (`kopf_nieZurueck_never`,
    NeverAsm.lean), never `hardware` (`kein_hardware_an_never`): the
    divergence of §3 and the leg cohere. Stated for every `bindAxiom` head
    -- the never instance is the joint witness of §5. -/
theorem nieZurueck_blatt_frei {D : Deklaration} {M : RufMaschineG D} {t : Faden}
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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
theorem divAx_never : divD.aerg () = some .never := rfl

/-- End holdings of `schreib`: the lock. -/
theorem divSchreib_ende :
    (vertragVon divD divSchreib).ende = [Res.held (D := divD) ()] := rfl

/-- The table access is allowed holding the lock. -/
theorem divDarf : darf divD () [Res.held (D := divD) ()] := by
  intro w h
  simp only [divD] at h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  have hh : w ∈ divD.braucht () := h
  rw [e] at hh ⊢
  exact List.mem_singleton.mpr rfl

/-- Parameters of `schreib`, by computation. -/
theorem divSchreib_params : divD.params divSchreib = [.int 0 10] := rfl

/-- The argument of the witness run: 7 in `.int 0 10`. -/
def divRho7 : Env divD (divD.params divSchreib) :=
  divSchreib_params.symm ▸ (.cons ⟨7, by decide, by decide⟩ .nil :
    Env divD [.int 0 10])

/-- `schreib` holds the lock: start equals end. -/
theorem divSchreib_start : Signatur.anfang divD (divD.signatur divSchreib) =
    [Res.held (D := divD) ()] := rfl

/-- Same access right at the `schreib` end holdings. -/
theorem divDarfSchreib : darf divD () (vertragVon divD divSchreib).ende := by
  rw [divSchreib_ende]
  exact divDarf

/-- Index `0` into the two-slot table, in the `schreib` context. -/
def divIdx : Expr divD [.int 0 10] [Res.held (D := divD) ()]
    (.index (divD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- The cap value `100` in range. -/
def divHundert : Expr divD [.int 0 10] [Res.held (D := divD) ()] (.int 0 100) :=
  .weiter (by decide) (by decide) (.lit 100)

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
  .forever () .wahr .nil

/-- `schreib` body: write the cap, then diverge. The `ret` is unreachable
    but well-typed -- exactly the accepted `-> never`-shaped body. -/
def divRumpfW :
    Endblock divD (vertragVon divD divSchreib) false [.int 0 10]
      [Res.held (D := divD) ()] :=
  .cons divWriteStAt (.cons divSchleife (.ret .keine (by rfl)))

/-- `lies` holds the lock: start equals end. -/
theorem divLies_start : Signatur.anfang divD (divD.signatur divLies) =
    [Res.held (D := divD) ()] := rfl

/-- Index `0` in the `lies` body context, at the start holdings. -/
def divIdxBodyR : Expr divD [] (Signatur.anfang divD (divD.signatur divLies))
    (.index (divD.count ())) :=
  divLies_start ▸
    (.weiter (by decide) (by decide) (.lit 0) :
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
  .ret (.wert (.slot () () divIdxBodyR divDarfBodyR)) (by rfl)

/-- The program: `schreib` writes then diverges, `lies` reads; every
    contract `true` (nothing is claimed beyond the divergence shapes). -/
def divP : Programm divD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
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
theorem divSp0_slot :
    divSp0.slots () 0 () = (⟨0, by decide, by decide⟩ :
      Wert divD (divD.typ () ())) := rfl

/-- Thread start: thread 0 runs `lies`, thread 1 runs `schreib 7`. -/
def divInit : Faden → Σ f : divD.Fn, Env divD (divD.params f)
  | 0 => ⟨divLies, Env.nil⟩
  | _ => ⟨divSchreib, divRho7⟩

/-! ## 6. The witness run: lock, write, then the head stands at `forever` -/

/-- The start machine for the witness run. -/
def divM0F : RufMaschineF divD := RufStartF divP divSp0 divInit

/-- The lock is free at the start: every trace is empty. -/
theorem divFrei0F : RufFreiF divM0F 1 (()) := by
  intro g hne hmem
  have e : (divM0F.faeden g).spur = [] := rfl
  have hnil : offen (divM0F.faeden g).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List divD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing yet. -/
theorem divSelf0F : (() : divD.Lock) ∉ offen (divM0F.faeden 1).spur := by
  intro hmem
  have e : (divM0F.faeden 1).spur = [] := rfl
  have hnil : offen (divM0F.faeden 1).spur = [] := by rw [e]; rfl
  have h2 : (()) ∈ ([] : List divD.Lock) := hnil ▸ hmem
  exact (List.mem_nil_iff _).mp h2 |>.elim

/-- Thread 1 holds nothing, so the rank side is vacuous. -/
theorem divRang0F (K : divD.Lock) (hK : K ∈ offen (divM0F.faeden 1).spur) :
    divD.rang K < divD.rang (()) := by
  have e : (divM0F.faeden 1).spur = [] := rfl
  have hnil : offen ([] : List (Ereignis divD)) = [] := rfl
  rw [e, hnil, List.mem_nil_iff] at hK
  exact absurd hK (by decide)

/-- Step A: thread 1 takes the lock. -/
def divM1F : RufMaschineF divD :=
  ⟨divM0F.speicher,
   rufUpdateF divM0F.faeden 1
     ⟨(divM0F.faeden 1).stapel, (divM0F.faeden 1).kopf,
      Ereignis.nimmt () (offen (divM0F.faeden 1).spur) :: (divM0F.faeden 1).spur,
      (divM0F.faeden 1).log⟩,
   divM0F.lauf ++ rufEigenF 1 [Ereignis.nimmt () (offen (divM0F.faeden 1).spur)],
   divM0F.start⟩

theorem divSchrittAF :
    RufSchrittF divP divO 0 divM0F 1 divM1F := by
  unfold divM1F
  exact RufSchrittF.nimmt divM0F 1 () divSelf0F (fun K hK => divRang0F K hK)
    divFrei0F

theorem divReachAF : RufErreichbarF divP divO 0 divM0F divM1F :=
  RufErreichbarF.schritt _ _ 1 RufErreichbarF.start divSchrittAF

/-- Thread 1 holds the lock exactly after step A. -/
theorem divM1Fhaelt :
    HeldGenau [Res.held (D := divD) ()]
      (offen (divM1F.faeden 1).spur) := by
  intro L
  have eL : L = () := by cases L <;> rfl
  have eH : offen (divM1F.faeden 1).spur = [()] := rfl
  rw [eH, eL]
  constructor
  · intro hL
    have heq : Res.held (D := divD) L = Res.held (D := divD) () :=
      (List.mem_singleton.mp hL)
    cases heq
    exact List.mem_singleton.mpr rfl
  · intro hL
    have heq : L = () :=
      (List.mem_singleton.mp (eH ▸ hL))
    cases heq
    exact List.mem_singleton.mpr rfl

/-- The evaluated index: `0`. -/
def divK0 : Int := 0

/-- The evaluated cap: `100` in range. -/
def divV100 : Wert divD (.int 0 100) := ⟨100, by decide, by decide⟩

/-- Step B: thread 1 fires the writing leaf `konto[0] := 100`. The head
    after the step stands at the diverging `forever`. -/
def divM2F : RufMaschineF divD :=
  ⟨(((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
      divK0 () divV100).speicher,
   rufUpdateF divM1F.faeden 1
     ⟨(divM1F.faeden 1).stapel,
      ⟨(divM1F.faeden 1).kopf.f, (divM1F.faeden 1).kopf.rho,
       (divM1F.faeden 1).kopf.s0,
       ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
        .cons divSchleife (.ret .keine (by rfl))⟩⟩,
      (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
        (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
        divK0 () divV100).spur,
      (divM1F.faeden 1).log⟩,
   divM1F.lauf ++ rufEigenF 1
     [Ereignis.zugriff () true [Res.held (D := divD) ()]
       (divM1F.weltVon 1).haelt],
   divM1F.start⟩

theorem divSchrittBF : RufSchrittF divP divO 0 divM1F 1 divM2F := by
  have hhead : (divM1F.faeden 1).kopf.rest =
      ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
        .cons divWriteStAt
          (.cons divSchleife (.ret .keine (by rfl)))⟩ := rfl
  have hstep : (execStmt divO 0 keinRuf divWriteStAt
      (divM1F.weltVon 1) divRho7) =
      Ausgang.ok (D := divD) (V := vertragVon divD divSchreib)
        (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
          (divIdx.orte ++ divHundert.orte)).schreibSlot ()
          [Res.held (D := divD) ()] divK0 () divV100) divRho7 := rfl
  have hneu : (((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)).schreibSlot () [Res.held (D := divD) ()]
      divK0 () divV100).spur =
      [Ereignis.zugriff () true [Res.held (D := divD) ()]
        (divM1F.weltVon 1).haelt] ++ (divM1F.faeden 1).spur := rfl
  have hkn : ∀ (L : divD.Lock) (h : List divD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := divD) ()] (divM1F.weltVon 1).haelt] := by
    intro L h hm
    simp at hm
  exact RufSchrittF.blatt divM1F 1 false [.int 0 10]
    [Res.held (D := divD) ()] [Res.held (D := divD) ()]
    divWriteStAt _ divRho7 rfl hhead divM1Fhaelt _ _ _ hstep hneu hkn

theorem divReachBF : RufErreichbarF divP divO 0 divM0F divM2F :=
  RufErreichbarF.schritt _ _ 1 divReachAF divSchrittBF

/-- `divM0F` IS the start machine. -/
theorem divM0F_start : divM0F = RufStartF divP divSp0 divInit := rfl

/-- The witness run: lock, then the writing leaf -- reached from start. -/
theorem divB_erreicht :
    RufErreichbarF divP divO 0 (RufStartF divP divSp0 divInit) divM2F := by
  rw [← divM0F_start]
  exact divReachBF

/-- The final memory carries the written cap at `konto[0]`. -/
theorem divMB_slot : divM2F.speicher.slots () 0 () = divV100 := by
  have hhit := storeSlot_hit (D := divD)
    ((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
      (divIdx.orte ++ divHundert.orte)) () divK0 () divV100
  have k0 : divK0 = (0 : Int) := rfl
  have hmem : divM2F.speicher.slots () 0 () =
      ((((divM1F.weltVon 1).lese [Res.held (D := divD) ()]
        (divIdx.orte ++ divHundert.orte)).storeSlot ()
        divK0 () divV100).slots () 0 ()) := rfl
  rw [k0] at hhit
  rw [hmem, k0]
  exact hhit

/-- Memory really moved: `konto[0]` reads `100`, the start reads `0`. -/
theorem divB_schreibt : divM2F.speicher.slots () 0 () ≠
    divSp0.slots () 0 () := by
  have h100 := divMB_slot
  have h0 : divSp0.slots () 0 () =
      (⟨0, by decide, by decide⟩ : Wert divD (divD.typ () ())) := rfl
  rw [h100, h0]
  intro hcon
  have hn : (divV100.n) = ((⟨0, by decide, by decide⟩ :
      Wert divD (divD.typ () ())).n) := congrArg Zahl.n hcon
  simp [divV100] at hn

/-- After step B the head stands at the diverging `forever`. -/
theorem divM2kopf : (divM2F.faeden 1).kopf.rest =
    ⟨false, [.int 0 10], [Res.held (D := divD) ()], divRho7,
      .cons divSchleife (.ret .keine (by rfl))⟩ := rfl

/-! ## 7. The joint witness: every premise together, nothing weakened -/

/-- The remaining body after the write diverges at every budget: the write
    runs, then the `forever` answers the named assumption. -/
theorem divRest_divergiert (n : Nat) (σ : World divD) (ρ : Env divD [.int 0 10]) :
    execEnd divO n keinRuf
      (.cons divSchleife (.ret .keine (by rfl)) :
        Endblock divD (vertragVon divD divSchreib) false [.int 0 10]
          [Res.held (D := divD) ()]) σ ρ =
      .hardware (.fortschritt ()) := by
  have hF : execStmt divO n keinRuf divSchleife σ ρ = .hardware (.fortschritt ()) :=
    forever_leer_divergiert divO n keinRuf () σ ρ
  simp only [execEnd, hF]

/-- Evidence bundle: the empty body cannot exit, at any oracle and budget. -/
theorem divNoExit (O : Orakel divD) (passes : Nat)
    (R : ∀ f : divD.Fn, World divD → Env divD (divD.params f) → RufAusgang f) :
    NoExit O passes R
      (.nil : Block divD (vertragVon divD divSchreib) true [.int 0 10]
        [Res.held (D := divD) ()] [Res.held (D := divD) ()]) :=
  fun _ _ => Or.inl ⟨_, _, rfl⟩

/-- Evidence bundle: `true` holds everywhere. -/
theorem divInvWahr :
    InvWahr (.wahr : Expr divD [.int 0 10] [Res.held (D := divD) ()] .bool)
      [Res.held (D := divD) ()] :=
  fun _ _ => rfl

/-- **ZEUGE: `divergent_body_zeuge`.** All premises JOINTLY on the concrete
    non-degenerate program `divP`: a writer that writes `konto` then
    diverges in the accepted `forever` shape, a `-> never` axiom (the
    accepted `asm` shape), and a reached run that changes memory and stands
    at the `forever`. The same exit evidence proves the divergence
    (`forever_noexit_divergiert` applied to the witnessed `hNo`/`hInv`);
    the run shows it. The loop budget is `3`, not `0`: at budget `0`
    `foreverLauf` answers `hardware (fortschritt a)` by its first equation
    for EVERY loop (false guard, leavable body), so a budget-`0` conjunct
    would not depend on `hNo`/`hInv` at all. At `3` the guard is checked
    and the body run three times before the named exit (review G10).
    Nothing is weakened: the table is written
    (`divB_schreibt`), the run is reached (`divB_erreicht`), the axiom
    admits its site (`StelleOk`) and fits no answer (`AntwortLeer`). -/
theorem divergent_body_zeuge :
    ∃ (σ : World divD) (ρ : Env divD [.int 0 10]),
    ∃ (hNo : NoExit divO 3 keinRuf
          (.nil : Block divD (vertragVon divD divSchreib) true [.int 0 10]
            [Res.held (D := divD) ()] [Res.held (D := divD) ()]))
      (hInv : InvWahr (.wahr : Expr divD [.int 0 10] [Res.held (D := divD) ()] .bool)
          [Res.held (D := divD) ()]),
      execStmt divO 3 keinRuf
          ((.forever () .wahr .nil : Stmt divD (vertragVon divD divSchreib) false
            [.int 0 10] [Res.held (D := divD) ()] [Res.held (D := divD) ()])) σ ρ =
          .hardware (.fortschritt ()) ∧
      (∃ M : RufMaschineF divD,
        RufErreichbarF divP divO 0 (RufStartF divP divSp0 divInit) M ∧
        M.speicher.slots () 0 () ≠ divSp0.slots () 0 ()) ∧
      StelleOk divD (.inl ()) ∧ AntwortLeer divD (divD.aerg ()) := by
  obtain ⟨hNo, hInv⟩ : NoExit divO 3 keinRuf
      (.nil : Block divD (vertragVon divD divSchreib) true [.int 0 10]
        [Res.held (D := divD) ()] [Res.held (D := divD) ()]) ∧
      InvWahr (.wahr : Expr divD [.int 0 10] [Res.held (D := divD) ()] .bool)
        [Res.held (D := divD) ()] :=
    ⟨divNoExit divO 3 keinRuf, divInvWahr⟩
  refine ⟨divSp0.welt [], divRho7, hNo, hInv, ?_, ?_, ?_, ?_⟩
  · exact forever_noexit_divergiert (l := false) divO 3 keinRuf () .wahr .nil _ _
      hNo hInv
  · exact ⟨divM2F, divB_erreicht, divB_schreibt⟩
  · exact stelleOk_never_ax (D := divD) () divAx_never
  · exact asm_never_antwort_leer () divAx_never

/-! ## CUTS

  Proved (every premise used by its proof):
  * `foreverLauf_noexit` -- syntax-free fuel lemma: exit-free step + true
    guard gives `hardware (fortschritt a)` at every fuel.
  * `forever_noexit_divergiert`, `forever_noexit_kein_logik`,
    `forever_noexit_kein_zurueck` -- the `forever` divergence as declared,
    never `logik`, never a return.
  * `forever_leer_divergiert` -- the empty spin, no evidence premises.
  * `asm_never_antwort_leer`, `asm_never_kein_ok` -- the `-> never` axiom
    fits no answer and never continues.
  * `ewig_wahr_schreitet` -- a true-`forever` head takes its G step:
    divergence serves `KeinLogikHaltG`.
  * `nieZurueck_blatt_frei` -- a `bindAxiom` head passes both leaf checks.
  * `divRest_divergiert`, `divergent_body_zeuge` -- the joint witness on
    `divD`/`divP`: table written (`0 -> 100`), run reached, head at
    `forever`, axiom site admissible with empty answer class.

  NOT proved, named:
  * THAT a body's exits are absent / an invariant holds on a REAL program
    is writer's logic (`NoExit`/`InvWahr` are premises, proved here only for
    the witness shapes `.nil`/`.wahr`).
  * No checker acceptance (`antwortenB`, lane 225's sentences) is claimed in
    Lean: the shapes are the model's, the acceptance is the checker's.
  * The bridge concludes per-head checks/steps, not `KeinLogikHaltG`
    itself: the leg's statement (`Spec.lean`) is untouched by design.
  * `divP` carries no `HeldGenau`/progress story: the run is on the F
    machine (contracts aside, as in `ReferenzB`), the G step only as the
    one-step bridge `ewig_wahr_schreitet`.
-/

#print axioms Gabbro.Grammatik.Zielsatz.foreverLauf_noexit
#print axioms Gabbro.Grammatik.Zielsatz.forever_noexit_divergiert
#print axioms Gabbro.Grammatik.Zielsatz.forever_noexit_kein_logik
#print axioms Gabbro.Grammatik.Zielsatz.forever_noexit_kein_zurueck
#print axioms Gabbro.Grammatik.Zielsatz.forever_leer_divergiert
#print axioms Gabbro.Grammatik.Zielsatz.asm_never_antwort_leer
#print axioms Gabbro.Grammatik.Zielsatz.asm_never_kein_ok
#print axioms Gabbro.Grammatik.Zielsatz.ewig_wahr_schreitet
#print axioms Gabbro.Grammatik.Zielsatz.nieZurueck_blatt_frei
#print axioms Gabbro.Grammatik.Zielsatz.divRest_divergiert
#print axioms Gabbro.Grammatik.Zielsatz.divergent_body_zeuge

end Gabbro.Grammatik.Zielsatz
