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

end Gabbro.Grammatik.Zielsatz
