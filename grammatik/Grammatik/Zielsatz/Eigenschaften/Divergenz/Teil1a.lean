module

public import Grammatik.Zielsatz.Eigenschaften.NeverAsm
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

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


end Gabbro.Grammatik.Zielsatz
