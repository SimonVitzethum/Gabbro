import Grammatik.Logik.WP.Regeln3
import Grammatik.Speichermodell.Atomar.AtomarSem

/-!
# GabbroV over the semantics of the user's obligation

The user's logic obligation of the goal theorem (`NutzerPflichtA`, `Spec.lean`) is stated over `execEndHA`: machine
G with the environment's lock moves `U` at every acquire, the release check `freiH` of every lock invariant, and the
atomic environment `A` at every read. This file is the weakest-precondition calculus over THAT semantics -- exact,
like `WP/Kern.lean`, and with the same structural rules; the loops reuse the generic invariant rules (`execStmtHA`
runs the same `traverseLauf`/`retryLauf`/`foreverLauf`). Every proof of the obligation can follow the program with it.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section HA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- The weakest precondition of a statement over `execStmtHA`. -/
def wpSA {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    Prop :=
  Q (execStmtHA S O U A passes R s σ ρ)

/-- The weakest precondition of a block over `execBlockHA`. -/
def wpBA {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    Prop :=
  Q (execBlockHA S O U A passes R b σ ρ)

/-- The weakest precondition of a body over `execEndHA`. -/
def wpEA {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    Prop :=
  Q (execEndHA S O U A passes R e σ ρ)

/-- **Exactness.** -/
theorem wpEA_exakt {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (Q : EndAusgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) : wpEA S O U A passes R e Q σ ρ ↔ Q (execEndHA S O U A passes R e σ ρ) := Iff.rfl

/-! ## Sequence and binding -/

def weiterBA {Λ' Λ'' : List (Res D)} (rest : Block D V l Γ Λ' Λ'') (Q : Ausgang V l Γ → Prop) :
    Ausgang V l Γ → Prop
  | .ok σ' ρ' => wpBA S O U A passes R rest Q σ' ρ'
  | o => Q o

theorem wpBA_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.cons s rest) Q σ ρ ↔ wpSA S O U A passes R s (weiterBA S O U A passes R rest Q) σ ρ := by
  unfold wpBA wpSA
  simp only [execBlockHA]
  cases execStmtHA S O U A passes R s σ ρ <;> rfl

def weiterEA {Λ' : List (Res D)} (rest : Endblock D V l Γ Λ') (Q : EndAusgang V l Γ → Prop) :
    Ausgang V l Γ → Prop
  | .ok σ' ρ' => wpEA S O U A passes R rest Q σ' ρ'
  | .zurueck σ' v => Q (.zurueck σ' v)
  | .why σ' r => Q (.why σ' r)
  | .leave h σ' ρ' => Q (.leave h σ' ρ')
  | .next h σ' ρ' => Q (.next h σ' ρ')
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpEA_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.cons s rest) Q σ ρ ↔ wpSA S O U A passes R s (weiterEA S O U A passes R rest Q) σ ρ := by
  unfold wpEA wpSA
  simp only [execEndHA]
  cases execStmtHA S O U A passes R s σ ρ <;> rfl

theorem wpBA_nil {Λ : List (Res D)} (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (Block.nil (D := D) (V := V) (l := l) (Λ := Λ)) Q σ ρ ↔ Q (.ok σ ρ) := Iff.rfl

theorem wpBA_bind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (rest : Block D V l (τ :: Γ) Λ Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.bind e rest) Q σ ρ ↔
      wpBA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A σ Λ e.orte)
        (.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ) := Iff.rfl

theorem wpEA_bind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.bind e rest) Q σ ρ ↔
      wpEA S O U A passes R rest (fun eo => Q eo.schrumpf) (leseA A σ Λ e.orte)
        (.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ) := Iff.rfl

/-! ## Branches, returns, locks, narrowing, checks -/

theorem wpSA_ite {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.ite c t e) Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) then
        wpBA S O U A passes R t Q (leseA A σ Λ c.orte) ρ
      else wpBA S O U A passes R e Q (leseA A σ Λ c.orte) ρ := by
  unfold wpSA wpBA
  simp only [execStmtHA]
  rw [apply_ite Q]

theorem wpSA_ret {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.ret e hΛ) Q σ ρ ↔
      Q (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) := Iff.rfl

theorem wpEA_ret {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) (Q : EndAusgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.ret e hΛ) Q σ ρ ↔
      Q (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) := Iff.rfl

/-- **`locks L { body }`**: the body runs from the environment's move of the acquire world; every exit passes the
    release check of `L`'s invariant. -/
theorem wpSA_locks {Λ : List (Res D)} (L : D.Lock) (h : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wpSA S O U A passes R (.locks L h body) Q σ ρ ↔
      wpBA S O U A passes R body (fun o => Q (freiH S L o)) ((U L σ).nimmt L) ρ := Iff.rfl

theorem wpBA_narrow {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.narrow e lo' hi' sonst rest) Q σ ρ ↔
      if h : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
          (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi' then
        wpBA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A σ Λ e.orte)
          (.cons ⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
      else wpEA S O U A passes R sonst (fun eo => Q eo.zuAusgang) (leseA A σ Λ e.orte) ρ := by
  unfold wpBA wpEA
  simp only [execBlockHA]
  rw [apply_dite Q]

theorem wpBA_check {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.check c sonst rest) Q σ ρ ↔
      if wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) then
        wpBA S O U A passes R rest Q (leseA A σ Λ c.orte) ρ
      else wpEA S O U A passes R sonst (fun eo => Q eo.zuAusgang) (leseA A σ Λ c.orte) ρ := by
  unfold wpBA wpEA
  simp only [execBlockHA]
  rw [apply_ite Q]

/-! ## Calls -/

def bindRufBA {Λ' Λ'' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) Λ' Λ'') (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpBA S O U A passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why _ r => keinGrund hr r
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

theorem wpBA_bindCall {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.bindCall f args he hp hr rest) Q σ ρ ↔
      bindRufBA S O U A passes R he hr rest Q ρ
        (R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)) := by
  unfold wpBA
  simp only [execBlockHA]
  cases R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | ok σ' v => rfl
  | why _ r => exact (Fin.cast hr r).elim0
  | logik e => rfl
  | hardware e => rfl

theorem wpBA_bindCall_spez {Sp : Spez D} (hR : Erfuellt Sp R) {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ)
    (h : ∀ out, Sp f (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) out →
      bindRufBA S O U A passes R he hr rest Q ρ out) :
    wpBA S O U A passes R (.bindCall f args he hp hr rest) Q σ ρ :=
  (wpBA_bindCall S O U A passes R f args he hp hr rest Q σ ρ).2 (h _ (hR f _ _))

/-- **The call statement `f(args);`**, exactly. -/
theorem wpSA_call {Λ : List (Res D)} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0) (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wpSA S O U A passes R (.call f args hp hr) Q σ ρ ↔
      Q (rufZuAusgang hr ρ
        (R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ))) := by
  unfold wpSA
  simp only [execStmtHA]
  cases R f (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) <;> rfl

/-! ## The loops, through the generic invariant rules -/

theorem wpSA_traverse {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (Q : Ausgang V l Γ → Prop)
    (I : List (Wert D (.index (D.count t))) → World D → Env D Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (hStart : I (alleIndizes (D.count t)) σ ρ)
    (hEnde : ∀ σ ρ, I [] σ ρ → Q (if wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true
      then .ok (leseA A σ Λ inv.orte) ρ else .logik .schleife))
    (hBruch : ∀ k ks σ ρ, I (k :: ks) σ ρ →
      wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false → Q (.logik .schleife))
    (hSchritt : ∀ k ks σ ρ, I (k :: ks) σ ρ →
      wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true →
      wpBA S O U A passes R body
        (TraverseSchritt (fun σ ρ => (leseA A σ Λ inv.orte, wahr? (eval (leseA A σ Λ inv.orte) inv
          (leseA A σ Λ inv.orte) ρ))) Q I ks)
        (leseA A σ Λ inv.orte) (.cons k ρ)) :
    wpSA S O U A passes R (.traverse t inv body) Q σ ρ :=
  traverse_regel _ _ Q I hEnde hBruch hSchritt _ σ ρ hStart

theorem wpSA_retry {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop) (σ : World D)
    (ρ : Env D Γ) (hStart : I n σ ρ)
    (hFertig : ∀ n σ ρ, I n σ ρ → wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = true →
      Q (.ok (leseA A σ Λ bis.orte) ρ))
    (hUeber : ∀ σ ρ, I 0 σ ρ → wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = false →
      wpBA S O U A passes R ueberlauf Q (leseA A σ Λ bis.orte) ρ)
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ →
      wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = false →
      wpBA S O U A passes R body (PassSchritt Q I n) (leseA A σ Λ bis.orte) ρ) :
    wpSA S O U A passes R (.retry n bis body ueberlauf) Q σ ρ :=
  retry_regel _ _ _ Q I hFertig hUeber hSchritt n σ ρ hStart

theorem wpSA_forever {Λ : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (hStart : I passes σ ρ) (hNull : ∀ σ ρ, I 0 σ ρ → Q (.hardware (.fortschritt a)))
    (hBruch : ∀ n σ ρ, I (n + 1) σ ρ →
      wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false → Q (.logik .schleife))
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ →
      wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true →
      wpBA S O U A passes R body (PassSchritt Q I n) (leseA A σ Λ inv.orte) ρ) :
    wpSA S O U A passes R (.forever a inv body) Q σ ρ :=
  forever_regel a _ _ Q I hNull hBruch hSchritt passes σ ρ hStart

end HA

end Gabbro.Grammatik.WP
