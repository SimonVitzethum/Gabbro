import Grammatik.Logik.WP.Regeln

/-!
# GabbroV over machine G: the remaining composite constructs

Locks, `breaking`, the three loops at the statement level (each with its invariant rule phrased through the body's
weakest precondition), `match` over options and over reasons, `check`, the foreign body's binding, and the end-block
forms of binding, call, `narrow` and `check`. Leaves (writes, register and transition statements, returns) need no
rule of their own: their weakest precondition is `Q` of the outcome they produce, which `simp only [wpS, execStmt]`
writes out.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Regeln2

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- `locks L { body }`: the body runs with `L` taken; every outcome gives `L` back. -/
theorem wpS_locks {Λ : List (Res D)} (L : D.Lock) (h : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ)) (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wpS O passes R (.locks L h body) Q σ ρ ↔
      wpB O passes R body (fun o => Q (o.mapWelt (·.gibt L))) (σ.nimmt L) ρ := Iff.rfl

/-- `match o { Some(k) => p, None => a }`. -/
theorem wpS_onOption {Λ Λ' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ)
    (hSome : ∀ k, eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = some k →
      wpB O passes R p (fun x => Q x.schrumpf) (σ.lese Λ o.orte) (.cons k ρ))
    (hNone : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = none → wpB O passes R a Q (σ.lese Λ o.orte) ρ) :
    wpS O passes R (.onOption o p a) Q σ ρ := by
  unfold wpS
  simp only [execStmt]
  cases h : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
  | some k => exact hSome k h
  | none => exact hNone h

/-- The arms of a `match` over a reason: the arm of reason `i`. -/
def wpGrund {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (i : Fin n) (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execGrund O passes R arms i σ ρ)

/-- The arm of reason `0` is the first block. -/
theorem wpGrund_null {Λ Λ' : List (Res D)} {n : Nat} (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
    (h : 0 < n + 1) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpGrund O passes R (.cons b rest) ⟨0, h⟩ Q σ ρ ↔ wpB O passes R b Q σ ρ := Iff.rfl

/-- The arm of reason `i + 1` is the arm of reason `i` among the rest. -/
theorem wpGrund_succ {Λ Λ' : List (Res D)} {n : Nat} (b : Block D V l Γ Λ Λ') (rest : GrundArms D V l Γ Λ Λ' n)
    (i : Nat) (h : i + 1 < n + 1) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpGrund O passes R (.cons b rest) ⟨i + 1, h⟩ Q σ ρ ↔
      wpGrund O passes R rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ Q σ ρ := Iff.rfl

/-- `match r { … }` over a reason. -/
theorem wpS_onWhy {Λ Λ' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n)) (arms : GrundArms D V l Γ Λ Λ' n)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpS O passes R (.onWhy r arms) Q σ ρ ↔
      wpGrund O passes R arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ) Q (σ.lese Λ r.orte) ρ := Iff.rfl

/-- **`traverse` at the statement level**: the invariant rule with the pass phrased through the body. -/
theorem wpS_traverse {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (Q : Ausgang V l Γ → Prop)
    (I : List (Wert D (.index (D.count t))) → World D → Env D Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (hStart : I (alleIndizes (D.count t)) σ ρ)
    (hEnde : ∀ σ ρ, I [] σ ρ → Q (if wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true
      then .ok (σ.lese Λ inv.orte) ρ else .logik .schleife))
    (hBruch : ∀ k ks σ ρ, I (k :: ks) σ ρ → wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false →
      Q (.logik .schleife))
    (hSchritt : ∀ k ks σ ρ, I (k :: ks) σ ρ → wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true →
      wpB O passes R body
        (TraverseSchritt (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
          Q I ks)
        (σ.lese Λ inv.orte) (.cons k ρ)) :
    wpS O passes R (.traverse t inv body) Q σ ρ :=
  traverse_regel _ _ Q I hEnde hBruch hSchritt _ σ ρ hStart

/-- **`retry` at the statement level.** -/
theorem wpS_retry {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (ueberlauf : Block D V l Γ Λ Λ) (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop) (σ : World D)
    (ρ : Env D Γ) (hStart : I n σ ρ)
    (hFertig : ∀ n σ ρ, I n σ ρ → wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true →
      Q (.ok (σ.lese Λ bis.orte) ρ))
    (hUeber : ∀ σ ρ, I 0 σ ρ → wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false →
      wpB O passes R ueberlauf Q (σ.lese Λ bis.orte) ρ)
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ → wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false →
      wpB O passes R body (PassSchritt Q I n) (σ.lese Λ bis.orte) ρ) :
    wpS O passes R (.retry n bis body ueberlauf) Q σ ρ :=
  retry_regel _ _ _ Q I hFertig hUeber hSchritt n σ ρ hStart

/-- **`forever` at the statement level.** -/
theorem wpS_forever {Λ : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (hStart : I passes σ ρ)
    (hNull : ∀ σ ρ, I 0 σ ρ → Q (.hardware (.fortschritt a)))
    (hBruch : ∀ n σ ρ, I (n + 1) σ ρ → wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false →
      Q (.logik .schleife))
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ → wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true →
      wpB O passes R body (PassSchritt Q I n) (σ.lese Λ inv.orte) ρ) :
    wpS O passes R (.forever a inv body) Q σ ρ :=
  forever_regel a _ _ Q I hNull hBruch hSchritt passes σ ρ hStart

/-- `check c else { … }; rest`. -/
theorem wpB_check {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (.check c sonst rest) Q σ ρ ↔
      if wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) then wpB O passes R rest Q (σ.lese Λ c.orte) ρ
      else wpE O passes R sonst (fun eo => Q eo.zuAusgang) (σ.lese Λ c.orte) ρ := by
  unfold wpB wpE
  simp only [execBlock]
  rw [apply_ite Q]

/-- `let x = g(args); rest` over a foreign body: what its answer leads to. -/
theorem wpB_bindAxiom {Λ Λ' : List (Res D)} {τ : Ty} (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (he : D.aerg a = some τ) (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ) (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (hAntwort : ∀ σ' v, axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = (σ', some v) →
      wpB O passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ))
    (hKeine : ∀ σ', axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = (σ', none) →
      Q (.hardware (.annahme a))) :
    wpB O passes R (.bindAxiom a args he hw hg hd hgd rest) Q σ ρ := by
  unfold wpB
  simp only [execBlock]
  cases h : axiomAntwort O a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk σ' ov =>
    cases ov with
    | some v => exact hAntwort σ' v h
    | none => exact hKeine σ' h

/-! ## End-block forms -/

/-- `let x = e;` ending in an end block. -/
theorem wpE_bind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (rest : Endblock D V l (τ :: Γ) Λ)
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpE O passes R (.bind e rest) Q σ ρ ↔
      wpE O passes R rest (fun eo => Q eo.schrumpf) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := Iff.rfl

/-- What a binding call makes of the callee's outcome, in an end block. -/
def bindRufE {Λ' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ) (hr : D.gruende f = 0)
    (rest : Endblock D V l (τ :: Γ) Λ') (Q : EndAusgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpE O passes R rest (fun eo => Q eo.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why _ r => keinGrund hr r
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- `let x = f(args);` in an end block, exactly. -/
theorem wpE_bindCall {Λ : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Endblock D V l (τ :: Γ) (nach D f Λ)) (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpE O passes R (.bindCall f args he hp hr rest) Q σ ρ ↔
      bindRufE O passes R he hr rest Q ρ
        (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)) := by
  unfold wpE
  simp only [execEnd]
  cases R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => rfl
  | why _ r => exact (Fin.cast hr r).elim0
  | logik e => rfl
  | hardware e => rfl

/-- `let x = f(args);` in an end block, against a specification. -/
theorem wpE_bindCall_spez {S : Spez D} (hR : Erfuellt S R) {Λ : List (Res D)} {τ : Ty} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) (rest : Endblock D V l (τ :: Γ) (nach D f Λ)) (Q : EndAusgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ)
    (h : ∀ out, S f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) out →
      bindRufE O passes R he hr rest Q ρ out) :
    wpE O passes R (.bindCall f args he hp hr rest) Q σ ρ :=
  (wpE_bindCall O passes R f args he hp hr rest Q σ ρ).2 (h _ (hR f _ _))

end Regeln2

end Gabbro.Grammatik.WP
