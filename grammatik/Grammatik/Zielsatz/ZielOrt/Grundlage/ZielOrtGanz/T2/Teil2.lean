module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T1
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

def PrueftG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) : Prop :=
    (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
        (inv : Expr D Γ Λ .bool)
        (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
        (ks : List (Wert D (.index (D.count tb))))
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .trav tb inv body ks k⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
        (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ)
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λx : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
        (inv : Expr D Γ Λ .bool)
        (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
        (is : List (Wert D (.index (D.count tb))))
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
        (rest : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λx Λ)
        (hl : true = true) (i : Wert D (.index (D.count tb))),
      (M.faeden t).kopf.rest = ⟨true, .index (D.count tb) :: Γ, Λx, .cons i ρ,
        .dann (.cons (.leave hl) rest) (.travRest tb inv body is k)⟩ →
      wahr? (eval ((M.weltVon t).lese Λ inv.orte) inv ((M.weltVon t).lese Λ inv.orte) ρ) = true) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ)
        (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
        (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons s K)⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ ≠ .logik e) ∧
    (∀ (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (ρ : Env D Γ)
        (s : Stmt D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
        (rst : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ' Λ'')
        (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
      s.istBlatt = true → (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.cons s rst) k⟩ →
      ∀ e : Logik D, execStmt O passes keinRuf s (M.weltVon t) ρ ≠ .logik e)

/-- **No thread of `M` is stopped at a `logik` check of G.** -/
def KeinLogikHaltG (O : Orakel D) (passes : Nat) (M : RufMaschineG D) : Prop :=
  ∀ t : Faden, PrueftG O passes M t

/-- A Boolean that is not `false` is `true`. -/
theorem wahr_of_nicht_falsch {b : Bool} (h : b = false → False) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

section Halt

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **A replayed thread is stopped at no `logik` check**, when every body
    meets `KeineLogik`. -/
theorem fadenR_prueft (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hL : ∀ f, KeineLogik P passes Q f) {M : RufMaschineG D} (t : Faden)
    (hF : FadenR P O passes Q (M.faeden t) (M.weltVon t)) : PrueftG O passes M t := by
  have hK := hF.1
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_trav_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_ewig_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semV_leaveTrav_falsch
    rw [eval_gleichAuf inv (fun _ h => hok.2.2.1 h) (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    obtain ⟨_, hss, _⟩ := okG_ende_cons hok
    have h' := blatt_logik P s hb hss hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    show zErg (execEnd (orakelAus O HA) passes (rufAusL H) (.cons s K) σ ρ) = _
    simp only [execEnd, h', zErg]
  · obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hK hr
    obtain ⟨_, hss, _⟩ := okG_dann_cons hok
    have h' := blatt_logik P s hb hss hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    rw [semV_dann_cons, h']
    exact weiterZ_logik _ _ _ _ e

end Halt
/-! ## 7. G moves at every `logik` check

  `KeinLogikHaltG` says the checks PASS. Here the step itself: at every
  place where a rule of G tests a `logik` condition, the rule fires -- given
  the one side condition every reading rule of G carries, `HeldGenau` of
  the head's static holdings (a lock-bookkeeping fact, not a `logik` check;
  `rufG_haelt_statisch` proves its `⊆` half on every reachable machine, the
  `⊇` half is not proved -- `THEOREM-MAP.md` §13.5). -/

/-- **Thread `t` of `M` stands at a `logik` check of G**: a `traverse`
    boundary, a `forever` boundary with budget left, a `leave` out of a
    `traverse` body, or a `state` transition at the head of an end block or
    of a block. -/
def AnPruefungG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count tb))))
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .trav tb inv body ks k⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ)
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ewig a (n + 1) inv body k⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λx : List (Res D)) (ρ : Env D Γ) (tb : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λ Λ)
      (is : List (Wert D (.index (D.count tb))))
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) true (.index (D.count tb) :: Γ) Λx Λ)
      (hl : true = true) (i : Wert D (.index (D.count tb))),
    (M.faeden t).kopf.rest = ⟨true, .index (D.count tb) :: Γ, Λx, .cons i ρ,
      .dann (.cons (.leave hl) rest) (.travRest tb inv body is k)⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ) (lo hi : Int) (tb : D.Tab)
      (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi) (i : Expr D Γ Λ (.index (D.count tb)))
      (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi) (he : D.erlaubt tb fl von nach = true)
      (hw : (vertragVon D (M.faeden t).kopf.f).schreibt tb = true) (hL : darf D tb Λ)
      (K : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
    (M.faeden t).kopf.rest =
      ⟨l, Γ, Λ, ρ, .ende (.cons (.shift tb fl hτ i von nach hn he hw hL) K)⟩) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (ρ : Env D Γ) (lo hi : Int) (tb : D.Tab)
      (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi) (i : Expr D Γ Λ (.index (D.count tb)))
      (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi) (he : D.erlaubt tb fl von nach = true)
      (hw : (vertragVon D (M.faeden t).kopf.f).schreibt tb = true) (hL : darf D tb Λ)
      (rst : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ'')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ''),
    (M.faeden t).kopf.rest =
      ⟨l, Γ, Λ, ρ, .dann (.cons (.shift tb fl hτ i von nach hn he hw hL) rst) k⟩)

/-- A `state` transition whose outcome is no `logik` outcome is an `ok`
    step that only adds accesses to the trace. -/
theorem uebergang_ok {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (O : Orakel D) (passes : Nat) (tb : D.Tab) (fl : D.Feld tb) (hτ : D.typ tb fl = .int lo hi)
    (i : Expr D Γ Λ (.index (D.count tb))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
    (he : D.erlaubt tb fl von nach = true) (hw : V.schreibt tb = true) (hL : darf D tb Λ)
    (W : World D) (ρ : Env D Γ)
    (hno : ∀ e : Logik D, execStmt O passes keinRuf
      (Stmt.shift (l := l) tb fl hτ i von nach hn he hw hL) W ρ ≠ .logik e) :
    ∃ σ' ρ', execStmt O passes keinRuf (Stmt.shift (l := l) tb fl hτ i von nach hn he hw hL)
      W ρ = .ok σ' ρ' ∧ Erw W σ' := by
  cases hx : execStmt O passes keinRuf (Stmt.shift (l := l) tb fl hτ i von nach hn he hw hL)
      W ρ with
  | ok σ' ρ' =>
      refine ⟨σ', ρ', rfl, ?_⟩
      simp only [execStmt] at hx
      split at hx
      · cases hx
        exact (Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)
      · cases hx
  | logik e => exact absurd hx (hno e)
  | _ =>
      simp only [execStmt] at hx
      split at hx <;> cases hx


end Gabbro.Grammatik
