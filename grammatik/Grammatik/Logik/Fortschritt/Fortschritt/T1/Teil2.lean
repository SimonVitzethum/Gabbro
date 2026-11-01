module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG
public import Grammatik.Logik.Fortschritt.Fortschritt.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **A leaf that is no return, reason or abrupt exit** ends normally with
    a trace extended by accesses, or answers hardware, or answers `logik`. -/
theorem blatt_fall {O : Orakel D} (hO : GutO O) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAbschluss = false) (W : World D) (ρ : Env D Γ) (hh : HeldIn Λ (offen W.spur)) :
    (∃ σ' ρ', execStmt O passes keinRuf s W ρ = .ok σ' ρ' ∧ Erw W σ') ∨
    (∃ h, execStmt O passes keinRuf s W ρ = .hardware h) ∨
    (∃ e, execStmt O passes keinRuf s W ρ = .logik e) := by
  cases hx : execStmt O passes keinRuf s W ρ with
  | ok σ' ρ' =>
      refine Or.inl ⟨σ', ρ', rfl, ?_⟩
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          simp only [execStmt] at hx
          split at hx
          · rename_i σ1 v hax
            simp only [Ausgang.ok.injEq] at hx
            obtain ⟨rfl, -⟩ := hx
            have h1 : (O.wirkt a ((W.lese Λ args.orte).fragt (.inl a))
                (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ)).1 = σ1 := by
              have := congrArg Prod.fst hax
              simpa [axiomAntwort] using this
            rw [← h1]
            refine ((Erw.lese W Λ args.orte).trans (Erw.fragt _ _)).trans (axiom_erw hO a _ _ hd hgd ?_)
            show HeldIn Λ (offen _)
            rw [((Erw.lese W Λ args.orte).trans (Erw.fragt _ _)).offen]
            exact hh
          · cases hx
      | _ =>
          first
          | (simp only [Stmt.istAbschluss, Bool.true_eq_false] at ha; done)
          | (simp only [Stmt.istBlatt, Bool.false_eq_true] at hb; done)
          | exact BlattG.erw O passes keinRuf (by constructor) W σ' ρ ρ' hx
  | hardware h => exact Or.inr (Or.inl ⟨h, rfl⟩)
  | logik e => exact Or.inr (Or.inr ⟨e, rfl⟩)
  | zurueck σ' v =>
      exfalso
      cases s <;> simp only [Stmt.istBlatt, Stmt.istAbschluss, Bool.false_eq_true, Bool.true_eq_false] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx
  | why σ' r =>
      exfalso
      cases s <;> simp only [Stmt.istBlatt, Stmt.istAbschluss, Bool.false_eq_true, Bool.true_eq_false] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx
  | leave hl σ' ρ' =>
      exfalso
      cases s <;> simp only [Stmt.istBlatt, Stmt.istAbschluss, Bool.false_eq_true, Bool.true_eq_false] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx
  | next hl σ' ρ' =>
      exfalso
      cases s <;> simp only [Stmt.istBlatt, Stmt.istAbschluss, Bool.false_eq_true, Bool.true_eq_false] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx

/-! ## 5. The case analysis -/

/-- The lock a `locks` head takes. -/
def Stmt.sperreVon {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Option D.Lock
  | .locks L _ _ => some L
  | _ => none

def Block.sperreVon {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Option D.Lock
  | .cons s _ => s.sperreVon
  | _ => none

def GRest.kopfSperre {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option D.Lock
  | .dann b _ => b.sperreVon
  | _ => none

theorem anSperre_kopf {M : RufMaschineG D} {t : Faden} {L : D.Lock} (h : AnSperre M t L) :
    (M.faeden t).kopf.rest.2.2.2.2.kopfSperre = some L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hh⟩ := h
  rw [hh]
  rfl

/-- **The float range checks of G pass for thread `t` of `M`** (2026-09-15, verdict F1): at a
    head `gleit`, float literal or `gleitVon`, the result lies in its declared range at the
    thread's world. Where it does not, G has no rule, and the sequential semantics answers
    `logik bereich` -- which the user's obligation excludes (`fadenS_bereich`). -/
def BereichG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (op : GleitOp)
      (l1 h1 l2 h2 lo hi : Int × Int) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.float op a b lo hi rest) k⟩ →
    gleitPasst lo hi (gleitRechne op
      (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) a
        ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x
      (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) b
        ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x) ≠ none) ∧
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (q lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.floatLit q lo hi rest) k⟩ →
    gleitPasst lo hi (bruch q) ≠ none) ∧
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (l1 h1 : Int)
      (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.floatOf e lo hi rest) k⟩ →
    gleitPasst lo hi (gleitAusInt
      (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n) ≠ none)


end Gabbro.Grammatik
