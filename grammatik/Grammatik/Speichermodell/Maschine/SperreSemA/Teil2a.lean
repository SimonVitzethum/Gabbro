module

public import Grammatik.Speichermodell.Atomar.AtomarSem
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section StufenA
variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semHA_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.onWhy r arms) rest) k) σ ρ =
      semHA S O U A passes R (.dann (grundWahlG arms (eval (leseA A σ Λ r.orte) r (leseA A σ Λ r.orte) ρ))
        (.dann rest k)) (leseA A σ Λ r.orte) ρ := by
  rw [semHA_dann_cons]
  simp only [execStmtHA]
  rw [execGrundHA_wahlW S O U A passes R arms]
  rfl

theorem semHA_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.breaking i body) rest) k) σ ρ =
      semHA S O U A passes R (.dann body (.dann rest k)) σ ρ := by
  rw [semHA_dann_cons]
  rfl

/-- **The acquire**: the body runs from the environment's move of the
    acquire world, and the release marker `frei L` carries the release
    check. -/
theorem semHA_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ =
      semHA S O U A passes R (.dann body (.frei L (.dann rest k))) ((U L σ).nimmt L) ρ := by
  rw [semHA_dann_cons]
  rfl

/-- **The release**, where the invariant holds. -/
theorem semHA_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) (hi : S.inv L σ.speicher = true) :
    semHA S O U A passes R (.frei L k) σ ρ = semHA S O U A passes R k (σ.gibt L) ρ := by
  show weiterHA S O U A passes R k (freiH S L (.ok σ ρ)) = _
  simp only [freiH, hi, if_true]
  rfl

/-- **A release where the invariant fails predicts `logik schleife`.** -/
theorem semHA_frei_falsch {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) (hi : S.inv L σ.speicher = false) :
    semHA S O U A passes R (.frei L k) σ ρ = .logik .schleife := by
  show weiterHA S O U A passes R k (freiH S L (.ok σ ρ)) = _
  simp only [freiH, hi, Bool.false_eq_true, if_false]
  exact weiterHA_logik S O U A passes R k _

theorem semHA_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semHA S O U A passes R (.schrumpf k) σ (.cons v ρ) = semHA S O U A passes R k σ ρ := by rfl

theorem semHA_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ende (.bind e rest)) σ ρ =
      semHA S O U A passes R (.ende rest) (leseA A σ Λ e.orte)
        (.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ) := by
  show zErgG (execEndHA S O U A passes R (.bind e rest) σ ρ) =
    zErgG (execEndHA S O U A passes R rest _ _)
  simp only [execEndHA]
  rw [zErgG_schrumpf]

theorem semHA_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.bind e rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ e.orte)
        (.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ) := by rfl

theorem semHA_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi') :
    semHA S O U A passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, h.1, h.2⟩ ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, dif_pos h]
  rfl

theorem semHA_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi')) :
    (semHA S O U A passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ).folgt
      (semHA S O U A passes R (.dann sonst.alsBlock.2 (.abbruch k)) (leseA A σ Λ e.orte) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, dif_neg h]
  rw [semHA_alsBlock]
  exact ZErgG.folgt_refl _

theorem semHA_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) = true) :
    semHA S O U A passes R (.dann (.check c sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest k) (leseA A σ Λ c.orte) ρ := by
  rw [semHA_dann]
  simp only [execBlockHA, hw, if_true]
  rfl

theorem semHA_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) = false) :
    (semHA S O U A passes R (.dann (.check c sonst rest) k) σ ρ).folgt
      (semHA S O U A passes R (.dann sonst.alsBlock.2 (.abbruch k)) (leseA A σ Λ c.orte) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hw, Bool.false_eq_true, if_false]
  rw [semHA_alsBlock]
  exact ZErgG.folgt_refl _

theorem semHA_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k))
        ((leseA A σ Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (leseA A σ Λ (.inr g :: neuE.orte)) neuE (leseA A σ Λ (.inr g :: neuE.orte))
            (.cons ((leseA A σ Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((leseA A σ Λ (.inr g :: neuE.orte)).globs g) ρ) := by rfl

theorem semHA_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ).x
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semHA S O U A passes R (.dann (.float op a b lo hi rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semHA S O U A passes R (.dann (.floatLit q lo hi rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (leseA A σ Λ e.orte) e
      (leseA A σ Λ e.orte) ρ).n) = some v) :
    semHA S O U A passes R (.dann (.floatOf e lo hi rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ e.orte) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x = some v) :
    semHA S O U A passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ e.orte) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x = none) :
    (semHA S O U A passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ).folgt
      (semHA S O U A passes R (.dann sonst.alsBlock.2 (.abbruch k)) (leseA A σ Λ e.orte) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hn]
  rw [semHA_alsBlock]
  exact ZErgG.folgt_refl _

/-! ### Loops -/

theorem semHA_dannTrav {Λ Λ'' : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.traverse t inv body) rest) k) σ ρ =
      semHA S O U A passes R (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_travNext {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true) :
    semHA S O U A passes R (.trav t inv body (i :: is) k) σ ρ =
      semHA S O U A passes R (.dann body (.travRest t inv body is k)) (leseA A σ Λ inv.orte)
        (.cons i ρ) := by
  have hl : (leseBA A inv σ ρ).2 = true := hw
  show weiterHA S O U A passes R k (traverseLauf _ _ (i :: is) σ ρ) =
    weiterHA S O U A passes R (.travRest t inv body is k)
      (execBlockHA S O U A passes R body (leseBA A inv σ ρ).1 (.cons i ρ))
  simp only [traverseLauf, hl, Bool.true_eq_false, if_false]
  cases execBlockHA S O U A passes R body (leseBA A inv σ ρ).1 (.cons i ρ) <;> rfl

theorem semHA_travFort {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.travRest t inv body is k) σ (.cons i ρ) =
      semHA S O U A passes R (.trav t inv body is k) σ ρ := by rfl

theorem semHA_travDone {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true) :
    semHA S O U A passes R (.trav t inv body [] k) σ ρ =
      semHA S O U A passes R k (leseA A σ Λ inv.orte) ρ := by
  have hl : (leseBA A inv σ ρ).2 = true := hw
  show weiterHA S O U A passes R k (traverseLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
    (leseBA A inv) [] σ ρ) = weiterHA S O U A passes R k (.ok _ ρ)
  simp only [traverseLauf, hl, if_true]
  rfl

/-! ### Consuming runs -/

theorem semHA_dannVerbrauch {Λ Λ'' : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons
      (.consumeTraverse t member edge inv bound mass body) rest) k) σ ρ =
      semHA S O U A passes R (.verbrauch t member edge inv bound mass body
        ((D.count t).toNat + bound.toNat + 1) (.dann rest k)) σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_verbrauchWeiter {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true)
    (σ₂ : World D) (v : Wert D (.index (D.count t))) (b : Bool) (m : Int)
    (hsel : verbrauchSelA A t member edge (leseBA A inv σ ρ).1 ρ = (σ₂, some v, b))
    (hm : (eval (leseA A σ₂ Λ mass.orte) mass (leseA A σ₂ Λ mass.orte) ρ).n = m) :
    semHA S O U A passes R (.verbrauch t member edge inv bound mass body (rest + 1) k) σ ρ =
      semHA S O U A passes R (.dann body
        (.verbrauchRest t member edge inv bound mass body rest m k))
        (leseA A σ₂ Λ mass.orte) (.cons v ρ) := by
  have hl : (leseBA A inv σ ρ).2 = true := hw
  show weiterHA S O U A passes R k (verbrauchLauf _ _ (rest + 1) σ ρ) =
    weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest m k)
      (execBlockHA S O U A passes R body (leseA A σ₂ Λ mass.orte) (.cons v ρ))
  simp only [verbrauchLauf, hl, Bool.true_eq_false, if_false, hsel]
  cases execBlockHA S O U A passes R body (leseA A σ₂ Λ mass.orte) (.cons v ρ) with
  | ok σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n ∧
          (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
      · simp only [hfall, if_false]
  | next _ σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n ∧
          (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
      · simp only [hfall, if_false]
  | leave _ σ' ρ' =>
      by_cases hfall : 0 ≤ (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n ∧
          (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n ≤ bound ∧
          (eval (leseA A σ' Λ mass.orte) mass (leseA A σ' Λ mass.orte) ρ'.tail).n < m
      · simp only [hfall, if_true]
        by_cases hc' : (leseBA A inv (leseA A σ' Λ mass.orte) ρ'.tail).2 = true
        · simp only [hc', if_true]
        · simp only [show (leseBA A inv (leseA A σ' Λ mass.orte) ρ'.tail).2 = false from by
            cases h' : (leseBA A inv (leseA A σ' Λ mass.orte) ρ'.tail).2 with
            | false => rfl
            | true => exact absurd h' hc', if_false]
      · simp only [hfall, if_false]
  | zurueck σ' v => rfl
  | why σ' r => rfl
  | logik e => rfl
  | hardware e => rfl

theorem semHA_verbrauchLeer {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true)
    (σ₂ : World D)
    (hsel : verbrauchSelA A t member edge (leseBA A inv σ ρ).1 ρ = (σ₂, none, false)) :
    semHA S O U A passes R (.verbrauch t member edge inv bound mass body (rest + 1) k) σ ρ =
      semHA S O U A passes R k σ₂ ρ := by
  have hl : (leseBA A inv σ ρ).2 = true := hw
  show weiterHA S O U A passes R k (verbrauchLauf _ _ (rest + 1) σ ρ) =
    weiterHA S O U A passes R k (.ok σ₂ ρ)
  simp only [verbrauchLauf, hl, hsel, Bool.true_eq_false, if_false]

theorem semHA_verbrauchFort {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (σ₁ : World D) (hs₁ : σ₁ = leseA A σ Λ mass.orte)
    (m' : Int) (hm' : (eval σ₁ mass σ₁ ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor) :
    semHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      σ (.cons i ρ) =
      semHA S O U A passes R (.verbrauch t member edge inv bound mass body rest k) σ₁ ρ := by
  show weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.ok σ (.cons i ρ)) =
    weiterHA S O U A passes R (.verbrauch t member edge inv bound mass body rest k) (.ok σ₁ ρ)
  simp only [weiterHA, hs₁, hm', hfall, if_true, laufA]

end StufenA
end Gabbro.Grammatik
