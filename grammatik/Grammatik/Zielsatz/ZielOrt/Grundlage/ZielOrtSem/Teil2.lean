module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section SemZ
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
variable {l : Bool} {Γ : Ctx}

theorem semZ_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semZ O passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) =
      semZ O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  exact semZ_dann O passes R b _ _ _

theorem semZ_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ =
      semZ O passes R (.dann (.cons (.onWhy r arms) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt]
  rw [execGrund_wahlW O passes R arms]

theorem semZ_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann body (.dann rest k)) σ ρ =
      semZ O passes R (.dann (.cons (.breaking i body) rest) k) σ ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt]

theorem semZ_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    (semZ O passes R (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ).gleich
      (semZ O passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ) := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons, semZ_dann]
  simp only [execStmt]
  exact nachZ_frei O passes R _ L _

theorem semZ_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) :
    semZ O passes R k (σ.gibt L) ρ = semZ O passes R (.frei L k) σ ρ := by rfl

theorem semZ_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semZ O passes R k σ ρ = semZ O passes R (.schrumpf k) σ (.cons v ρ) := by rfl

theorem semZ_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semZ O passes R (.ende (.bind e rest)) σ ρ := by
  simp only [semZ, execEnd]
  rw [zErg_schrumpf]

theorem semZ_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) =
      semZ O passes R (.dann (.bind e rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock]
  rw [nachZ_schrumpf]

theorem semZ_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) =
      semZ O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semZ_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_pos h, nachZ_schrumpf, semZ_dann]

/-- An end block run as a block in front of any continuation means the end
    block (it never ends normally). -/
theorem semZ_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann e.alsBlock.2 (.abbruch k)) σ ρ = semZ O passes R (.ende e) σ ρ := by
  rw [semZ_dann, Endblock.execBlock_alsBlock, nachZ_zuAusgang]
  rfl

theorem semZ_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semZ O passes R (.ende sonst) (σ.lese Λ e.orte) ρ =
      semZ O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semZ_dann O passes R (.narrow e lo' hi' sonst rest), execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_neg h, nachZ_zuAusgang]
  rfl

theorem semZ_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semZ O passes R (.dann rest k) (σ.lese Λ c.orte) ρ =
      semZ O passes R (.dann (.check c sonst rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hw, if_true]

theorem semZ_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semZ O passes R (.ende sonst) (σ.lese Λ c.orte) ρ =
      semZ O passes R (.dann (.check c sonst rest) k) σ ρ := by
  rw [semZ_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachZ_zuAusgang]
  rfl

theorem semZ_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semZ O passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock]
  rw [nachZ_schrumpf]

theorem semZ_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semZ O passes R (.dann (.float op a b lo hi rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semZ O passes R (.dann (.floatLit q lo hi rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semZ O passes R (.dann (.floatOf e lo hi rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semZ O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semZ O passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semZ_dann, semZ_dann]
  simp only [execBlock, hv]
  rw [nachZ_schrumpf]

theorem semZ_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semZ O passes R (.ende sonst) (σ.lese Λ e.orte) ρ =
      semZ O passes R (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semZ_dann]
  simp only [execBlock, hn]
  rw [nachZ_zuAusgang]
  rfl

theorem semZ_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by rfl

theorem semZ_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semZ, execEnd, execStmt, zErg]

theorem semZ_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semZ O passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semZ_dann, nachZ_cons]
  rfl

/-! ### Calls: the answer of the handler decides -/

theorem semZ_rufDann {Λ Λ'' : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l Γ (nach D g Λ) Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semZ O passes R (.dann (.cons (.call g args hp hr) rest) k) σ ρ =
      semZ O passes R (.dann rest k) σ1 ρ := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt, h]
  rfl

theorem semZ_ruf {Λ : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D V l Γ (nach D g Λ)) (σ : World D) (ρ : Env D Γ)
    (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semZ O passes R (.ende (.cons (.call g args hp hr) rest)) σ ρ =
      semZ O passes R (.ende rest) σ1 ρ := by
  simp only [semZ, execEnd, execStmt, h]

theorem semZ_bindCall {Λ Λ' : List (Res D)} {τ : Ty} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (σ1 : World D) (v1 : ErgVal D (D.erg g))
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .ok σ1 v1) :
    semZ O passes R (.dann (.bindCall g args he hp hr rest) k) σ ρ =
      semZ O passes R (.dann rest (.schrumpf k)) σ1 (.cons (ergWert he v1) ρ) := by
  rw [semZ_dann]
  simp only [execBlock, h]
  rw [nachZ_schrumpf, semZ_dann]

theorem semZ_rufDann_logik {Λ Λ'' : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l Γ (nach D g Λ) Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (e : Logik D)
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .logik e) :
    semZ O passes R (.dann (.cons (.call g args hp hr) rest) k) σ ρ = .logik e := by
  rw [semZ_dann O passes R (.cons _ rest), nachZ_cons]
  simp only [execStmt, h]
  rfl

theorem semZ_ruf_logik {Λ : List (Res D)} (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Endblock D V l Γ (nach D g Λ)) (σ : World D) (ρ : Env D Γ) (e : Logik D)
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .logik e) :
    semZ O passes R (.ende (.cons (.call g args hp hr) rest)) σ ρ = .logik e := by
  simp only [semZ, execEnd, execStmt, h]
  rfl

theorem semZ_bindCall_logik {Λ Λ' : List (Res D)} {τ : Ty} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    (hp : RufPasst D V (D.signatur g) Λ) (hr : D.gruende g = 0)
    (rest : Block D V l (τ :: Γ) (nach D g Λ) Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (e : Logik D)
    (h : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
      .logik e) :
    semZ O passes R (.dann (.bindCall g args he hp hr rest) k) σ ρ = .logik e := by
  rw [semZ_dann]
  simp only [execBlock, h]
  rfl

end SemZ

/-! ## 4. The residues the replay follows -/

/-- A residue in the fragment (`kOk`) whose blocks read, and whose calls
    rely on contracts, only inside the footprint `S`. Loop shims and
    `wartetSonst` are outside. -/
def GRest.okZ (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.kOk = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.kOk = true ∧ blockOrteP P b ⊆ S ∧ k.okZ P S
  | _, _, _, .schrumpf k => k.okZ P S
  | _, _, _, .frei _ k => k.okZ P S
  | _, _, _, .wartet b k => b.kOk = true ∧ blockOrteP P b ⊆ S ∧ k.okZ P S
  | _, _, _, .trav .. => False
  | _, _, _, .travRest .. => False
  | _, _, _, .wieder .. => False
  | _, _, _, .wiederRest .. => False
  | _, _, _, .ewig .. => False
  | _, _, _, .ewigRest .. => False
  | _, _, _, .wartetSonst .. => False
  | _, _, _, .abbruch k => k.okZ P S
  | _, _, _, .leer => True

theorem teil_append {α : Type} {a b S : List α} (h : a ++ b ⊆ S) : a ⊆ S ∧ b ⊆ S :=
  ⟨fun _ hx => h (List.mem_append_left _ hx), fun _ hx => h (List.mem_append_right _ hx)⟩

theorem teil_von_append {α : Type} {a b S : List α} (ha : a ⊆ S) (hb : b ⊆ S) : a ++ b ⊆ S :=
  fun _ hx => (List.mem_append.mp hx).elim (fun h => ha h) (fun h => hb h)

section OkZ

variable {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okZ_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okZ P S) :
    s.kOk = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okZ P S := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.kOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okZ_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okZ P S) :
    s.kOk = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okZ P S := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.kOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

/-- The chosen arm of `onTag` is in the fragment and reads inside the arms. -/
theorem armWahlG_orteP {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    blockOrteP P (armWahlG arms v).2.1 ⊆ armsOrteP P arms
  | _, .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩ => fun _ hx => List.mem_append_left _ hx
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩ => fun _ hx =>
      List.mem_append_right _ (armWahlG_orteP rest _ hx)

theorem armWahlG_orteP' {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) {c : Option (Int × Int)}
    {b : Block D V l (ArmCtx Γ c) Λ Λ'} {nutz : Nutzlast c}
    (hw : armWahlG arms v = ⟨c, b, nutz⟩) : blockOrteP P b ⊆ armsOrteP P arms := by
  have h := armWahlG_orteP (P := P) arms v
  rw [hw] at h
  exact h

theorem grundWahlG_orteP {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    blockOrteP P (grundWahlG arms r) ⊆ grundArmsOrteP P arms
  | _, .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩ => fun _ hx => List.mem_append_left _ hx
  | _, .cons _ rest, ⟨_ + 1, _⟩ => fun _ hx =>
      List.mem_append_right _ (grundWahlG_orteP rest _ hx)

end OkZ

/-! ## CUTS:

  What is proved: agreement on a footprint (`GleichAuf`) and the locality
  of `eval`/`evalArgs`/`evalErg`, of slot/global/byte writes and of every
  leaf of the fragment (`blatt_lokal`); the frame semantics `semZ` with
  its residue step lemmas for every rule of the fragment, including the
  call lemmas for a normal answer and for a logic answer; the residue
  predicate `GRest.okZ` with its inversions.

  What is NOT here: loops, abrupt exits, the error channel, indirect calls,
  axioms and the oracle forms have no step lemma (`semZ` gives their
  residues no meaning); `ziel_ort` does not need them because
  `programmImFragment` keeps every reachable residue inside the fragment.
-/

#print axioms Gabbro.Grammatik.blatt_lokal
#print axioms Gabbro.Grammatik.semZ_locks
#print axioms Gabbro.Grammatik.semZ_bindCall
#print axioms Gabbro.Grammatik.semZ_rufDann_logik

end Gabbro.Grammatik
