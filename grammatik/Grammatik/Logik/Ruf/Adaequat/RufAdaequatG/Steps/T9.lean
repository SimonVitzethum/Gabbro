/- Part 9 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9Basis
import all Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T9Basis
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.Steps.T8
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section SemSchritt

variable (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem sem_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semR O passes (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ =
      semR O passes (.dann (.narrow e lo' hi' sonst rest) k) σ ρ := by
  rw [semR_alsBlock]
  rw [semR_dann O passes (.narrow e lo' hi' sonst rest), execBlock_narrow]
  unfold narrowWeiter
  rw [dif_neg h, nachA_zuAusgang]
  rfl

theorem sem_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semR O passes (.dann rest k) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.check c sonst rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hw, if_true]

theorem sem_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    semR O passes (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ c.orte) ρ =
      semR O passes (.dann (.check c sonst rest) k) σ ρ := by
  rw [semR_alsBlock]
  rw [semR_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  rw [nachA_zuAusgang]
  rfl

theorem sem_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
      semR O passes (.dann (.exchange g neuE hw hL rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock]
  rw [nachA_schrumpf]

theorem sem_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) =
      semR O passes (.dann (.float op a b lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semR O passes (.dann rest (.schrumpf k)) σ (.cons v ρ) =
      semR O passes (.dann (.floatLit q lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.dann (.floatOf e lo hi rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semR O passes (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) =
      semR O passes (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semR_dann, semR_dann]
  simp only [execBlock, hv]
  rw [nachA_schrumpf]

theorem sem_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    semR O passes (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ e.orte) ρ =
      semR O passes (.dann (.floatNarrow e lo hi sonst rest) k) σ ρ := by
  rw [semR_alsBlock]
  rw [semR_dann]
  simp only [execBlock, hn]
  rw [nachA_zuAusgang]
  rfl

theorem sem_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende (.ret (l := l) e hperm)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by rfl

theorem sem_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semR O passes (.ende (.cons (.ret e hperm) rest)) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  simp only [semR, execEnd, execStmt, endErg]

theorem sem_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semR O passes (.dann (.cons (.ret e hperm) rest) k) σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  rw [semR_dann, nachA_cons]
  rfl

end SemSchritt
theorem faeden_upd (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    (⟨sp, rufUpdateG m f z, la, st⟩ : RufMaschineG D).faeden f = z :=
  rufUpdateG_self m f z

theorem weltVon_upd (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    (⟨sp, rufUpdateG m f z, la, st⟩ : RufMaschineG D).weltVon f = sp.welt z.spur := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]

/-- What one step of thread `f` does to a covered frame: either the frame
    stays on top with a covered residue and the same frame result (up to
    the trace), or it pops, logging a `rueck` whose world and value ARE the
    frame result (up to the trace). -/
def ErhaltG (O : Orakel D) (passes : Nat) (A : D.Lock → Prop) (M M' : RufMaschineG D)
    (f : Faden) (z : RufFadenG D) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D z.kopf.f) l Γ Λ) : Prop :=
  (∃ (l' : Bool) (Γ' : Ctx) (Λ' : List (Res D)) (ρ' : Env D Γ')
      (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (sp : List (Ereignis D)),
      M'.faeden f = ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, sp, z.log⟩ ∧
      RestG A r' ∧ (semR O passes r' (M'.weltVon f) ρ').gleich (semR O passes r (M.weltVon f) ρ)) ∨
  (∃ (v : ErgVal D (D.erg z.kopf.f)) (s1 : World D),
      (M'.faeden f).log = RufEreignisF.rueck z.kopf.f z.kopf.rho v z.kopf.s0 s1 :: z.log ∧
      (semR O passes r (M.weltVon f) ρ).gleich (.zurueck s1 v))

set_option hygiene false in
/-- Refute a step whose head shape the covered residue cannot have. -/
macro "widerlege" h:ident : tactic => `(tactic| (
  rw [hR] at $h:ident
  cases $h:ident
  first
  | exact absurd hcov.dann_cons_art (by simp [Stmt.gArt, Stmt.blattArt])
  | exact absurd hcov.ende_cons_art (by simp [Stmt.gArt, Stmt.blattArt])
  | (obtain ⟨_, hbo, _⟩ := hcov.dann_inv; simp [Block.ohneOrakel] at hbo; done)
  | (obtain ⟨⟨_, hbw⟩, _, _⟩ := hcov.dann_inv; cases hbw; done)
  | (obtain ⟨hew, _⟩ := hcov.ende_inv; cases hew; done)
  | cases hcov))

theorem armWahlG_G {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    ArmsG A mr arms → BlockG A mr (armWahlG arms v).2.1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => armWahlG_G rest _ h.cons_inv.2

theorem grundWahlG_G {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    GrundArmsG A mr arms → BlockG A mr (grundWahlG arms r)
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => h.cons_inv.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => grundWahlG_G rest _ h.cons_inv.2

theorem armWahlG_G' {V : Vertrag D} {A : D.Lock → Prop} {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option Ty} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast D.Fn D.passt c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : ArmsG A mr arms) :
    BlockG A mr b := by
  have h0 := armWahlG_G arms v h
  rw [hw] at h0
  exact h0

theorem armWahlG_ohne' {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option Ty} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast D.Fn D.passt c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.ohneOrakel = true) :
    b.ohneOrakel = true := by
  have h0 := armWahlG_ohneOrakel arms v h
  rw [hw] at h0
  exact h0


end Gabbro.Grammatik
