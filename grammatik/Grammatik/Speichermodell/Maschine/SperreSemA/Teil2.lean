module
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil2a

public import Grammatik.Speichermodell.Atomar.AtomarSem
public import Grammatik.Speichermodell.Maschine.SperreSemA.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section StufenA
variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semHA_dannRetry {Λ Λ'' : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.retry n bis body ueber) rest) k) σ ρ =
      semHA S O U A passes R (.wieder n bis body ueber (.dann rest k)) σ ρ := by
  rw [semHA_dann_cons]
  rfl

/-- A block `.nil` in front of a residue changes nothing. -/
theorem weiterHA_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (o : Ausgang V l Γ) :
    weiterHA S O U A passes R (.dann .nil k) o = weiterHA S O U A passes R k o := by
  cases o <;> rfl

/-- The spent `retry` (corrected 2026-09-13): `if bis {} else { overflow }`. -/
theorem semHA_wiederUeber {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.wieder 0 bis body ueber k) σ ρ =
      semHA S O U A passes R (.dann (.cons (.ite bis .nil ueber) .nil) k) σ ρ := by
  cases hb : wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) with
  | true =>
      rw [semHA_ite S O U A passes R bis .nil ueber .nil k σ ρ true hb]
      show weiterHA S O U A passes R k (retryLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A bis)
        (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseBA A bis σ ρ).2 = true := hb
      simp only [retryLauf, hl, if_true]
      rfl
  | false =>
      rw [semHA_ite S O U A passes R bis .nil ueber .nil k σ ρ false hb]
      show weiterHA S O U A passes R k (retryLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A bis)
        (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseBA A bis σ ρ).2 = false := hb
      simp only [retryLauf, hl, Bool.false_eq_true, if_false]
      show _ = weiterHA S O U A passes R (.dann .nil k) (execBlockHA S O U A passes R ueber (leseBA A bis σ ρ).1 ρ)
      rw [weiterHA_dannLeer]

theorem semHA_wiederWeiter {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = true) :
    semHA S O U A passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semHA S O U A passes R k (leseA A σ Λ bis.orte) ρ := by
  have hl : (leseBA A bis σ ρ).2 = true := hw
  show weiterHA S O U A passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterHA S O U A passes R k (.ok _ ρ)
  simp only [retryLauf, hl, if_true]
  rfl

theorem semHA_wiederSchritt {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ) = false) :
    semHA S O U A passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semHA S O U A passes R (.dann body (.wiederRest n bis body ueber k)) (leseA A σ Λ bis.orte) ρ := by
  have hl : (leseBA A bis σ ρ).2 = false := hw
  show weiterHA S O U A passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterHA S O U A passes R (.wiederRest n bis body ueber k)
      (execBlockHA S O U A passes R body (leseBA A bis σ ρ).1 ρ)
  simp only [retryLauf, hl, Bool.false_eq_true, if_false]
  cases execBlockHA S O U A passes R body (leseBA A bis σ ρ).1 ρ <;> rfl

theorem semHA_wiederFort {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.wiederRest n bis body ueber k) σ ρ =
      semHA S O U A passes R (.wieder n bis body ueber k) σ ρ := by rfl

theorem semHA_dannForever {Λ Λ'' : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.forever a inv body) rest) k) σ ρ =
      semHA S O U A passes R (.ewig a passes inv body (.dann rest k)) σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_ewigWeiter {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true) :
    semHA S O U A passes R (.ewig a (n + 1) inv body k) σ ρ =
      semHA S O U A passes R (.dann body (.ewigRest a n inv body k)) (leseA A σ Λ inv.orte) ρ := by
  have hl : (leseBA A inv σ ρ).2 = true := hw
  show weiterHA S O U A passes R k (foreverLauf a _ _ (n + 1) σ ρ) =
    weiterHA S O U A passes R (.ewigRest a n inv body k)
      (execBlockHA S O U A passes R body (leseBA A inv σ ρ).1 ρ)
  simp only [foreverLauf, hl, Bool.true_eq_false, if_false]
  cases execBlockHA S O U A passes R body (leseBA A inv σ ρ).1 ρ <;> rfl

theorem semHA_ewigFort {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ewigRest a n inv body k) σ ρ =
      semHA S O U A passes R (.ewig a n inv body k) σ ρ := by rfl

/-! ### The exits `leave` and `next` -/

theorem semHA_leaveTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = true) :
    semHA S O U A passes R (.dann (.cons (.leave h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semHA S O U A passes R k (leseA A σ Λ inv.orte) ρ := by
  have hl : (leseBA A inv σ ρ).2 = true := hw
  rw [semHA_dann_cons]
  show weiterHA S O U A passes R k (if (leseBA A inv σ ρ).2 = true then _ else _) = _
  rw [if_pos hl]
  rfl

theorem semHA_nextTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semHA S O U A passes R (.dann (.cons (.next h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semHA S O U A passes R (.trav t inv body is k) σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_leaveVerbrauch {Λ Λx : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (σm : World D) (hsm : σm = leseA A σ Λ mass.orte)
    (m' : Int) (hm' : (eval σm mass σm ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor)
    (hw : wahr? (eval (leseA A σm Λ inv.orte) inv (leseA A σm Λ inv.orte) ρ) = true) :
    semHA S O U A passes R (.dann (.cons (.leave h) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      semHA S O U A passes R k ((leseA A σm Λ inv.orte)) ρ := by
  rw [semHA_dann_cons]
  show weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.leave h σ (.cons i ρ)) = _
  simp only [weiterHA, hsm, hm', hfall, if_true]
  have hl : (leseBA A inv σm ρ).2 = true := hw
  simp only [hl, if_true]

theorem semHA_nextVerbrauch {Λ Λx : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int)
    (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Nat) (vor : Int) (k : GRest D V l Γ Λ)
    (restb : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (σm : World D) (hsm : σm = leseA A σ Λ mass.orte)
    (m' : Int) (hm' : (eval σm mass σm ρ).n = m')
    (hfall : 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor) :
    semHA S O U A passes R (.dann (.cons (.next h) restb)
      (.verbrauchRest t member edge inv bound mass body rest vor k)) σ (.cons i ρ) =
      semHA S O U A passes R (.verbrauch t member edge inv bound mass body rest k) σm ρ := by
  rw [semHA_dann_cons]
  show weiterHA S O U A passes R (.verbrauchRest t member edge inv bound mass body rest vor k)
      (.next h σ (.cons i ρ)) = _
  simp only [weiterHA, hsm, hm', hfall, if_true, laufA]

theorem semHA_leaveWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semHA S O U A passes R (.dann (.cons (.leave h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semHA S O U A passes R k σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_nextWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semHA S O U A passes R (.dann (.cons (.next h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semHA S O U A passes R (.wieder n bis body ueber k) σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_leaveEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semHA S O U A passes R (.dann (.cons (.leave h) rest) (.ewigRest a n inv body k)) σ ρ =
      semHA S O U A passes R k σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_nextEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semHA S O U A passes R (.dann (.cons (.next h) rest) (.ewigRest a n inv body k)) σ ρ =
      semHA S O U A passes R (.ewig a n inv body k) σ ρ := by
  rw [semHA_dann_cons]
  rfl

theorem semHA_peelDann {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (b : Block D V true Γ Λ1 Λ2) (k : GRest D V true Γ Λ2)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) rest) (.dann b k)) σ ρ =
      semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semHA_dann_cons, semHA_dann_cons]
  cases x <;> rfl

theorem semHA_peelSchrumpf {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty}
    (rest : Block D V true (τ :: Γ) Λ Λ1) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D (τ :: Γ)) (h : true = true) (x : Bool) :
    semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) rest) (.schrumpf k)) σ ρ =
      semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ.tail := by
  rw [semHA_dann_cons, semHA_dann_cons]
  cases x <;> rfl

/-- **A `leave`/`next` out of a `locks` body releases through the check.** -/
theorem semHA_peelFrei {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) (hi : S.inv L σ.speicher = true) :
    semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) (σ.gibt L) ρ := by
  rw [semHA_dann_cons, semHA_dann_cons]
  cases x
  · show weiterHA S O U A passes R k (freiH S L (.next h σ ρ)) =
      weiterHA S O U A passes R k (.next h (σ.gibt L) ρ)
    simp only [freiH, hi, if_true]
  · show weiterHA S O U A passes R k (freiH S L (.leave h σ ρ)) =
      weiterHA S O U A passes R k (.leave h (σ.gibt L) ρ)
    simp only [freiH, hi, if_true]

/-- **A `leave`/`next` out of a `locks` body where the invariant fails
    predicts `logik schleife`.** -/
theorem semHA_peelFrei_falsch {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) (hi : S.inv L σ.speicher = false) :
    semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      .logik .schleife := by
  rw [semHA_dann_cons]
  cases x
  · show weiterHA S O U A passes R k (freiH S L (.next h σ ρ)) = _
    simp only [freiH, hi, Bool.false_eq_true, if_false]
    exact weiterHA_logik S O U A passes R k _
  · show weiterHA S O U A passes R k (freiH S L (.leave h σ ρ)) = _
    simp only [freiH, hi, Bool.false_eq_true, if_false]
    exact weiterHA_logik S O U A passes R k _

theorem semHA_peelAbbruch {Γ : Ctx} {Λ Λ1 Λk : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (k : GRest D V true Γ Λk)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) rest) (.abbruch k)) σ ρ =
      semHA S O U A passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semHA_dann_cons, semHA_dann_cons]
  cases x <;> rfl

/-- The `else` residue after a reason answer (`.abbruch (.schrumpf k)`)
    means the end block's outcome, the reason dropped, continued by `k`. -/
theorem semHA_alsBlock_schrumpf {Λ Λk : List (Res D)} {τ : Ty} (e : Endblock D V l (τ :: Γ) Λ)
    (k : GRest D V l Γ Λk) (σ : World D) (ρ : Env D (τ :: Γ)) :
    semHA S O U A passes R (.dann e.alsBlock.2 (.abbruch (.schrumpf k))) σ ρ =
      weiterHA S O U A passes R k (execEndHA S O U A passes R e σ ρ).schrumpf.zuAusgang := by
  rw [semHA_alsBlock]
  cases execEndHA S O U A passes R e σ ρ <;> rfl

/-! ### Returns -/

end StufenA
end Gabbro.Grammatik
