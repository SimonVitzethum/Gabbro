/-
  File:      Grammatik/Speichermodell/SperreSemA.lean
  Subject:   The frame semantics of every residue and the residue step lemmas (one per rule of
             G) for `execStmtHA`, the semantics with the atomic rely (AtomarSem.lean) -- the
             copy of SperreSem.lean §3/§4 with every sequential read through `leseA`.
             Opus lane O25b, 2026-09-26. Standalone.
-/
import Grammatik.Speichermodell.AtomarSem

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The check of a loop condition through the atomic environment (`leseB` with `leseA`). -/
def leseBA (A : AUmwelt D) {Γ : Ctx} {Λ : List (Res D)} (c : Expr D Γ Λ .bool) :
    World D → Env D Γ → World D × Bool :=
  fun σ ρ => let σ := leseA A σ Λ c.orte; (σ, wahr? (eval σ c σ ρ))

/-! ## 3. The frame semantics of every residue, with lock invariants

  `weiterHA`/`semHA` are `weiterZ`/`semV` (`ZielOrtVollSem.lean`) over
  `execStmtHA`; the one new case is the release marker `frei L`, which runs
  the release check `freiH`. -/

section WeiterA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- **How a residue continues from an outcome**, with lock invariants. -/
def weiterHA : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ →
    Ausgang V l Γ → ZErgG V
  | _, _, _, .ende e, o =>
      match o with
      | .ok σ ρ => zErgG (execEndHA S O U A passes R e σ ρ)
      | .zurueck σ v => .zurueck σ v
      | .grund σ r => .grund σ r
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .dann b k, o => weiterHA k (laufA (fun σ ρ => execBlockHA S O U A passes R b σ ρ) o)
  | _, _, _, .schrumpf k, o => weiterHA k o.schrumpf
  | _, _, _, .frei L k, o => weiterHA k (freiH S L o)
  | _, _, _, .trav _ inv body ks k, o =>
      weiterHA k (laufA (traverseLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A inv) ks) o)
  | _, _, _, .travRest _ inv body ks k, o =>
      match o with
      | .ok σ ρ =>
          weiterHA k (traverseLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A inv) ks σ
            ρ.tail)
      | .next _ σ ρ =>
          weiterHA k (traverseLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A inv) ks σ
            ρ.tail)
      | .leave _ σ ρ =>
          weiterHA k (if (leseBA A inv σ ρ.tail).2 = true then .ok (leseBA A inv σ ρ.tail).1 ρ.tail
            else .logik .schleife)
      | .zurueck σ v => weiterHA k (.zurueck σ v)
      | .grund σ r => weiterHA k (.grund σ r)
      | .logik e => weiterHA k (.logik e)
      | .hardware e => weiterHA k (.hardware e)
  | _, _, _, .wieder n bis body ueber k, o =>
      weiterHA k (laufA (retryLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A bis)
        (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) n) o)
  | _, _, _, .wiederRest n bis body ueber k, o =>
      match o with
      | .ok σ ρ => weiterHA k (retryLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A bis)
          (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) n σ ρ)
      | .next _ σ ρ => weiterHA k (retryLauf (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
          (leseBA A bis) (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) n σ ρ)
      | .leave _ σ ρ => weiterHA k (.ok σ ρ)
      | .zurueck σ v => weiterHA k (.zurueck σ v)
      | .grund σ r => weiterHA k (.grund σ r)
      | .logik e => weiterHA k (.logik e)
      | .hardware e => weiterHA k (.hardware e)
  | _, _, _, .ewig a n inv body k, o =>
      weiterHA k (laufA (foreverLauf a (fun σ ρ => execBlockHA S O U A passes R body σ ρ) (leseBA A inv) n) o)
  | _, _, _, .ewigRest a n inv body k, o =>
      match o with
      | .ok σ ρ => weiterHA k (foreverLauf a (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
          (leseBA A inv) n σ ρ)
      | .next _ σ ρ => weiterHA k (foreverLauf a (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
          (leseBA A inv) n σ ρ)
      | .leave _ σ ρ => weiterHA k (.ok σ ρ)
      | .zurueck σ v => weiterHA k (.zurueck σ v)
      | .grund σ r => weiterHA k (.grund σ r)
      | .logik e => weiterHA k (.logik e)
      | .hardware e => weiterHA k (.hardware e)
  | _, _, _, .wartet _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterHA k o
  | _, _, _, .wartetSonst _ _ _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterHA k o
  | _, _, _, .abbruch k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterHA k o

/-- The frame semantics of a residue with lock invariants: run it from `σ`,
    `ρ`. -/
def semHA {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : ZErgG V :=
  weiterHA S O U A passes R r (.ok σ ρ)

variable {l : Bool} {Γ : Ctx}

theorem execBlockHA_cons_laufA {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ : World D) (ρ : Env D Γ) :
    execBlockHA S O U A passes R (.cons s rest) σ ρ =
      laufA (fun σ ρ => execBlockHA S O U A passes R rest σ ρ) (execStmtHA S O U A passes R s σ ρ) := by
  simp only [execBlockHA]
  cases execStmtHA S O U A passes R s σ ρ <;> rfl

theorem semHA_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann b k) σ ρ =
      weiterHA S O U A passes R k (execBlockHA S O U A passes R b σ ρ) := rfl

theorem semHA_dann_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons s rest) k) σ ρ =
      weiterHA S O U A passes R (.dann rest k) (execStmtHA S O U A passes R s σ ρ) := by
  rw [semHA_dann, execBlockHA_cons_laufA]
  rfl

theorem weiterHA_logik : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Logik D), weiterHA S O U A passes R k (.logik e) = .logik e
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterHA_logik k e
  | _, _, _, .schrumpf k, e => weiterHA_logik k e
  | _, _, _, .frei _ k, e => weiterHA_logik k e
  | _, _, _, .trav _ _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .wartet _ k, e => weiterHA_logik k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterHA_logik k e
  | _, _, _, .abbruch k, e => weiterHA_logik k e

theorem weiterHA_zurueck : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (v : ErgVal D V.erg),
    (weiterHA S O U A passes R k (.zurueck σ v)).gleich (.zurueck σ v)
  | _, _, _, .ende _, _, _ => ZErgG.gleich_refl _
  | _, _, _, .dann _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .schrumpf k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .frei L k, σ, v =>
      ZErgG.gleich_trans (weiterHA_zurueck k (σ.gibt L) v) ⟨sg_gibt σ L, rfl⟩
  | _, _, _, .trav _ _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .travRest _ _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .wieder _ _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .wiederRest _ _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .ewig _ _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .ewigRest _ _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .wartet _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .wartetSonst _ _ _ k, σ, v => weiterHA_zurueck k σ v
  | _, _, _, .abbruch k, σ, v => weiterHA_zurueck k σ v

/-- A reason exit passes every residue unchanged up to the trace (the twin
    of `weiterHA_zurueck`, 2026-09-14). -/
theorem weiterHA_grund : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (r : Fin V.gruende),
    (weiterHA S O U A passes R k (.grund σ r)).gleich (.grund σ r)
  | _, _, _, .ende _, _, _ => ZErgG.gleich_refl _
  | _, _, _, .dann _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .schrumpf k, σ, r => weiterHA_grund k σ r
  | _, _, _, .frei L k, σ, r =>
      ZErgG.gleich_trans (weiterHA_grund k (σ.gibt L) r) ⟨sg_gibt σ L, rfl⟩
  | _, _, _, .trav _ _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .travRest _ _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .wieder _ _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .wiederRest _ _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .ewig _ _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .ewigRest _ _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .wartet _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .wartetSonst _ _ _ k, σ, r => weiterHA_grund k σ r
  | _, _, _, .abbruch k, σ, r => weiterHA_grund k σ r

/-- **An end block replacing a residue** (as `weiterZ_ende_folgt`). -/
theorem weiterHA_ende_folgt {Λ : List (Res D)} (k : GRest D V l Γ Λ) (eo : EndAusgang V l Γ) :
    (weiterHA S O U A passes R k eo.zuAusgang).folgt (zErgG eo) := by
  cases eo with
  | zurueck σ v => exact ZErgG.folgt_of_gleich (weiterHA_zurueck S O U A passes R k σ v)
  | grund σ r => exact ZErgG.folgt_of_gleich (weiterHA_grund S O U A passes R k σ r)
  | logik e => exact ZErgG.folgt_of_eq (weiterHA_logik S O U A passes R k e)
  | _ => exact ZErgG.folgt_sonst _

/-- `execBlockHA` of an end block run as a block (`Endblock.alsBlock`) is
    the end block's own outcome (as `Endblock.execBlock_alsBlock`). -/
theorem Endblock.execBlockHA_alsBlock :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
      execBlockHA S O U A passes R e.alsBlock.2 σ ρ = (execEndHA S O U A passes R e σ ρ).zuAusgang
  | _, _, .ret _ _, _, _ => rfl
  | _, _, .retGrund _ _, _, _ => rfl
  | _, _, .leave _, _, _ => rfl
  | _, _, .next _, _, _ => rfl
  | _, _, .cons s rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      cases execStmtHA S O U A passes R s σ ρ with
      | ok σ' ρ' => exact Endblock.execBlockHA_alsBlock rest σ' ρ'
      | _ => rfl
  | _, _, .bind e rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      rw [Endblock.execBlockHA_alsBlock rest]
      cases execEndHA S O U A passes R rest _ _ <;> rfl

/-- Past `abbruch`, an end outcome continues as without it. -/
theorem weiterHA_abbruch_zu {Λ Λk : List (Res D)} (k : GRest D V l Γ Λk) (eo : EndAusgang V l Γ) :
    weiterHA S O U A passes R (.abbruch (Λ := Λ) k) eo.zuAusgang =
      weiterHA S O U A passes R k eo.zuAusgang := by
  cases eo <;> rfl

/-- **The residue of an `else` branch** (`.dann e.alsBlock.2 (.abbruch k)`)
    means the end block's outcome continued by `k`: a `leave`/`next` in
    it reaches the loop in `k`. -/
theorem semHA_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ) (k : GRest D V l Γ Λk)
    (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann e.alsBlock.2 (.abbruch k)) σ ρ =
      weiterHA S O U A passes R k (execEndHA S O U A passes R e σ ρ).zuAusgang := by
  rw [semHA_dann, Endblock.execBlockHA_alsBlock, weiterHA_abbruch_zu]

/-- `execArmsHA` runs the arm `armWahlG` selects. -/
theorem execArmsHA_wahl {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
      (σ : World D) (ρ : Env D Γ),
    execArmsHA S O U A passes R arms v σ ρ =
      (execBlockHA S O U A passes R (armWahlG arms v).2.1 σ
        (armEnv (armWahlG arms v).2.2 ρ)).schrumpfArm (armWahlG arms v).1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArmsHA, armWahlG]
      exact execArmsHA_wahl rest _ σ ρ

/-- `execGrundHA` runs the arm `grundWahlG` selects. -/
theorem execGrundHA_wahl {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrundHA S O U A passes R arms r σ ρ = execBlockHA S O U A passes R (grundWahlG arms r) σ ρ
  | _, .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨k + 1, h⟩, σ, ρ => by
      simp only [execGrundHA, grundWahlG]
      exact execGrundHA_wahl rest _ σ ρ

theorem execGrundHA_wahlW {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n)
    (r : Wert D (.grund n)) (σ : World D) (ρ : Env D Γ) :
    execGrundHA S O U A passes R arms r σ ρ = execBlockHA S O U A passes R (grundWahlG arms r) σ ρ :=
  execGrundHA_wahl S O U A passes R arms r σ ρ

end WeiterA

/-! ## 4. The residue step lemmas, one per rule of G -/

section StufenA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semHA_ende_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ende (.cons s rest)) σ ρ =
      weiterHA S O U A passes R (.ende rest) (execStmtHA S O U A passes R s σ ρ) := by
  show zErgG (execEndHA S O U A passes R (.cons s rest) σ ρ) = _
  simp only [execEndHA]
  cases execStmtHA S O U A passes R s σ ρ <;> rfl

theorem laufAHA_nil {Λ : List (Res D)} (o : Ausgang V l Γ) :
    laufA (fun σ ρ => execBlockHA S O U A passes R (.nil : Block D V l Γ Λ Λ) σ ρ) o = o := by
  cases o <;> rfl

theorem semHA_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ende (.cons s rest)) σ ρ =
      semHA S O U A passes R (.dann (.cons s .nil) (.ende rest)) σ ρ := by
  rw [semHA_ende_cons, semHA_dann_cons]
  show _ = weiterHA S O U A passes R (.ende rest) (laufA _ _)
  rw [laufAHA_nil]

theorem semHA_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann .nil k) σ ρ = semHA S O U A passes R k σ ρ := rfl

theorem semHA_ite {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) (b : Bool)
    (hw : wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) = b) :
    semHA S O U A passes R (.dann (.cons (.ite c t e) rest) k) σ ρ =
      semHA S O U A passes R (.dann (if b then t else e) (.dann rest k)) (leseA A σ Λ c.orte) ρ := by
  rw [semHA_dann_cons]
  cases b <;> simp only [execStmtHA, hw] <;> rfl

theorem semHA_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ = Option.some v) :
    semHA S O U A passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semHA S O U A passes R (.dann p (.schrumpf (.dann rest k))) (leseA A σ Λ o.orte) (.cons v ρ) := by
  rw [semHA_dann_cons]
  simp only [execStmtHA, hv]
  rfl

theorem semHA_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ = Option.none) :
    semHA S O U A passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semHA S O U A passes R (.dann a (.dann rest k)) (leseA A σ Λ o.orte) ρ := by
  rw [semHA_dann_cons]
  simp only [execStmtHA, hv]
  rfl

theorem semHA_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (leseA A σ Λ v.orte) v (leseA A σ Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semHA S O U A passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semHA S O U A passes R (.dann b (.schrumpf (.dann rest k))) (leseA A σ Λ v.orte)
        (armEnv nutz ρ) := by
  rw [semHA_dann_cons]
  simp only [execStmtHA]
  rw [execArmsHA_wahl, hw]
  rfl

theorem semHA_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (leseA A σ Λ v.orte) v (leseA A σ Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semHA S O U A passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semHA S O U A passes R (.dann b (.dann rest k)) (leseA A σ Λ v.orte) (armEnv nutz ρ) := by
  rw [semHA_dann_cons]
  simp only [execStmtHA]
  rw [execArmsHA_wahl, hw]
  rfl

theorem semHA_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.dann (.cons (.onGrund r arms) rest) k) σ ρ =
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
    semHA S O U A passes R (.schrumpf k) σ (.cons v ρ) = semHA S O U A passes R k σ ρ := rfl

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
        (.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ) := rfl

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
    semHA S O U A passes R (.dann (.pruefung c sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest k) (leseA A σ Λ c.orte) ρ := by
  rw [semHA_dann]
  simp only [execBlockHA, hw, if_true]
  rfl

theorem semHA_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ) = false) :
    (semHA S O U A passes R (.dann (.pruefung c sonst rest) k) σ ρ).folgt
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
        (.cons ((leseA A σ Λ (.inr g :: neuE.orte)).globs g) ρ) := rfl

theorem semHA_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ).x
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semHA S O U A passes R (.dann (.gleit op a b lo hi rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semHA S O U A passes R (.dann (.gleitLit q lo hi rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitAusInt (eval (leseA A σ Λ e.orte) e
      (leseA A σ Λ e.orte) ρ).n) = some v) :
    semHA S O U A passes R (.dann (.gleitVon e lo hi rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ e.orte) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x = some v) :
    semHA S O U A passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ e.orte) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv]
  rfl

theorem semHA_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x = none) :
    (semHA S O U A passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ).folgt
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
      semHA S O U A passes R (.trav t inv body is k) σ ρ := rfl

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
      semHA S O U A passes R (.wieder n bis body ueber k) σ ρ := rfl

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
      semHA S O U A passes R (.ewig a n inv body k) σ ρ := rfl

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

theorem semHA_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.ret (l := l) e hperm)) σ ρ).gleich
      (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) :=
  ZErgG.gleich_refl _

theorem semHA_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.cons (.ret e hperm) rest)) σ ρ).gleich
      (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) := by
  rw [semHA_ende_cons]
  exact ZErgG.gleich_refl _

theorem semHA_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ).gleich
      (.zurueck (leseA A σ Λ e.orte) (evalErg (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ)) := by
  rw [semHA_dann_cons]
  exact weiterHA_zurueck S O U A passes R (.dann rest k) _ _

/-! ### Reason returns (2026-09-14): the residue predicts the reason exit
    at the current world -/

theorem semHA_rueckGrund {Λ : List (Res D)} (r : Fin V.gruende) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.retGrund (l := l) r hperm)) σ ρ).gleich (.grund σ r) :=
  ZErgG.gleich_refl _

theorem semHA_rueckConsGrund {Λ : List (Res D)} (r : Fin V.gruende) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.ende (.cons (.retGrund r hperm) rest)) σ ρ).gleich (.grund σ r) := by
  rw [semHA_ende_cons]
  exact ZErgG.gleich_refl _

theorem semHA_dannRetGrund {Λ Λ'' : List (Res D)} (r : Fin V.gruende)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semHA S O U A passes R (.dann (.cons (.retGrund r hperm) rest) k) σ ρ).gleich (.grund σ r) := by
  rw [semHA_dann_cons]
  exact weiterHA_grund S O U A passes R (.dann rest k) _ _

/-! ### The device forms -/

theorem semHA_regLies {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v)
    (hz : D.rzusage r v = true) :
    semHA S O U A passes R (.dann (.regLies r hk rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv, hz, if_true]
  rfl

theorem semHA_regLiesElseWahr {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v)
    (hw : wahr? (eval (leseA A σ Λ zusage.orte) zusage (leseA A σ Λ zusage.orte) (.cons v ρ)) = true) :
    semHA S O U A passes R (.dann (.regLiesElse r hk zusage sonst rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ zusage.orte) (.cons v ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv, hw, if_true]
  rfl

theorem semHA_regLiesElseFalsch {Λ Λ' : List (Res D)} (r : D.Reg)
    (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) = some v)
    (hw : wahr? (eval (leseA A σ Λ zusage.orte) zusage (leseA A σ Λ zusage.orte) (.cons v ρ)) = false) :
    (semHA S O U A passes R (.dann (.regLiesElse r hk zusage sonst rest) k) σ ρ).folgt
      (semHA S O U A passes R (.dann sonst.alsBlock.2 (.abbruch k)) (leseA A σ Λ zusage.orte) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hv, hw, Bool.false_eq_true, if_false]
  rw [semHA_alsBlock]
  exact ZErgG.folgt_refl _

theorem semHA_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (hvis : O.sichtbar g (leseA A σ Λ [.inr g]) = true) :
    semHA S O U A passes R (.dann (.awaits g payload hp hL rest) k) σ ρ =
      semHA S O U A passes R (.dann rest (.schrumpf k)) (leseA A σ Λ [.inr g])
        (.cons ((leseA A σ Λ [.inr g]).globs g) ρ) := by
  rw [semHA_dann]
  simp only [execBlockHA, hvis, if_true]
  rfl

/-! ### The checks of G, failing -/

theorem semHA_trav_falsch {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false) :
    semHA S O U A passes R (.trav t inv body ks k) σ ρ = .logik .schleife := by
  cases ks with
  | nil =>
      simp only [semHA, weiterHA, laufA, traverseLauf, leseBA, hw]
      exact weiterHA_logik S O U A passes R k _
  | cons i is =>
      simp only [semHA, weiterHA, laufA, traverseLauf, leseBA, hw]
      exact weiterHA_logik S O U A passes R k _

theorem semHA_ewig_falsch {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false) :
    semHA S O U A passes R (.ewig a (n + 1) inv body k) σ ρ = .logik .schleife := by
  simp only [semHA, weiterHA, laufA, foreverLauf, leseBA, hw]
  exact weiterHA_logik S O U A passes R k _

theorem semHA_leaveTrav_falsch {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ) (hl : true = true)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ) = false) :
    semHA S O U A passes R (.dann (.cons (.leave hl) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semHA_dann_cons]
  show weiterHA S O U A passes R (.travRest t inv body is k) (.leave hl σ (.cons i ρ)) = _
  simp only [weiterHA, leseBA, Env.tail, hw]
  exact weiterHA_logik S O U A passes R k _

end StufenA

end Gabbro.Grammatik
