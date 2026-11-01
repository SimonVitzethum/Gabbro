module

public import Grammatik.Speichermodell.Atomar.AtomarSem

@[expose] public section



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
      | .why σ r => .why σ r
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
      | .why σ r => weiterHA k (.why σ r)
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
      | .why σ r => weiterHA k (.why σ r)
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
      | .why σ r => weiterHA k (.why σ r)
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
  | _, _, _, .leer, o =>
      match o with
      | .zurueck σ v => .zurueck σ v
      | .why σ r => .why σ r
      | .logik e => .logik e
      | _ => .sonst

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
      weiterHA S O U A passes R k (execBlockHA S O U A passes R b σ ρ) := by rfl

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
  | _, _, _, .leer, _ => rfl

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
  | _, _, _, .leer, _, _ => ZErgG.gleich_refl _

/-- A reason exit passes every residue unchanged up to the trace (the twin
    of `weiterHA_zurueck`, 2026-09-14). -/
theorem weiterHA_grund : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (r : Fin V.gruende),
    (weiterHA S O U A passes R k (.why σ r)).gleich (.why σ r)
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
  | _, _, _, .leer, _, _ => ZErgG.gleich_refl _

/-- **An end block replacing a residue** (as `weiterZ_ende_folgt`). -/
theorem weiterHA_ende_folgt {Λ : List (Res D)} (k : GRest D V l Γ Λ) (eo : EndAusgang V l Γ) :
    (weiterHA S O U A passes R k eo.zuAusgang).folgt (zErgG eo) := by
  cases eo with
  | zurueck σ v => exact ZErgG.folgt_of_gleich (weiterHA_zurueck S O U A passes R k σ v)
  | why σ r => exact ZErgG.folgt_of_gleich (weiterHA_grund S O U A passes R k σ r)
  | logik e => exact ZErgG.folgt_of_eq (weiterHA_logik S O U A passes R k e)
  | _ => exact ZErgG.folgt_sonst _

/-- `execBlockHA` of an end block run as a block (`Endblock.alsBlock`) is
    the end block's own outcome (as `Endblock.execBlock_alsBlock`). -/
theorem Endblock.execBlockHA_alsBlock :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
      execBlockHA S O U A passes R e.alsBlock.2 σ ρ = (execEndHA S O U A passes R e σ ρ).zuAusgang
  | _, _, .ret _ _, _, _ => rfl
  | _, _, .retWhy _ _, _, _ => rfl
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
  | _, _, .bindCall f args he hp hr rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rfl
      · rfl
  | _, _, .bindCallElse f args he hp hr err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · cases execEndHA S O U A passes R err _ _ <;> rfl
      · rfl
      · rfl
  | _, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · cases execEndHA S O U A passes R err _ _ <;> rfl
      · rfl
  | _, _, .regRead r hk rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · split
        · rw [Endblock.execBlockHA_alsBlock rest]
          cases execEndHA S O U A passes R rest _ _ <;> rfl
        · rfl
      · rfl
  | _, _, .regReadElse r hk z sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · split
        · rw [Endblock.execBlockHA_alsBlock rest]
          cases execEndHA S O U A passes R rest _ _ <;> rfl
        · rfl
      · rfl
  | _, _, .awaits g pl hp hL hat rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      rename_i f hf _
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · rename_i r _
        exact keinGrundSig hf hr r
      · rfl
      · rfl
  | _, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · rw [Endblock.execBlockHA_alsBlock rest]
        cases execEndHA S O U A passes R rest _ _ <;> rfl
      · rfl
  | _, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      rw [Endblock.execBlockHA_alsBlock rest]
      cases execEndHA S O U A passes R rest _ _ <;> rfl
  | _, _, .ite c t e, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockHA, execEndHA]
      split
      · exact Endblock.execBlockHA_alsBlock t _ _
      · rfl

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

/-- The base of the `endeForm` continuation passes an end outcome on as it is. -/
theorem weiterHA_leer_zu {Λ : List (Res D)} (eo : EndAusgang V l Γ) :
    weiterHA S O U A passes R (.leer (Λ := Λ)) eo.zuAusgang = zErgG eo := by
  cases eo <;> rfl

/-- **An end block unfolded into block position** (`endeForm`) means the end block. -/
theorem semHA_endeForm {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semHA S O U A passes R (.ende e) σ ρ =
      semHA S O U A passes R (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) σ ρ := by
  rw [semHA_alsBlock, weiterHA_leer_zu]
  rfl

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
    (r : Wert D (.why n)) (σ : World D) (ρ : Env D Γ) :
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
    semHA S O U A passes R (.dann .nil k) σ ρ = semHA S O U A passes R k σ ρ := by rfl

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

end StufenA
end Gabbro.Grammatik
