/- Part 2 of 4 of `ZielOrtVollSem` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtVollSem.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Weiter

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- Run `f` on an `ok` outcome, pass every other outcome through. -/
def laufA {l : Bool} {Γ : Ctx} (f : World D → Env D Γ → Ausgang V l Γ) :
    Ausgang V l Γ → Ausgang V l Γ
  | .ok σ ρ => f σ ρ
  | o => o

/-- The invariant/bound read of a loop head, exactly as `execStmt` reads it. -/
def leseB {Γ : Ctx} {Λ : List (Res D)} (c : Expr D Γ Λ .bool) :
    World D → Env D Γ → World D × Bool :=
  fun σ ρ => let σ := σ.lese Λ c.orte; (σ, wahr? (eval σ c σ ρ))

/-- **How a residue continues from an outcome** (see the file header). -/
def weiterZ : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ →
    Ausgang V l Γ → ZErg V
  | _, _, _, .ende e, o =>
      match o with
      | .ok σ ρ => zErg (execEnd O passes R e σ ρ)
      | .zurueck σ v => .zurueck σ v
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .dann b k, o => weiterZ k (laufA (fun σ ρ => execBlock O passes R b σ ρ) o)
  | _, _, _, .schrumpf k, o => weiterZ k o.schrumpf
  | _, _, _, .frei L k, o => weiterZ k (o.mapWelt (·.gibt L))
  | _, _, _, .trav _ inv body ks k, o =>
      weiterZ k (laufA (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) ks) o)
  | _, _, _, .travRest _ inv body ks k, o =>
      match o with
      | .ok σ ρ =>
          weiterZ k (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) ks σ ρ.tail)
      | .next _ σ ρ =>
          weiterZ k (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) ks σ ρ.tail)
      | .leave _ σ ρ =>
          weiterZ k (if (leseB inv σ ρ.tail).2 = true then .ok (leseB inv σ ρ.tail).1 ρ.tail
            else .logik .schleife)
      | .zurueck σ v => weiterZ k (.zurueck σ v)
      | .why σ r => weiterZ k (.why σ r)
      | .logik e => weiterZ k (.logik e)
      | .hardware e => weiterZ k (.hardware e)
  | _, _, _, .wieder n bis body ueber k, o =>
      weiterZ k (laufA (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlock O passes R ueber σ ρ) n) o)
  | _, _, _, .wiederRest n bis body ueber k, o =>
      match o with
      | .ok σ ρ => weiterZ k (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
          (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ)
      | .next _ σ ρ => weiterZ k (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
          (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ)
      | .leave _ σ ρ => weiterZ k (.ok σ ρ)
      | .zurueck σ v => weiterZ k (.zurueck σ v)
      | .why σ r => weiterZ k (.why σ r)
      | .logik e => weiterZ k (.logik e)
      | .hardware e => weiterZ k (.hardware e)
  | _, _, _, .ewig a n inv body k, o =>
      weiterZ k (laufA (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) n) o)
  | _, _, _, .ewigRest a n inv body k, o =>
      match o with
      | .ok σ ρ => weiterZ k (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .next _ σ ρ => weiterZ k (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .leave _ σ ρ => weiterZ k (.ok σ ρ)
      | .zurueck σ v => weiterZ k (.zurueck σ v)
      | .why σ r => weiterZ k (.why σ r)
      | .logik e => weiterZ k (.logik e)
      | .hardware e => weiterZ k (.hardware e)
  | _, _, _, .wartet _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterZ k o
  | _, _, _, .wartetSonst _ _ _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterZ k o
  | _, _, _, .abbruch k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterZ k o

/-- The frame semantics of a residue: run it from `σ`, `ρ`. -/
def semV {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : ZErg V :=
  weiterZ O passes R r (.ok σ ρ)

variable {l : Bool} {Γ : Ctx}

theorem laufA_ok (f : World D → Env D Γ → Ausgang V l Γ) (σ : World D) (ρ : Env D Γ) :
    laufA f (.ok σ ρ) = f σ ρ := rfl

/-- A block with a head statement: the head, then the rest on `ok`. -/
theorem execBlock_cons_laufA {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.cons s rest) σ ρ =
      laufA (fun σ ρ => execBlock O passes R rest σ ρ) (execStmt O passes R s σ ρ) := by
  simp only [execBlock]
  cases execStmt O passes R s σ ρ <;> rfl

theorem semV_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann b k) σ ρ = weiterZ O passes R k (execBlock O passes R b σ ρ) := rfl

theorem semV_dann_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons s rest) k) σ ρ =
      weiterZ O passes R (.dann rest k) (execStmt O passes R s σ ρ) := by
  rw [semV_dann, execBlock_cons_laufA]
  rfl

/-! ### Outcomes that pass through every residue -/

theorem weiterZ_logik : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Logik D), weiterZ O passes R k (.logik e) = .logik e
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterZ_logik k e
  | _, _, _, .schrumpf k, e => weiterZ_logik k e
  | _, _, _, .frei _ k, e => weiterZ_logik k e
  | _, _, _, .trav _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .wartet _ k, e => weiterZ_logik k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .abbruch k, e => weiterZ_logik k e

theorem weiterZ_grund : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (r : Fin V.gruende), weiterZ O passes R k (.why σ r) = .sonst
  | _, _, _, .ende _, _, _ => rfl
  | _, _, _, .dann _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .schrumpf k, σ, r => weiterZ_grund k σ r
  | _, _, _, .frei L k, σ, r => weiterZ_grund k (σ.gibt L) r
  | _, _, _, .trav _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .travRest _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wieder _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wiederRest _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .ewig _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .ewigRest _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wartet _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wartetSonst _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .abbruch k, σ, r => weiterZ_grund k σ r

theorem weiterZ_hardware : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Hardware D), weiterZ O passes R k (.hardware e) = .sonst
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterZ_hardware k e
  | _, _, _, .schrumpf k, e => weiterZ_hardware k e
  | _, _, _, .frei _ k, e => weiterZ_hardware k e
  | _, _, _, .trav _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .wartet _ k, e => weiterZ_hardware k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .abbruch k, e => weiterZ_hardware k e

theorem sg_gibt (σ : World D) (L : D.Lock) : SG (σ.gibt L) σ := ⟨rfl, rfl⟩

theorem weiterZ_zurueck : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (v : ErgVal D V.erg),
    (weiterZ O passes R k (.zurueck σ v)).gleich (.zurueck σ v)
  | _, _, _, .ende _, _, _ => ZErg.gleich_refl _
  | _, _, _, .dann _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .schrumpf k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .frei L k, σ, v =>
      ZErg.gleich_trans (weiterZ_zurueck k (σ.gibt L) v) ⟨sg_gibt σ L, rfl⟩
  | _, _, _, .trav _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .travRest _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wieder _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wiederRest _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .ewig _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .ewigRest _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wartet _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wartetSonst _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .abbruch k, σ, v => weiterZ_zurueck k σ v

/-- **An end block replacing a residue.** Where G replaces the whole residue
    by an end block (the `else` block of `narrow`/`pruefung`/float
    narrowing, the `else` block of `let … else` on a reason), the old
    residue's prediction is refined by the end block's own result: a return
    and a logic failure pass through every continuation; everything else
    the end block predicts nothing. -/
theorem weiterZ_ende_folgt {Λ : List (Res D)} (k : GRest D V l Γ Λ) (eo : EndAusgang V l Γ) :
    (weiterZ O passes R k eo.zuAusgang).folgt (zErg eo) := by
  cases eo with
  | zurueck σ v => exact ZErg.folgt_of_gleich (weiterZ_zurueck O passes R k σ v)
  | logik e => exact ZErg.folgt_of_eq (weiterZ_logik O passes R k e)
  | _ => exact ZErg.folgt_sonst _

/-- Past `abbruch`, an end outcome continues as without it. -/
theorem weiterZ_abbruch_zu {Λ Λk : List (Res D)} (k : GRest D V l Γ Λk) (eo : EndAusgang V l Γ) :
    weiterZ O passes R (.abbruch (Λ := Λ) k) eo.zuAusgang = weiterZ O passes R k eo.zuAusgang := by
  cases eo <;> rfl

/-- **The residue of an `else` branch** (`.dann e.alsBlock.2 (.abbruch k)`)
    means the end block's outcome continued by `k`: a `leave`/`next` in
    it reaches the loop in `k`. -/
theorem semV_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ) (k : GRest D V l Γ Λk)
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann e.alsBlock.2 (.abbruch k)) σ ρ =
      weiterZ O passes R k (execEnd O passes R e σ ρ).zuAusgang := by
  rw [semV_dann, Endblock.execBlock_alsBlock, weiterZ_abbruch_zu]

end Weiter
/-! ## 4. The residues the replay follows -/

/-- A residue in the covered fragment whose blocks, loop heads and calls
    read only inside the footprint `S`. -/
def GRest.okV (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.vOk (kandP P S) = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.vOk (kandP P S) = true ∧ blockOrteP P b ⊆ S ∧ k.okV P S
  | _, _, _, .schrumpf k => k.okV P S
  | _, _, _, .frei _ k => k.okV P S
  | _, _, _, .trav _ inv body _ k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.vOk (kandP P S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okV P S
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.vOk (kandP P S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okV P S
  | _, _, _, .ewig _ _ inv body k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .ewigRest _ _ inv body k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .wartet b k => b.vOk (kandP P S) = true ∧ blockOrteP P b ⊆ S ∧ k.okV P S
  | _, _, _, .wartetSonst _ err b k =>
      err.vOk (kandP P S) = true ∧ endblockOrteP P err ⊆ S ∧ b.vOk (kandP P S) = true ∧
        blockOrteP P b ⊆ S ∧ k.okV P S
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k =>
      (∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) ∧ k.okV P S

section OkV

variable {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okV_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okV P S) :
    s.vOk (kandP P S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okV P S := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.vOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okV_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okV P S) :
    s.vOk (kandP P S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okV P S := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.vOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

/-- **The residue of an `else` branch is in the fragment** when the end
    block is and the continuation is (its held set agreeing). -/
theorem okV_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ) (k : GRest D V l Γ Λk)
    (hΛ : ∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) (he : e.vOk (kandP P S) = true)
    (heS : endblockOrteP P e ⊆ S) (hk : k.okV P S) :
    (GRest.dann e.alsBlock.2 (.abbruch k)).okV P S :=
  ⟨by rw [Endblock.vOk_alsBlock]; exact he, by rw [blockOrteP_alsBlock]; exact heS,
    fun L => (hΛ L).trans (e.alsBlock.2.held_iff L).symm, hk⟩

end OkV
/-! ## 5. The residue step lemmas, one per rule of G -/


end Gabbro.Grammatik
