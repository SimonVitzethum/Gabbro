/-
  File:      Grammatik/Logik/Ruf/Maschine/Budget.lean
  Subject:   THE BUDGET IS MONOTONE: a run of machine G with the `forever` budget `p` is, step for step, a run
             with every larger budget `p + j`, on the machines whose `ewig` counters are `j` higher.

  Machine G gives every `forever` instance the budget `passes` when it is entered (`dannForever` writes
  `.ewig a passes …`) and counts it down per pass (`ewigWeiter`); at `0` the loop stops with the named budget
  stop. The budget is the ONLY thing `passes` decides in a step: a leaf, `leave` and `next` run the same at
  every budget (`execStmt_blatt_passes`). So shifting every counter by `j` (`RufMaschineG.plus`) maps each step
  at budget `p` to a step at budget `p + j` (`rufSchrittG_plus`), and every run (`rufErreichbarG_plus`, over GX
  `rufErreichbarGX_plus`, the thread machine `fadenErreichbarX_plus`). The start machine has no counter
  (`rufStartG_plus`).

  Reading: the family of budgets is increasing, and a finite run of the program -- any prefix of an unbounded
  run -- is a run at every budget above the number of its passes. A stop on budget is never final: from the
  shifted machine one budget higher the stopped loop takes its next pass (`ewig_budget_unecht`).
-/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG
import Grammatik.Speichermodell.Maschine.GXMaschine

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Shifting the counters -/

/-- Every `ewig` counter of the residue `j` higher; nothing else changes. -/
def GRest.plus (j : Nat) {V : Vertrag D} : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    GRest D V l Γ Λ → GRest D V l Γ Λ
  | _, _, _, .ende e => .ende e
  | _, _, _, .dann b k => .dann b (k.plus j)
  | _, _, _, .schrumpf k => .schrumpf (k.plus j)
  | _, _, _, .frei L k => .frei L (k.plus j)
  | _, _, _, .trav t inv body ks k => .trav t inv body ks (k.plus j)
  | _, _, _, .travRest t inv body ks k => .travRest t inv body ks (k.plus j)
  | _, _, _, .wieder n bis body ueber k => .wieder n bis body ueber (k.plus j)
  | _, _, _, .wiederRest n bis body ueber k => .wiederRest n bis body ueber (k.plus j)
  | _, _, _, .ewig a n inv body k => .ewig a (n + j) inv body (k.plus j)
  | _, _, _, .ewigRest a n inv body k => .ewigRest a (n + j) inv body (k.plus j)
  | _, _, _, .wartet rest k => .wartet rest (k.plus j)
  | _, _, _, .wartetSonst n err rest k => .wartetSonst n err rest (k.plus j)
  | _, _, _, .abbruch k => .abbruch (k.plus j)
  | _, _, _, .leer => .leer

/-- A frame with its residue shifted. -/
def RufRahmenG.plus (j : Nat) (r : RufRahmenG D) : RufRahmenG D :=
  ⟨r.f, r.rho, r.s0, ⟨r.rest.1, r.rest.2.1, r.rest.2.2.1, r.rest.2.2.2.1, r.rest.2.2.2.2.plus j⟩⟩

/-- A thread with every frame shifted. -/
def RufFadenG.plus (j : Nat) (z : RufFadenG D) : RufFadenG D :=
  ⟨z.stapel.map (RufRahmenG.plus j), z.kopf.plus j, z.spur, z.log⟩

/-- A machine with every thread shifted. -/
def RufMaschineG.plus (j : Nat) (M : RufMaschineG D) : RufMaschineG D :=
  ⟨M.speicher, fun t => (M.faeden t).plus j, M.lauf, M.start⟩

/-- A thread machine with its machine-G state shifted. -/
def FadenMaschine.plus (j : Nat) (K : FadenMaschine D) : FadenMaschine D :=
  ⟨K.m.plus j, K.lebt, K.wartet, K.rang, K.uhr⟩

@[simp] theorem RufMaschineG.plus_speicher (j : Nat) (M : RufMaschineG D) :
    (M.plus j).speicher = M.speicher := rfl
@[simp] theorem RufMaschineG.plus_lauf (j : Nat) (M : RufMaschineG D) : (M.plus j).lauf = M.lauf := rfl
@[simp] theorem RufMaschineG.plus_start (j : Nat) (M : RufMaschineG D) : (M.plus j).start = M.start := rfl
@[simp] theorem RufMaschineG.plus_faeden (j : Nat) (M : RufMaschineG D) (t : Faden) :
    (M.plus j).faeden t = (M.faeden t).plus j := rfl
@[simp] theorem RufFadenG.plus_spur (j : Nat) (z : RufFadenG D) : (z.plus j).spur = z.spur := rfl
@[simp] theorem RufFadenG.plus_log (j : Nat) (z : RufFadenG D) : (z.plus j).log = z.log := rfl
@[simp] theorem RufFadenG.plus_stapel (j : Nat) (z : RufFadenG D) :
    (z.plus j).stapel = z.stapel.map (RufRahmenG.plus j) := rfl
@[simp] theorem RufFadenG.plus_kopf (j : Nat) (z : RufFadenG D) : (z.plus j).kopf = z.kopf.plus j := rfl
@[simp] theorem RufRahmenG.plus_f (j : Nat) (r : RufRahmenG D) : (r.plus j).f = r.f := rfl
@[simp] theorem RufRahmenG.plus_rho (j : Nat) (r : RufRahmenG D) : (r.plus j).rho = r.rho := rfl
@[simp] theorem RufRahmenG.plus_s0 (j : Nat) (r : RufRahmenG D) : (r.plus j).s0 = r.s0 := rfl

theorem RufMaschineG.plus_weltVon (j : Nat) (M : RufMaschineG D) (t : Faden) :
    (M.plus j).weltVon t = M.weltVon t := rfl

/-- A residue with its context, shifted, read through its own equation. -/
theorem sigmaRest_plus (j : Nat) {V : Vertrag D}
    {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {g : GRest D V l Γ Λ} (h : x = ⟨l, Γ, Λ, ρ, g⟩) :
    (⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.plus j⟩ :
      Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) = ⟨l, Γ, Λ, ρ, g.plus j⟩ := by
  subst h; rfl

theorem RufRahmenG.plus_rest {j : Nat} {r : RufRahmenG D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {g : GRest D (vertragVon D r.f) l Γ Λ} (h : r.rest = ⟨l, Γ, Λ, ρ, g⟩) :
    (r.plus j).rest = ⟨l, Γ, Λ, ρ, g.plus j⟩ :=
  sigmaRest_plus j h

theorem rufUpdateG_plus (j : Nat) (m : Faden → RufFadenG D) (f : Faden) (z : RufFadenG D) :
    (fun t => (rufUpdateG m f z t).plus j) = rufUpdateG (fun t => (m t).plus j) f (z.plus j) := by
  funext t
  by_cases h : t = f
  · subst h; simp [rufUpdateG]
  · simp [rufUpdateG, h]

theorem GRest.plus_zero {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : GRest D V l Γ Λ),
    g.plus 0 = g
  | _, _, _, .ende _ => rfl
  | _, _, _, .dann _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .schrumpf k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .frei _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .trav .. => by rename_i k; simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .travRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .wieder .. => by rename_i k; simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .wiederRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .ewig .. => by rename_i k; simp only [GRest.plus, GRest.plus_zero k, Nat.add_zero]
  | _, _, _, .ewigRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k, Nat.add_zero]
  | _, _, _, .wartet _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .wartetSonst _ _ _ k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .abbruch k => by simp only [GRest.plus, GRest.plus_zero k]
  | _, _, _, .leer => rfl

theorem GRest.plus_plus (i j : Nat) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ), (g.plus i).plus j = g.plus (i + j)
  | _, _, _, .ende _ => rfl
  | _, _, _, .dann _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .schrumpf k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .frei _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .trav .. => by rename_i k; simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .travRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .wieder .. => by rename_i k; simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .wiederRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .ewig .. => by rename_i k; simp only [GRest.plus, GRest.plus_plus i j k, Nat.add_assoc]
  | _, _, _, .ewigRest _ _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k, Nat.add_assoc]
  | _, _, _, .wartet _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .wartetSonst _ _ _ k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .abbruch k => by simp only [GRest.plus, GRest.plus_plus i j k]
  | _, _, _, .leer => rfl

theorem GRest.plus_wartend (j : Nat) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ), (g.plus j).wartend = g.wartend
  | _, _, _, .ende _ | _, _, _, .dann .. | _, _, _, .schrumpf _ | _, _, _, .frei .. | _, _, _, .trav ..
  | _, _, _, .travRest .. | _, _, _, .wieder .. | _, _, _, .wiederRest .. | _, _, _, .ewig ..
  | _, _, _, .ewigRest .. | _, _, _, .wartet .. | _, _, _, .wartetSonst .. | _, _, _, .abbruch _
  | _, _, _, .leer => rfl

/-! ## 2. The budget decides nothing but the budget -/

/-- **A leaf runs the same at every budget** (it contains no loop). -/
theorem execStmt_blatt_passes (O : Orakel D) (p q : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (h : s.istBlatt = true) (σ : World D) (ρ : Env D Γ) :
    execStmt O p R s σ ρ = execStmt O q R s σ ρ := by
  cases s <;> simp only [Stmt.istBlatt, Bool.false_eq_true] at h <;> rfl

/-- The start machine has no counter. -/
theorem rufStartG_plus (j : Nat) (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) :
    (RufStartG P sp init).plus j = RufStartG P sp init := by
  simp only [RufMaschineG.plus, RufStartG, RufFadenG.plus, RufRahmenG.plus, GRest.plus, List.map_nil]

theorem RufRahmenG.plus_wartend (j : Nat) (r : RufRahmenG D) : (r.plus j).wartend = r.wartend :=
  GRest.plus_wartend j _

theorem GRest.plus_anRueck (j : Nat) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ), (g.plus j).anRueck = g.anRueck
  | _, _, _, .ende _ | _, _, _, .dann .. | _, _, _, .schrumpf _ | _, _, _, .frei .. | _, _, _, .trav ..
  | _, _, _, .travRest .. | _, _, _, .wieder .. | _, _, _, .wiederRest .. | _, _, _, .ewig ..
  | _, _, _, .ewigRest .. | _, _, _, .wartet .. | _, _, _, .wartetSonst .. | _, _, _, .abbruch _
  | _, _, _, .leer => rfl

theorem fertigG_plus (j : Nat) (M : RufMaschineG D) (t : Faden) : FertigG (M.plus j) t ↔ FertigG M t := by
  unfold FertigG
  refine and_congr ?_ ?_
  · simp
  · exact Eq.to_iff (congrArg (· = true) (GRest.plus_anRueck j (M.faeden t).kopf.rest.2.2.2.2))

/-! ## 3. Every step at budget `p` is a step at budget `p + j` -/

/-- The successor machine of every step, shifted: the update of the acting thread, shifted. -/
theorem RufMaschineG.plus_update (j : Nat) (sp : Speicher D) (m : Faden → RufFadenG D) (f : Faden)
    (z : RufFadenG D) (la : Lauf D) (st : World D) :
    RufMaschineG.plus j ⟨sp, rufUpdateG m f z, la, st⟩ =
      ⟨sp, rufUpdateG (fun t => (m t).plus j) f (z.plus j), la, st⟩ := by
  simp only [RufMaschineG.plus, rufUpdateG_plus]

/-- **A step at budget `p` is a step at budget `p + j`** of the shifted machines. -/
theorem rufSchrittG_plus {P : Programm D} {O : Orakel D} {p : Nat} (j : Nat) {M M' : RufMaschineG D}
    {f : Faden} (h : RufSchrittG P O p M f M') : RufSchrittG P O (p + j) (M.plus j) f (M'.plus j) := by
  cases h with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein_nimmt =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.blatt (passes := p + j) (M.plus j) f l Γ Λ Λ' s rest ρ hleaf (RufRahmenG.plus_rest hhead) hΛ σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf s hleaf _ _).symm.trans hstep) hneu hkein_nimmt
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.ruf (passes := p + j) (M.plus j) f l Γ Λ g args hp hr rest ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
  | rueck caller rest hpop Γ Λ e hperm ρ hAnon8 g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rueck (passes := p + j) (M.plus j) f (caller.plus j) (rest.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) Γ Λ e hperm ρ (RufRahmenG.plus_rest hAnon8) g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu (by rw [RufRahmenG.plus_wartend]; exact hnw)
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.endeEntf (passes := p + j) (M.plus j) f l Γ Λ Λ' s rest ρ hent (RufRahmenG.plus_rest hhead)
  | endeForm l Γ Λ e ρ hl hent hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.endeForm (passes := p + j) (M.plus j) f l Γ Λ e ρ hl hent (RufRahmenG.plus_rest hhead)
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein_nimmt =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBlatt (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' s rest (k.plus j) ρ hleaf (RufRahmenG.plus_rest hhead) hΛ σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf s hleaf _ _).symm.trans hstep) hneu hkein_nimmt
  | dannLeer l Γ Λ k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannLeer (passes := p + j) (M.plus j) f l Γ Λ (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannIteWahr (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c t e rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannIteFalsch (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c t e rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o pB a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannOnOptionSome (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n o pB a rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o pB a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannOnOptionNone (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n o pB a rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hv neu hneu hΛ
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannOnTagSome (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' cs v arms rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ lo hi b nutz hw neu hneu hΛ
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannOnTagNone (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' cs v arms rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ b nutz hw neu hneu hΛ
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannOnGrund (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n r arms rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ b hw neu hneu hΛ
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.endeBind (passes := p + j) (M.plus j) f l Γ Λ τ e rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ neu hneu hΛ
  | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.endeBindAxiom (passes := p + j) (M.plus j) f l Γ Λ τ a args he hw hg hd hgd rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBind (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ e rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ neu hneu hΛ
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannNarrowOk (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ h neu hneu hΛ
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannNarrowElse (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ h neu hneu hΛ
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannPruefWahr (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannPruefFalsch (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' c sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBreaking (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' i body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannLocks (passes := p + j) (M.plus j) f l Γ Λ Λ'' L hr body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hself hrang hfrei
  | freiGib l Γ Λ L k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.freiGib (passes := p + j) (M.plus j) f l Γ Λ L (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.schrumpfVergiss (passes := p + j) (M.plus j) f l Γ Λ τ (k.plus j) v ρ (RufRahmenG.plus_rest hhead)
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannTrav (passes := p + j) (M.plus j) f l Γ Λ Λ'' t inv body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | travNext l Γ Λ t inv body i is k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.travNext (passes := p + j) (M.plus j) f l Γ Λ t inv body i is (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | travFort l Γ Λ t inv body is k i ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.travFort (passes := p + j) (M.plus j) f l Γ Λ t inv body is (k.plus j) i ρ (RufRahmenG.plus_rest hhead)
  | travDone l Γ Λ t inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.travDone (passes := p + j) (M.plus j) f l Γ Λ t inv body (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | dannRetry l Γ Λ Λ' Λ'' n bis body ueber rest k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRetry (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n bis body ueber rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | wiederUeber l Γ Λ bis body ueber k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.wiederUeber (passes := p + j) (M.plus j) f l Γ Λ bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | wiederWeiter l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.wiederWeiter (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | wiederSchritt l Γ Λ n bis body ueber k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.wiederSchritt (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hw neu hneu hΛ
  | wiederFort l Γ Λ n bis body ueber k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.wiederFort (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | dannForever l Γ Λ Λ' Λ'' a inv body rest k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannForever (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' a inv body rest (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | ewigWeiter l Γ Λ a n inv body k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.ewigWeiter (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) ρ (by have h := RufRahmenG.plus_rest (j := j) hhead; simp only [GRest.plus] at h; rwa [show n + 1 + j = n + j + 1 by omega] at h) σ₁ hs₁ hw neu hneu hΛ
  | ewigFort l Γ Λ a n inv body k ρ hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.ewigFort (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) ρ (RufRahmenG.plus_rest hhead)
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rufDann (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' g args hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
  | dannCallInd l Γ Λ Λ' Λ'' n pB args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannCallInd (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' n pB args hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
  | rufCallInd l Γ Λ n pB args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rufCallInd (passes := p + j) (M.plus j) f l Γ Λ n pB args hp hr rest ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBindCall (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ g args he hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n pB args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBindCallInd (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ n pB args he hp hr rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 g hg hv rho hrho neu hneu
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBindCallElse (passes := p + j) (M.plus j) f l Γ Λ Λ' Λ'' τ g args he hp hr err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hΛ s0 hs0 rho hrho neu hneu
  | rueckBind caller rest hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hAnon17 g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rueckBind (passes := p + j) (M.plus j) f (caller.plus j) (rest.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ restb (k.plus j) ρc (hcaller.imp (fun h => RufRahmenG.plus_rest h) (fun ⟨n, err, h⟩ => ⟨n, err, RufRahmenG.plus_rest h⟩)) Γc Λc e hperm ρ (RufRahmenG.plus_rest hAnon17) g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv he neu hneu
  | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannLeaveTrav (passes := p + j) (M.plus j) f l Γ Λ t inv body is (k.plus j) rest i ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt σ₁ hs₁ hw neu₁ hneu₁ hΛ
  | dannNextTrav l Γ Λ t inv body is k rest i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannNextTrav (passes := p + j) (M.plus j) f l Γ Λ t inv body is (k.plus j) rest i ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
  | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannLeaveWieder (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) rest ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
  | dannNextWieder l Γ Λ n bis body ueber k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannNextWieder (passes := p + j) (M.plus j) f l Γ Λ n bis body ueber (k.plus j) rest ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
  | dannLeaveEwig l Γ Λ a n inv body k rest ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannLeaveEwig (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) rest ρ hleave (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
  | dannNextEwig l Γ Λ a n inv body k rest ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannNextEwig (passes := p + j) (M.plus j) f l Γ Λ a (n + j) inv body (k.plus j) rest ρ hnext (RufRahmenG.plus_rest hhead) σ' ρ' neu ((execStmt_blatt_passes O p (p + j) keinRuf _ rfl _ _).symm.trans hstep) hneu hkein_nimmt hΛ
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelDannLeave (passes := p + j) (M.plus j) f l Γ Λ rest b (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelDannNext (passes := p + j) (M.plus j) f l Γ Λ rest b (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelSchrumpfLeave (passes := p + j) (M.plus j) f l Γ Λ τ rest (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelSchrumpfNext (passes := p + j) (M.plus j) f l Γ Λ τ rest (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelFreiLeave (passes := p + j) (M.plus j) f l Γ Λ L rest (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelFreiNext (passes := p + j) (M.plus j) f l Γ Λ L rest (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
  | peelAbbruchLeave Γ Λ Λ1 Λk rest k ρ hleave hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelAbbruchLeave (passes := p + j) (M.plus j) f Γ Λ Λ1 Λk rest (k.plus j) ρ hleave (RufRahmenG.plus_rest hhead)
  | peelAbbruchNext Γ Λ Λ1 Λk rest k ρ hnext hhead =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.peelAbbruchNext (passes := p + j) (M.plus j) f Γ Λ Λ1 Λk rest (k.plus j) ρ hnext (RufRahmenG.plus_rest hhead)
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu hnw =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRet (passes := p + j) (M.plus j) f l Γ Λ Λ'' e hperm rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv neu hneu (by rw [RufRahmenG.plus_wartend]; exact hnw)
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hAnon9 g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rueckCons (passes := p + j) (M.plus j) f (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) Γ Λ e hperm rest ρ (RufRahmenG.plus_rest hAnon9) g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu (by rw [RufRahmenG.plus_wartend]; exact hnw)
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRetBind (passes := p + j) (M.plus j) f lk Γk Λk Λk'' e hperm restk (kk.plus j) ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ restb (k.plus j) ρc (hcaller.imp (fun h => RufRahmenG.plus_rest h) (fun ⟨n, err, h⟩ => ⟨n, err, RufRahmenG.plus_rest h⟩)) hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rueckConsBind (passes := p + j) (M.plus j) f lk Γk Λk e hperm restk ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ restb (k.plus j) ρc (hcaller.imp (fun h => RufRahmenG.plus_rest h) (fun ⟨n, err, h⟩ => ⟨n, err, RufRahmenG.plus_rest h⟩)) hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rueckGrund (passes := p + j) (M.plus j) f r hperm ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ n err restb (k.plus j) ρc (RufRahmenG.plus_rest hcaller) hΛ g hfg rho hrho s0 hs0 rg hrg hn
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.rueckConsGrund (passes := p + j) (M.plus j) f r hperm restk ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ n err restb (k.plus j) ρc (RufRahmenG.plus_rest hcaller) hΛ g hfg rho hrho s0 hs0 rg hrg hn
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho hrho s0 hs0 rg hrg hn =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRetGrund (passes := p + j) (M.plus j) f r hperm restk (kk.plus j) ρ (RufRahmenG.plus_rest hhead) (caller.plus j) (rst.map (RufRahmenG.plus j)) (congrArg (List.map (RufRahmenG.plus j)) hpop) l Γ Λ Λ' τ n err restb (k.plus j) ρc (RufRahmenG.plus_rest hcaller) hΛ g hfg rho hrho s0 hs0 rg hrg hn
  | dannRegLies l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRegLies (passes := p + j) (M.plus j) f l Γ Λ Λ' r hk rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv hz hΛ
  | dannRegLiesElseWahr l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRegLiesElseWahr (passes := p + j) (M.plus j) f l Γ Λ Λ' r hk zusage sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv σ₁ hs₁ hw neu hneu hΛ
  | dannRegLiesElseFalsch l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannRegLiesElseFalsch (passes := p + j) (M.plus j) f l Γ Λ Λ' r hk zusage sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv σ₁ hs₁ hw neu hneu hΛ
  | dannAwaits l Γ Λ Λ' g payload hp hL hat rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannAwaits (passes := p + j) (M.plus j) f l Γ Λ Λ' g payload hp hL hat rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) hvis σ₁ hs₁ neu hneu hΛ
  | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannExchange (passes := p + j) (M.plus j) f l Γ Λ Λ' g neuE hw hL rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ hs₂ neu hneu hΛ
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannGleit (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannGleitLit (passes := p + j) (M.plus j) f l Γ Λ Λ' q lo hi rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) v hv
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannGleitVon (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ e lo hi rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannGleitNarrowOk (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ v hv neu hneu hΛ
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannGleitNarrowElse (passes := p + j) (M.plus j) f l Γ Λ Λ' l₁ h₁ e lo hi sonst rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ hn neu hneu hΛ
  | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBindAxiom (passes := p + j) (M.plus j) f l Γ Λ Λ' τ a args he hw hg hd hgd rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
  | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBindAxiomElseOk (passes := p + j) (M.plus j) f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
  | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.dannBindAxiomElseGrund (passes := p + j) (M.plus j) f l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest (k.plus j) ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.endeBindAxiomElseOk (passes := p + j) (M.plus j) f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ v hax neu hneu hΛ
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      rw [RufMaschineG.plus_update]
      exact RufSchrittG.endeBindAxiomElseGrund (passes := p + j) (M.plus j) f l Γ Λ τ a args he hr hw hg hd hgd err rest ρ (RufRahmenG.plus_rest hhead) σ₁ hs₁ σ₂ r hax neu hneu hΛ

theorem rufErreichbarG_plus {P : Programm D} {O : Orakel D} {p : Nat} (j : Nat) {M0 M : RufMaschineG D}
    (h : RufErreichbarG P O p M0 M) : RufErreichbarG P O (p + j) (M0.plus j) (M.plus j) := by
  induction h with
  | start => exact .start
  | schritt M M' f _ hs ih => exact .schritt _ _ f ih (rufSchrittG_plus j hs)

/-! ## 4. Over GX and on the thread machine -/

theorem mitSpeicher_plus (j : Nat) (M : RufMaschineG D) (σ : Speicher D) :
    mitSpeicher (M.plus j) σ = (mitSpeicher M σ).plus j := rfl

theorem schreibG_plus (j : Nat) (M M' : RufMaschineG D) (u : Faden) (c : D.Tab ⊕ D.Glob) :
    SchreibG (M.plus j) (M'.plus j) u c ↔ SchreibG M M' u c := Iff.rfl

theorem rufSchrittGX_plus {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (j : Nat)
    {M M' : RufMaschineG D} {u : Faden} (h : RufSchrittGX P O p Tg M u M') :
    RufSchrittGX P O (p + j) Tg (M.plus j) u (M'.plus j) := by
  obtain ⟨σ, M'', hs, hσ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨σ, M''.plus j, ?_, hσ, h1, h2, ?_, h4, h5⟩
  · rw [mitSpeicher_plus]; exact rufSchrittG_plus j hs
  · show (fun t => (M'.faeden t).plus j) = fun t => (M''.faeden t).plus j
    rw [h3]

theorem rufErreichbarGX_plus {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (j : Nat) {M0 M : RufMaschineG D} (h : RufErreichbarGX P O p Tg M0 M) :
    RufErreichbarGX P O (p + j) Tg (M0.plus j) (M.plus j) := by
  induction h with
  | start => exact .start
  | schritt M M' u _ hs ih => exact .schritt _ _ u ih (rufSchrittGX_plus j hs)

theorem fadenSchrittX_plus {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop} (j : Nat)
    {K K' : FadenMaschine D} (h : FadenSchrittX P O p Tg K K') :
    FadenSchrittX P O (p + j) Tg (K.plus j) (K'.plus j) := by
  cases h with
  | lauf f M' hf hw hs => exact .lauf (K.plus j) f (M'.plus j) hf hw (rufSchrittGX_plus j hs)
  | start q cs hp hw hfrei hcs => exact .start (K.plus j) q cs hp hw hfrei hcs
  | kind q c hp hw hc => exact .kind (K.plus j) q c hp hw hc
  | join q hp hw hf => exact .join (K.plus j) q hp hw fun u hu => (fertigG_plus j K.m u).mpr (hf u hu)

theorem fadenErreichbarX_plus {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (j : Nat) {K0 K : FadenMaschine D} (h : FadenErreichbarX P O p Tg K0 K) :
    FadenErreichbarX P O (p + j) Tg (K0.plus j) (K.plus j) := by
  induction h with
  | start => exact .start
  | schritt K K' _ hs ih => exact .schritt _ _ ih (fadenSchrittX_plus j hs)

/-- The start of the thread machine has no counter. -/
theorem fadenStart_plus (j : Nat) (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (lebt0 : Faden → Bool) :
    (FadenStart P sp init lebt0).plus j = FadenStart P sp init lebt0 := by
  simp only [FadenMaschine.plus, FadenStart, rufStartG_plus]

/-- **Every thread machine reached over GX at budget `p` is, shifted, reached at every larger budget.** -/
theorem fadenErreichbarX_budget {P : Programm D} {O : Orakel D} {p : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    (j : Nat) {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)} {lebt0 : Faden → Bool}
    {K : FadenMaschine D} (h : FadenErreichbarX P O p Tg (FadenStart P sp init lebt0) K) :
    FadenErreichbarX P O (p + j) Tg (FadenStart P sp init lebt0) (K.plus j) := by
  have := fadenErreichbarX_plus j h
  rwa [fadenStart_plus] at this

end Gabbro.Grammatik
