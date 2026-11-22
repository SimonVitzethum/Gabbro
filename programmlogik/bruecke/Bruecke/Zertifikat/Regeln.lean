module
public import Bruecke.Zertifikat.Satz
import all Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
import all Grammatik.Kern.Semantik.Semantik.T1.Teil1
@[expose] public section

/-!
# Further exact weakest-precondition rules: the matches and the choice of an arm

The model's calculus (`Logik/WP/HA/Kern.lean`) has exact rules for sequences, bindings, branches,
returns, locks, narrowing, checks and calls. These are the rules for the three matches (`onTag`,
`onWhy`, `onOption`) and for choosing an arm by its index, read off the model's semantics
(`execStmtHA`, `execArmsHA`, `execGrundHA`). Each is an equivalence: no case is lost. They are proof
support for `gabbrov_wp`, not trust points; every proof that uses them is checked by the kernel.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.WP

variable {D : Deklaration} {V : Vertrag D}

section HA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- The weakest precondition of a tag match's arms at the value `w`. -/
def wpArmsA {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs)
    (w : Wert D (.sum cs)) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execArmsHA S O U A passes R arms w σ ρ)

/-- The weakest precondition of a reason match's arms at the case `r`. -/
def wpGrundA {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execGrundHA S O U A passes R arms r σ ρ)

theorem wpSA_onTag {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (v : Expr D Γ Λ (.sum cs))
    (arms : Arms D V l Γ Λ Λ' cs) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.onTag v arms) Q σ ρ ↔
      wpArmsA S O U A passes R arms (eval (leseA A σ Λ v.orte) v (leseA A σ Λ v.orte) ρ) Q
        (leseA A σ Λ v.orte) ρ := by
  unfold wpSA wpArmsA
  simp only [execStmtHA]

theorem wpSA_onWhy {Λ Λ' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.why n))
    (arms : GrundArms D V l Γ Λ Λ' n) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.onWhy r arms) Q σ ρ ↔
      wpGrundA S O U A passes R arms (eval (leseA A σ Λ r.orte) r (leseA A σ Λ r.orte) ρ) Q
        (leseA A σ Λ r.orte) ρ := by
  unfold wpSA wpGrundA
  simp only [execStmtHA]

theorem wpSA_onOption {Λ Λ' : List (Res D)} {k : Int} (o : Expr D Γ Λ (.opt k))
    (p : Block D V l (.index k :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.onOption o p a) Q σ ρ ↔
      match eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ with
      | Option.some x => wpBA S O U A passes R p (fun out => Q out.schrumpf) (leseA A σ Λ o.orte) (.cons x ρ)
      | Option.none => wpBA S O U A passes R a Q (leseA A σ Λ o.orte) ρ := by
  unfold wpSA wpBA
  simp only [execStmtHA]
  cases eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ <;> rfl

theorem wpArmsA_null {Λ Λ' : List (Res D)} {c : Option Ty} {cs : List (Option Ty)}
    (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs) (h : 0 < (c :: cs).length)
    (nutz : Fall D.Fn D.passt (c :: cs) ⟨0, h⟩) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpArmsA S O U A passes R (.cons b rest) ⟨⟨0, h⟩, nutz⟩ Q σ ρ ↔
      wpBA S O U A passes R b (fun out => Q (out.schrumpfArm _))  σ
        (armEnv (Fall.toNutzlast _ _ _ _ nutz) ρ) := by
  unfold wpArmsA wpBA
  simp only [execArmsHA]

theorem wpArmsA_succ {Λ Λ' : List (Res D)} {c : Option Ty} {cs : List (Option Ty)}
    (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs) (i : Nat) (h : i + 1 < (c :: cs).length)
    (nutz : Fall D.Fn D.passt (c :: cs) ⟨i + 1, h⟩) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpArmsA S O U A passes R (.cons b rest) ⟨⟨i + 1, h⟩, nutz⟩ Q σ ρ ↔
      wpArmsA S O U A passes R rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ Q σ ρ := by
  unfold wpArmsA
  simp only [execArmsHA]

theorem wpGrundA_null {Λ Λ' : List (Res D)} {n : Nat} (b : Block D V l Γ Λ Λ')
    (rest : GrundArms D V l Γ Λ Λ' n) (h : 0 < n + 1) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpGrundA S O U A passes R (.cons b rest) ⟨0, h⟩ Q σ ρ ↔ wpBA S O U A passes R b Q σ ρ := by
  unfold wpGrundA wpBA
  simp only [execGrundHA]

theorem wpGrundA_succ {Λ Λ' : List (Res D)} {n : Nat} (b : Block D V l Γ Λ Λ')
    (rest : GrundArms D V l Γ Λ Λ' n) (i : Nat) (h : i + 1 < n + 1) (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ) :
    wpGrundA S O U A passes R (.cons b rest) ⟨i + 1, h⟩ Q σ ρ ↔
      wpGrundA S O U A passes R rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ Q σ ρ := by
  unfold wpGrundA
  simp only [execGrundHA]

theorem wpSA_breaking {Λ Λ' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpSA S O U A passes R (.breaking i body) Q σ ρ ↔ wpBA S O U A passes R body Q σ ρ := by
  unfold wpSA wpBA
  simp only [execStmtHA]

theorem wpBA_narrowRequired {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpBA S O U A passes R (.narrowRequired e lo' hi' rest) Q σ ρ ↔
      if h : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
          (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi' then
        wpBA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A σ Λ e.orte)
          (.cons ⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
      else Q (.logik .kapazitaet) := by
  unfold wpBA
  simp only [execBlockHA]
  rw [apply_dite Q]

theorem wpEA_narrowRequired {Λ : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (rest : Endblock D V l (.int lo' hi' :: Γ) Λ) (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.narrowRequired e lo' hi' rest) Q σ ρ ↔
      if h : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
          (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi' then
        wpEA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A σ Λ e.orte)
          (.cons ⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
      else Q (.logik .kapazitaet) := by
  unfold wpEA
  simp only [execEndHA]
  rw [apply_dite Q]

theorem wpEA_narrow {Λ : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (sonst : Endblock D V l Γ Λ) (rest : Endblock D V l (.int lo' hi' :: Γ) Λ) (Q : EndAusgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpEA S O U A passes R (.narrow e lo' hi' sonst rest) Q σ ρ ↔
      if h : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
          (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi' then
        wpEA S O U A passes R rest (fun o => Q o.schrumpf) (leseA A σ Λ e.orte)
          (.cons ⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
      else wpEA S O U A passes R sonst Q (leseA A σ Λ e.orte) ρ := by
  unfold wpEA
  simp only [execEndHA]
  rw [apply_dite Q]

/-- **A dependent branch the kernel does not decide**: both branches, each under its condition. -/
theorem dite_faelle {α : Sort _} {G : α → Prop} (c : Prop) [Decidable c] (a : c → α) (b : ¬c → α)
    (ha : ∀ h : c, G (a h)) (hb : ∀ h : ¬c, G (b h)) : G (if h : c then a h else b h) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h

end HA

/-! ## Splitting a symbolic value into its cases -/

/-- A tagged value is its case and its payload. -/
theorem sigma_faelle {α : Type} {β : α → Type} {G : Sigma β → Prop} (w : Sigma β)
    (h : ∀ a b, w = ⟨a, b⟩ → G ⟨a, b⟩) : G w := by
  cases w with
  | mk a b => exact h a b rfl

/-- A tagged value over `n + 1` cases is case `0` with its payload or a later case with its payload. -/
theorem sum_faelle {n : Nat} {β : Fin (n + 1) → Type} {G : Sigma β → Prop} (w : Sigma β)
    (h0 : ∀ b : β 0, w = ⟨0, b⟩ → G ⟨0, b⟩)
    (hs : ∀ (i : Fin n) (b : β i.succ), w = ⟨i.succ, b⟩ → G ⟨i.succ, b⟩) : G w := by
  rcases w with ⟨i, b⟩
  cases i using Fin.cases with
  | zero => exact h0 b rfl
  | succ i => exact hs i b rfl

/-- A case number below `n + 1` is `0` or the successor of one below `n`. -/
theorem fin_faelle {n : Nat} {G : Fin (n + 1) → Prop} (r : Fin (n + 1))
    (h0 : r = 0 → G 0) (hs : ∀ i : Fin n, r = i.succ → G i.succ) : G r := by
  cases r using Fin.cases with
  | zero => exact h0 rfl
  | succ i => exact hs i rfl

/-! ## The return obligation at a known outcome -/

theorem rueckPost_zurueck (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (σ' : World D) (v : ErgVal D (D.erg f)) :
    RueckPost P f σ ρ (.zurueck σ' v) ↔ EnsAmRueck P f σ σ' ρ v ∧ InvAmRueck P f σ' :=
  ⟨fun h => h.1 σ' v rfl, fun h => ⟨fun _ _ e => (by cases e; exact h), fun _ _ e => (by cases e)⟩⟩

theorem rueckPost_why (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (σ' : World D) (r : Fin (D.gruende f)) :
    RueckPost P f σ ρ (.why σ' r) ↔ InvAmRueck P f σ' :=
  ⟨fun h => h.2 σ' r rfl, fun h => ⟨fun _ _ e => (by cases e), fun _ _ e => (by cases e; exact h)⟩⟩

theorem zurueck_ne_logik {l : Bool} {Γ : Ctx} {σ : World D} {v : ErgVal D V.erg} {e : Logik D} :
    (EndAusgang.zurueck σ v : EndAusgang V l Γ) ≠ EndAusgang.logik e := nofun

theorem why_ne_logik {l : Bool} {Γ : Ctx} {σ : World D} {r : Fin V.gruende} {e : Logik D} :
    (EndAusgang.why σ r : EndAusgang V l Γ) ≠ EndAusgang.logik e := nofun

/-- Two `logik` outcomes with different stops differ. -/
theorem logik_ne_logik {l : Bool} {Γ : Ctx} {e e' : Logik D} (h : e ≠ e') :
    (EndAusgang.logik e : EndAusgang V l Γ) ≠ EndAusgang.logik e' :=
  fun h' => h (by cases h'; rfl)

/-- No declared invariant: nothing is owed at a return. -/
theorem invAmRueck_leer {P : Programm D} {f : D.Fn} {σ : World D} (h : D.invs = []) : InvAmRueck P f σ :=
  fun i hi => by rw [h] at hi; cases hi

/-- The return check over the function's own postcondition `e` (`P.ensures f = e`). -/
theorem ensAmRueck_von {P : Programm D} {f : D.Fn} {e : Expr D (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende .bool}
    (h : P.ensures f = e) (σ σ' : World D) (ρ : Env D (D.params f)) (v : ErgVal D (D.erg f)) :
    EnsAmRueck P f σ σ' ρ v ↔ wahr? (eval σ e σ' (ergEnv (D.erg f) v ρ)) = true := by
  unfold EnsAmRueck
  rw [h]

/-! ## The evaluation that chooses an arm -/

theorem eval_var_here {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (σ₀ σ : World D) (x : Wert D τ) (ρ : Env D Γ) :
    eval σ₀ (Expr.var (Λ := Λ) (Var.here (Γ := Γ))) σ (Env.cons x ρ) = x := rfl

theorem eval_var_there {Γ : Ctx} {Λ : List (Res D)} {τ τ' : Ty} (σ₀ σ : World D) (y : Var Γ τ) (x : Wert D τ')
    (ρ : Env D Γ) :
    eval σ₀ (Expr.var (Λ := Λ) (Var.there y)) σ (Env.cons x ρ) = eval σ₀ (Expr.var (Λ := Λ) y) σ ρ := rfl

theorem eval_case {Γ : Ctx} {Λ : List (Res D)} (cs : List (Option Ty)) (i : Fin cs.length)
    (nutz : NutzlastExpr D Γ Λ (cs.get i)) (σ₀ σ : World D) (ρ : Env D Γ) :
    eval σ₀ (Expr.case cs i nutz) σ ρ = ⟨i, Fall.ofNutzlast _ _ _ _ (evalNutz σ₀ nutz σ ρ)⟩ := rfl

end Gabbro.Bruecke
