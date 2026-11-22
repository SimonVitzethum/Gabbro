module
public import Bruecke.Zertifikat.Satz
import all Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
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

end HA

end Gabbro.Bruecke
