import Grammatik.Logik.WP.Regeln2

/-!
# GabbroV over machine G: fallible calls, tagged matches, indirect calls

`let x = f(args) else (e) { … }; rest` (a callee with a reason channel), `match v { C => … }` over a tagged value
(arm by arm), and a call through a function pointer.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Regeln3

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- What a fallible binding call makes of the callee's outcome: the value runs the rest, a reason runs the `else`. -/
def bindRufElseB {Λ' Λ'' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) Λ') (rest : Block D V l (τ :: Γ) Λ' Λ'')
    (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpB O passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why σ' r => wpE O passes R err (fun eo => Q eo.schrumpf.zuAusgang) σ' (.cons r ρ)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- **`let x = f(args) else (e) { … }; rest`**, exactly. -/
theorem wpB_bindCallElse {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ)) (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (.bindCallElse f args he hp hr err rest) Q σ ρ ↔
      bindRufElseB O passes R he err rest Q ρ
        (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)) := by
  unfold wpB
  simp only [execBlock]
  cases R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) <;> rfl

/-- **`let x = f(args) else (e) { … }; rest`** against a specification. -/
theorem wpB_bindCallElse_spez {S : Spez D} (hR : Erfuellt S R) {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : 0 < D.gruende f) (err : Endblock D V l (.why (D.gruende f) :: Γ) (nach D f Λ))
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (h : ∀ out, S f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) out →
      bindRufElseB O passes R he err rest Q ρ out) :
    wpB O passes R (.bindCallElse f args he hp hr err rest) Q σ ρ :=
  (wpB_bindCallElse O passes R f args he hp hr err rest Q σ ρ).2 (h _ (hR f _ _))

/-- The arms of a `match` over a tagged value: the arm of the value's case. -/
def wpArms {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execArms O passes R arms v σ ρ)

/-- The arm of case `0` is the first block, with the payload in front (if the case has one). -/
theorem wpArms_null {Λ Λ' : List (Res D)} {c : Option (Int × Int)} {cs : List (Option (Int × Int))}
    (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs) (h : 0 < (c :: cs).length)
    (nutz : Nutzlast c) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpArms O passes R (.cons b rest) ⟨⟨0, h⟩, nutz⟩ Q σ ρ ↔
      wpB O passes R b (fun o => Q (o.schrumpfArm c)) σ (armEnv nutz ρ) := Iff.rfl

/-- The arm of case `i + 1` is the arm of case `i` among the rest. -/
theorem wpArms_succ {Λ Λ' : List (Res D)} {c : Option (Int × Int)} {cs : List (Option (Int × Int))}
    (b : Block D V l (ArmCtx Γ c) Λ Λ') (rest : Arms D V l Γ Λ Λ' cs) (i : Nat) (h : i + 1 < (c :: cs).length)
    (nutz : Nutzlast ((c :: cs).get ⟨i + 1, h⟩)) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpArms O passes R (.cons b rest) ⟨⟨i + 1, h⟩, nutz⟩ Q σ ρ ↔
      wpArms O passes R rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ Q σ ρ := Iff.rfl

/-- `match v { … }` over a tagged value. -/
theorem wpS_onTag {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (v : Expr D Γ Λ (.sum cs))
    (arms : Arms D V l Γ Λ Λ' cs) (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpS O passes R (.onTag v arms) Q σ ρ ↔
      wpArms O passes R arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) Q (σ.lese Λ v.orte) ρ := Iff.rfl

end Regeln3

end Gabbro.Grammatik.WP
