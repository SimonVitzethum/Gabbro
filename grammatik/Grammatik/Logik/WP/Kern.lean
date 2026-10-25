import Grammatik.Kern.Semantik.Semantik

/-!
# GabbroV over machine G: the weakest-precondition calculus

The program logic of GabbroV, stated over the ONE semantics the goal theorem uses (`execStmt`, `execBlock`,
`execEnd`), not over a second model. Machine G is total: every run ends in an outcome (`Ausgang`), and what would
diverge ends in a budget or progress outcome. So the weakest precondition of a postcondition `Q` over outcomes is
EXACT:

* `wpB b Q σ ρ` holds exactly when the run of `b` from `σ, ρ` ends in an outcome satisfying `Q` (`wpB_exakt`);
* a triple `Gilt Pre b Q` is valid exactly when `Pre` implies `wpB b Q` (`gilt_iff`) -- the calculus is sound and
  complete at once (relative to Lean's logic as the assertion language);
* `Q` ranges over ALL outcomes, so partial correctness (`NurOk`), total correctness (`Normal`), returns, reasons, loop
  exits and named stops are one notion.

The structural rules (sequence, binding, the three loops with their invariant rules, each sound AND complete) let a
proof follow the program instead of unfolding the semantics by hand.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Kalkuel

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- The weakest precondition of a statement for a postcondition over its outcomes. -/
def wpS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execStmt O passes R s σ ρ)

/-- The weakest precondition of a block. -/
def wpB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execBlock O passes R b σ ρ)

/-- The weakest precondition of a block that does not fall off. -/
def wpE {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (Q : EndAusgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  Q (execEnd O passes R e σ ρ)

/-- A triple: from every state meeting `Pre`, the run ends in an outcome meeting `Q`. -/
def Gilt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (Pre : World D → Env D Γ → Prop) (b : Block D V l Γ Λ Λ')
    (Q : Ausgang V l Γ → Prop) : Prop :=
  ∀ σ ρ, Pre σ ρ → wpB O passes R b Q σ ρ

/-- The triple of a block that does not fall off. -/
def GiltE {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (Pre : World D → Env D Γ → Prop) (e : Endblock D V l Γ Λ)
    (Q : EndAusgang V l Γ → Prop) : Prop :=
  ∀ σ ρ, Pre σ ρ → wpE O passes R e Q σ ρ

/-- **Exactness**: the weakest precondition is the run's outcome meeting `Q`. -/
theorem wpB_exakt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ')
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R b Q σ ρ ↔ Q (execBlock O passes R b σ ρ) := Iff.rfl

/-- **Soundness and completeness at once**: a triple holds exactly when its precondition implies the weakest
    precondition, and exactly when every run from `Pre` meets `Q`. -/
theorem gilt_iff {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (Pre : World D → Env D Γ → Prop)
    (b : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop) :
    Gilt O passes R Pre b Q ↔ ∀ σ ρ, Pre σ ρ → Q (execBlock O passes R b σ ρ) := Iff.rfl

/-- Consequence. -/
theorem gilt_konsequenz {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {Pre Pre' : World D → Env D Γ → Prop}
    {b : Block D V l Γ Λ Λ'} {Q Q' : Ausgang V l Γ → Prop} (h : Gilt O passes R Pre b Q)
    (hp : ∀ σ ρ, Pre' σ ρ → Pre σ ρ) (hq : ∀ o, Q o → Q' o) : Gilt O passes R Pre' b Q' :=
  fun σ ρ hpre => hq _ (h σ ρ (hp σ ρ hpre))

/-- Conjunction of two triples over the same block. -/
theorem gilt_und {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {Pre : World D → Env D Γ → Prop}
    {b : Block D V l Γ Λ Λ'} {Q Q' : Ausgang V l Γ → Prop} (h : Gilt O passes R Pre b Q)
    (h' : Gilt O passes R Pre b Q') : Gilt O passes R Pre b (fun o => Q o ∧ Q' o) :=
  fun σ ρ hpre => ⟨h σ ρ hpre, h' σ ρ hpre⟩

/-! ## Outcome postconditions -/

/-- Partial correctness: a normal end meets `Post`; every other outcome is allowed. -/
def NurOk {l : Bool} {Γ : Ctx} (Post : World D → Env D Γ → Prop) : Ausgang V l Γ → Prop
  | .ok σ ρ => Post σ ρ
  | _ => True

/-- Total correctness of a straight block: it ends normally, in a state meeting `Post`. -/
def Normal {l : Bool} {Γ : Ctx} (Post : World D → Env D Γ → Prop) : Ausgang V l Γ → Prop
  | .ok σ ρ => Post σ ρ
  | _ => False

/-- A body returns a value meeting `Post` (the total correctness of a function body). -/
def Kehrt {l : Bool} {Γ : Ctx} (Post : World D → ErgVal D V.erg → Prop) : EndAusgang V l Γ → Prop
  | .zurueck σ v => Post σ v
  | _ => False

/-! ## Sequence and binding -/

/-- The postcondition a statement owes in front of the rest of its block. -/
def weiterB {l : Bool} {Γ : Ctx} {Λ' Λ'' : List (Res D)} (rest : Block D V l Γ Λ' Λ'') (Q : Ausgang V l Γ → Prop) :
    Ausgang V l Γ → Prop
  | .ok σ' ρ' => wpB O passes R rest Q σ' ρ'
  | o => Q o

/-- **Sequence**: `s; rest` meets `Q` exactly when `s` ends normally in a state where `rest` meets `Q`, or ends
    otherwise in an outcome meeting `Q`. -/
theorem wpB_cons {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (.cons s rest) Q σ ρ ↔ wpS O passes R s (weiterB O passes R rest Q) σ ρ := by
  unfold wpB wpS
  simp only [execBlock]
  cases execStmt O passes R s σ ρ <;> rfl

/-- **Binding** `let x = e; rest`: the rest runs with the value in front, the outcome seen without it. -/
theorem wpB_bind {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (.bind e rest) Q σ ρ ↔
      wpB O passes R rest (fun o => Q o.schrumpf) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := Iff.rfl

/-- The empty block ends normally where it started. -/
theorem wpB_nil {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (Block.nil (D := D) (V := V) (l := l) (Λ := Λ)) Q σ ρ ↔ Q (.ok σ ρ) := Iff.rfl

end Kalkuel

/-! ## The loops: invariant rules, sound and complete -/

section Schleifen

variable {τ : Ty} {Γ : Ctx} {l : Bool}

/-- What one pass of a `traverse` owes its invariant: continue with the invariant at the rest of the indices, end the
    loop through the loop's own check, or leave the loop with an outcome meeting `Q`. -/
def TraverseSchritt (inv : World D → Env D Γ → World D × Bool) (Q : Ausgang V l Γ → Prop)
    (I : List (Wert D τ) → World D → Env D Γ → Prop) (ks : List (Wert D τ)) :
    Ausgang V true (τ :: Γ) → Prop
  | .ok σ' ρ' => I ks σ' ρ'.tail
  | .next _ σ' ρ' => I ks σ' ρ'.tail
  | .leave _ σ' ρ' =>
    Q (if (inv σ' ρ'.tail).2 = true then .ok (inv σ' ρ'.tail).1 ρ'.tail else .logik .schleife)
  | .zurueck σ' v => Q (.zurueck σ' v)
  | .why σ' r => Q (.why σ' r)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- **The `traverse` rule.** An invariant `I` over the indices still to visit: it holds at the start; at the end of
    the indices the loop's own check gives `Q`; a failing check gives `Q`; every pass from the invariant meets
    `TraverseSchritt`. Then the loop meets `Q`. -/
theorem traverse_regel (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (Q : Ausgang V l Γ → Prop)
    (I : List (Wert D τ) → World D → Env D Γ → Prop)
    (hEnde : ∀ σ ρ, I [] σ ρ → Q (if (inv σ ρ).2 = true then .ok (inv σ ρ).1 ρ else .logik .schleife))
    (hBruch : ∀ k ks σ ρ, I (k :: ks) σ ρ → (inv σ ρ).2 = false → Q (.logik .schleife))
    (hSchritt : ∀ k ks σ ρ, I (k :: ks) σ ρ → (inv σ ρ).2 = true →
      TraverseSchritt inv Q I ks (schritt (inv σ ρ).1 (.cons k ρ))) :
    ∀ ks σ ρ, I ks σ ρ → Q (traverseLauf schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil => intro σ ρ h; exact hEnde σ ρ h
  | cons k ks ih =>
    intro σ ρ h
    unfold traverseLauf
    by_cases hc : (inv σ ρ).2 = false
    · rw [if_pos hc]; exact hBruch k ks σ ρ h hc
    · rw [if_neg hc]
      have hc' : (inv σ ρ).2 = true := by simpa using hc
      have hs := hSchritt k ks σ ρ h hc'
      revert hs
      cases schritt (inv σ ρ).1 (.cons k ρ) with
      | ok σ' ρ' => exact fun hs => ih _ _ hs
      | next _ σ' ρ' => exact fun hs => ih _ _ hs
      | leave _ σ' ρ' => exact id
      | zurueck σ' v => exact id
      | why σ' r => exact id
      | logik e => exact id
      | hardware e => exact id

/-- **The `traverse` rule is complete**: the invariant "the rest of the loop meets `Q`" satisfies every premise. -/
theorem traverse_vollstaendig (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) (Q : Ausgang V l Γ → Prop) :
    let I : List (Wert D τ) → World D → Env D Γ → Prop := fun ks σ ρ => Q (traverseLauf schritt inv ks σ ρ)
    (∀ σ ρ, I [] σ ρ → Q (if (inv σ ρ).2 = true then .ok (inv σ ρ).1 ρ else .logik .schleife)) ∧
    (∀ k ks σ ρ, I (k :: ks) σ ρ → (inv σ ρ).2 = false → Q (.logik .schleife)) ∧
    (∀ k ks σ ρ, I (k :: ks) σ ρ → (inv σ ρ).2 = true →
      TraverseSchritt inv Q I ks (schritt (inv σ ρ).1 (.cons k ρ))) := by
  refine ⟨fun σ ρ h => h, fun k ks σ ρ h hc => ?_, fun k ks σ ρ h hc => ?_⟩
  · simpa [traverseLauf, hc] using h
  · have hc' : ¬ (inv σ ρ).2 = false := by simp [hc]
    simp only [traverseLauf, hc', if_false] at h
    revert h
    cases schritt (inv σ ρ).1 (.cons k ρ) <;> exact id

/-- What one pass of a `retry`/`forever` owes: continue with the invariant at one pass less, or leave the loop with
    an outcome meeting `Q`. -/
def PassSchritt (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop) (n : Nat) :
    Ausgang V true Γ → Prop
  | .ok σ' ρ' => I n σ' ρ'
  | .next _ σ' ρ' => I n σ' ρ'
  | .leave _ σ' ρ' => Q (.ok σ' ρ')
  | .zurueck σ' v => Q (.zurueck σ' v)
  | .why σ' r => Q (.why σ' r)
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- **The `retry` rule.** An invariant over the passes left: the exit condition met gives `Q`; at zero passes left the
    overflow block meets `Q`; a pass from the invariant meets `PassSchritt`. -/
theorem retry_regel (schritt : World D → Env D Γ → Ausgang V true Γ) (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop)
    (hFertig : ∀ n σ ρ, I n σ ρ → (bis σ ρ).2 = true → Q (.ok (bis σ ρ).1 ρ))
    (hUeber : ∀ σ ρ, I 0 σ ρ → (bis σ ρ).2 = false → Q (ueberlauf (bis σ ρ).1 ρ))
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ → (bis σ ρ).2 = false → PassSchritt Q I n (schritt (bis σ ρ).1 ρ)) :
    ∀ n σ ρ, I n σ ρ → Q (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero =>
    intro σ ρ h
    unfold retryLauf
    by_cases hb : (bis σ ρ).2 = true
    · rw [if_pos hb]; exact hFertig 0 σ ρ h hb
    · rw [if_neg hb]; exact hUeber σ ρ h (by simpa using hb)
  | succ n ih =>
    intro σ ρ h
    unfold retryLauf
    by_cases hb : (bis σ ρ).2 = true
    · rw [if_pos hb]; exact hFertig _ σ ρ h hb
    · rw [if_neg hb]
      have hs := hSchritt n σ ρ h (by simpa using hb)
      revert hs
      cases schritt (bis σ ρ).1 ρ with
      | ok σ' ρ' => exact fun hs => ih _ _ hs
      | next _ σ' ρ' => exact fun hs => ih _ _ hs
      | leave _ σ' ρ' => exact id
      | zurueck σ' v => exact id
      | why σ' r => exact id
      | logik e => exact id
      | hardware e => exact id

/-- **The `retry` rule is complete.** -/
theorem retry_vollstaendig (schritt : World D → Env D Γ → Ausgang V true Γ) (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) (Q : Ausgang V l Γ → Prop) :
    let I : Nat → World D → Env D Γ → Prop := fun n σ ρ => Q (retryLauf schritt bis ueberlauf n σ ρ)
    (∀ n σ ρ, I n σ ρ → (bis σ ρ).2 = true → Q (.ok (bis σ ρ).1 ρ)) ∧
    (∀ σ ρ, I 0 σ ρ → (bis σ ρ).2 = false → Q (ueberlauf (bis σ ρ).1 ρ)) ∧
    (∀ n σ ρ, I (n + 1) σ ρ → (bis σ ρ).2 = false → PassSchritt Q I n (schritt (bis σ ρ).1 ρ)) := by
  refine ⟨fun n σ ρ h hb => ?_, fun σ ρ h hb => ?_, fun n σ ρ h hb => ?_⟩
  · cases n <;> simpa [retryLauf, hb] using h
  · simpa [retryLauf, hb] using h
  · simp only [retryLauf, hb, Bool.false_eq_true, if_false] at h
    revert h
    cases schritt (bis σ ρ).1 ρ <;> exact id

/-- **The `forever` rule.** An invariant over the passes the environment still gives: at zero the progress stop meets
    `Q`; a failing loop invariant gives `Q`; a pass from the invariant meets `PassSchritt`. -/
theorem forever_regel (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) (Q : Ausgang V l Γ → Prop) (I : Nat → World D → Env D Γ → Prop)
    (hNull : ∀ σ ρ, I 0 σ ρ → Q (.hardware (.fortschritt a)))
    (hBruch : ∀ n σ ρ, I (n + 1) σ ρ → (inv σ ρ).2 = false → Q (.logik .schleife))
    (hSchritt : ∀ n σ ρ, I (n + 1) σ ρ → (inv σ ρ).2 = true → PassSchritt Q I n (schritt (inv σ ρ).1 ρ)) :
    ∀ n σ ρ, I n σ ρ → Q (foreverLauf a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ h; exact hNull σ ρ h
  | succ n ih =>
    intro σ ρ h
    unfold foreverLauf
    by_cases hc : (inv σ ρ).2 = false
    · rw [if_pos hc]; exact hBruch n σ ρ h hc
    · rw [if_neg hc]
      have hs := hSchritt n σ ρ h (by simpa using hc)
      revert hs
      cases schritt (inv σ ρ).1 ρ with
      | ok σ' ρ' => exact fun hs => ih _ _ hs
      | next _ σ' ρ' => exact fun hs => ih _ _ hs
      | leave _ σ' ρ' => exact id
      | zurueck σ' v => exact id
      | why σ' r => exact id
      | logik e => exact id
      | hardware e => exact id

/-- **The `forever` rule is complete.** -/
theorem forever_vollstaendig (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) (Q : Ausgang V l Γ → Prop) :
    let I : Nat → World D → Env D Γ → Prop := fun n σ ρ => Q (foreverLauf a schritt inv n σ ρ)
    (∀ σ ρ, I 0 σ ρ → Q (.hardware (.fortschritt a))) ∧
    (∀ n σ ρ, I (n + 1) σ ρ → (inv σ ρ).2 = false → Q (.logik .schleife)) ∧
    (∀ n σ ρ, I (n + 1) σ ρ → (inv σ ρ).2 = true → PassSchritt Q I n (schritt (inv σ ρ).1 ρ)) := by
  refine ⟨fun σ ρ h => h, fun n σ ρ h hc => ?_, fun n σ ρ h hc => ?_⟩
  · simpa [foreverLauf, hc] using h
  · have hc' : ¬ (inv σ ρ).2 = false := by simp [hc]
    simp only [foreverLauf, hc', if_false] at h
    revert h
    cases schritt (inv σ ρ).1 ρ <;> exact id

end Schleifen

end Gabbro.Grammatik.WP
