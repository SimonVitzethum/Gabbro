/-
  File:      Grammatik/HandlerKongruenz.lean
  Subject:   **THE CONGRUENCE OF `execStmt` / `execBlock` / `execEnd` IN ITS
             HANDLER** -- two handlers that differ only where BOTH answer an
             error give body runs that differ only where BOTH are errors.

  WHY IT EXISTS. The sequential semantics of a body is parametric in the
  handler `R` that answers a call (`Semantik.lean`, section `Rumpf`). Every
  obligation the user proves is quantified over handlers in a CLASS --
  `KoerperGutS` (SperreFuss.lean) over `RespektiertRahmen ∧ OhneVorbedingung`
  and `RespektiertRahmen ∧ OhneLogik` -- and the handler the closing theorem
  speaks about, `rufAt` (the model's own call), is in NEITHER: it answers
  `logik (vorbedingung g)` at every key whose `requires` fails and
  `logik (abstieg g)` at depth `0`. Relating the body run under `rufAt` to the
  body run under a handler that IS in the class is what this file is for; so
  is relating `rufAt` at two DEPTHS (`rufAt_tiefer`, section 5).

  THE SHAPE, and why it is the shape. Every error outcome of the semantics
  propagates through every constructor VERBATIM, with its tag: `.logik e` and
  `.hardware e` are treated identically by `Ausgang.schrumpf`,
  `.schrumpfArm`, `.mapWelt`, `EndAusgang.schrumpf`, `.zuAusgang`, by
  `traverseLauf`, `retryLauf`, `foreverLauf` and by every `match` in
  `execStmt`/`execBlock`/`execEnd`. Nothing in the semantics CATCHES an error
  (`bindCallElse` catches a REASON, which is not an error). So if the two
  handlers agree at a key, the two runs go on together; and the first key at
  which they disagree ends both runs, each with its own mark, and the rest of
  the body is not run by either.

  That is exactly what `AusgangUnter`/`EndUnter` say: the outcome under `R₁`
  is the outcome under `R₂`, or it is an error whose mark lies in the set `Er`
  the handler premise carries -- "`R₁` is `R₂` except that it may FAIL EARLY,
  and only in the named way". `Er` is a parameter because the two consumers
  want different sets:

  * part 4's `logik` condition takes `R₁ = rufAt n` and `R₂` the same handler
    patched into `OhneLogik`; `Er` is "a `logik` mark";
  * depth monotonicity takes `R₁ = rufAt n`, `R₂ = rufAt (n+1)`; `Er` is
    "an `abstieg` mark".

  WHY ONE-SIDED AND NOT SYMMETRIC. A symmetric form ("both are errors, with
  related marks") does NOT cover depth monotonicity: where `rufAt n` answers
  `abstieg`, `rufAt (n+1)` may answer `ok`, so the second side is no error at
  all. The one-sided form covers both, and the symmetric statement follows
  from TWO instances of it (once in each direction) where it holds.

  WHAT IT DOES NOT DO. It says nothing about which of the two runs is "right",
  nothing about worlds or traces, and nothing about the handler classes: a
  frame fact about `rufAt` (`RespektiertRahmen`) is a different statement and
  is NOT proved here (see `RufLogik.lean` and the report).
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The error mark -- the one thing the three outcome types share -/

/-- **An error outcome's tag.** `Ausgang`, `EndAusgang` and `RufAusgang` each
    have exactly two error constructors and they carry the same two payloads
    (`Semantik.lean`: "es gibt keinen dritten"). A mark is that payload
    without the outcome type around it, so that one relation can speak about
    all three. -/
inductive Fehlermarke (D : Deklaration) where
  | logik (e : Logik D)
  | hardware (e : Hardware D)

/-- The mark as a call outcome. -/
def Fehlermarke.zuRuf {f : D.Fn} : Fehlermarke D → RufAusgang f
  | .logik e => .logik e
  | .hardware e => .hardware e

section Marke

variable {V : Vertrag D}

/-- The mark as a statement outcome. -/
def Fehlermarke.zuAusgang {l : Bool} {Γ : Ctx} : Fehlermarke D → Ausgang V l Γ
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- The mark as a terminal-block outcome. -/
def Fehlermarke.zuEnd {l : Bool} {Γ : Ctx} : Fehlermarke D → EndAusgang V l Γ
  | .logik e => .logik e
  | .hardware e => .hardware e

@[simp] theorem Fehlermarke.schrumpf_zuAusgang {l : Bool} {Γ : Ctx} {τ : Ty}
    (m : Fehlermarke D) : (m.zuAusgang : Ausgang V l (τ :: Γ)).schrumpf = m.zuAusgang := by
  cases m <;> rfl

@[simp] theorem Fehlermarke.schrumpfArm_zuAusgang {l : Bool} {Γ : Ctx}
    (c : Option (Int × Int)) (m : Fehlermarke D) :
    Ausgang.schrumpfArm (V := V) (l := l) (Γ := Γ) c m.zuAusgang = m.zuAusgang := by
  cases c with
  | none => rfl
  | some p => cases m <;> rfl

@[simp] theorem Fehlermarke.mapWelt_zuAusgang {l : Bool} {Γ : Ctx}
    (f : World D → World D) (m : Fehlermarke D) :
    (m.zuAusgang : Ausgang V l Γ).mapWelt f = m.zuAusgang := by
  cases m <;> rfl

@[simp] theorem Fehlermarke.schrumpf_zuEnd {l : Bool} {Γ : Ctx} {τ : Ty}
    (m : Fehlermarke D) : (m.zuEnd : EndAusgang V l (τ :: Γ)).schrumpf = m.zuEnd := by
  cases m <;> rfl

@[simp] theorem Fehlermarke.zuAusgang_zuEnd {l : Bool} {Γ : Ctx} (m : Fehlermarke D) :
    (m.zuEnd : EndAusgang V l Γ).zuAusgang = m.zuAusgang := by
  cases m <;> rfl

end Marke

/-! ## 2. The relation on outcomes, and the handler premise -/

section Rel

variable {V : Vertrag D}

/-- **Two call outcomes under `Er`**: equal, or both errors with related
    marks. -/
def RufUnter (Er : Fehlermarke D → Prop) {f : D.Fn}
    (a₁ a₂ : RufAusgang f) : Prop :=
  a₁ = a₂ ∨ ∃ m : Fehlermarke D, a₁ = m.zuRuf ∧ Er m

/-- **Two statement outcomes under `Er`**. -/
def AusgangUnter (Er : Fehlermarke D → Prop) {l : Bool} {Γ : Ctx}
    (o₁ o₂ : Ausgang V l Γ) : Prop :=
  o₁ = o₂ ∨ ∃ m : Fehlermarke D, o₁ = m.zuAusgang ∧ Er m

/-- **Two terminal-block outcomes under `Er`**. -/
def EndUnter (Er : Fehlermarke D → Prop) {l : Bool} {Γ : Ctx}
    (o₁ o₂ : EndAusgang V l Γ) : Prop :=
  o₁ = o₂ ∨ ∃ m : Fehlermarke D, o₁ = m.zuEnd ∧ Er m

variable {Er : Fehlermarke D → Prop} {l : Bool} {Γ : Ctx}

theorem AusgangUnter.refl (o : Ausgang V l Γ) : AusgangUnter Er o o := Or.inl rfl
theorem EndUnter.refl (o : EndAusgang V l Γ) : EndUnter Er o o := Or.inl rfl

theorem AusgangUnter.schrumpf {τ : Ty} {o₁ o₂ : Ausgang V l (τ :: Γ)}
    (h : AusgangUnter Er o₁ o₂) : AusgangUnter Er o₁.schrumpf o₂.schrumpf := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg Ausgang.schrumpf h)
  · exact Or.inr ⟨m, by rw [h1]; simp, hE⟩

theorem AusgangUnter.schrumpfArm {c : Option (Int × Int)} {o₁ o₂ : Ausgang V l (ArmCtx Γ c)}
    (h : AusgangUnter Er o₁ o₂) :
    AusgangUnter Er (Ausgang.schrumpfArm c o₁) (Ausgang.schrumpfArm c o₂) := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg _ h)
  · exact Or.inr ⟨m, by rw [h1]; simp, hE⟩

theorem AusgangUnter.mapWelt {f : World D → World D} {o₁ o₂ : Ausgang V l Γ}
    (h : AusgangUnter Er o₁ o₂) :
    AusgangUnter Er (o₁.mapWelt f) (o₂.mapWelt f) := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg _ h)
  · exact Or.inr ⟨m, by rw [h1]; simp, hE⟩

theorem EndUnter.schrumpf {τ : Ty} {o₁ o₂ : EndAusgang V l (τ :: Γ)}
    (h : EndUnter Er o₁ o₂) : EndUnter Er o₁.schrumpf o₂.schrumpf := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg EndAusgang.schrumpf h)
  · exact Or.inr ⟨m, by rw [h1]; simp, hE⟩

theorem EndUnter.zuAusgang {o₁ o₂ : EndAusgang V l Γ} (h : EndUnter Er o₁ o₂) :
    AusgangUnter Er o₁.zuAusgang o₂.zuAusgang := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg EndAusgang.zuAusgang h)
  · exact Or.inr ⟨m, by rw [h1]; simp, hE⟩

theorem AusgangUnter.ite {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : Ausgang V l Γ}
    (ha : AusgangUnter Er a₁ a₂) (hb : AusgangUnter Er b₁ b₂) :
    AusgangUnter Er (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

theorem AusgangUnter.dite {c : Prop} [Decidable c] {a₁ a₂ : c → Ausgang V l Γ}
    {b₁ b₂ : ¬c → Ausgang V l Γ} (ha : ∀ h, AusgangUnter Er (a₁ h) (a₂ h))
    (hb : ∀ h, AusgangUnter Er (b₁ h) (b₂ h)) :
    AusgangUnter Er (dite c a₁ b₁) (dite c a₂ b₂) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]; exact ha h
  · rw [dif_neg h, dif_neg h]; exact hb h

end Rel

/-- **THE HANDLER PREMISE**: at every key the two handlers agree, or both
    answer an error and the two marks stand in `Er`. -/
def HandlerUnter (Er : Fehlermarke D → Prop)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)), RufUnter Er (R₁ g σ ρ) (R₂ g σ ρ)

/-! ## 3. The three loop combinators -/

section Schleifen

variable {V : Vertrag D} {Er : Fehlermarke D → Prop}

theorem traverseLauf_kongruent {l : Bool} {Γ : Ctx} {τ : Ty}
    (s₁ s₂ : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, AusgangUnter Er (s₁ σ ρ) (s₂ σ ρ)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (traverseLauf (l := l) s₁ inv ks σ ρ)
        (traverseLauf (l := l) s₂ inv ks σ ρ)
  | [], σ, ρ => Or.inl rfl
  | k :: ks, σ, ρ => by
      simp only [traverseLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact Or.inl rfl
      · rw [if_neg hc, if_neg hc]
        rcases hs (inv σ ρ).1 (.cons k ρ) with h | ⟨m, h1, hE⟩
        · rw [h]
          cases hx : s₂ (inv σ ρ).1 (Env.cons k ρ) with
          | ok σ' ρ' => exact traverseLauf_kongruent s₁ s₂ inv hs ks σ' ρ'.tail
          | next hl σ' ρ' => exact traverseLauf_kongruent s₁ s₂ inv hs ks σ' ρ'.tail
          | leave hl σ' ρ' => exact Or.inl rfl
          | zurueck σ' v => exact Or.inl rfl
          | grund σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

theorem retryLauf_kongruent {l : Bool} {Γ : Ctx}
    (s₁ s₂ : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool)
    (u₁ u₂ : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, AusgangUnter Er (s₁ σ ρ) (s₂ σ ρ))
    (hu : ∀ σ ρ, AusgangUnter Er (u₁ σ ρ) (u₂ σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (retryLauf s₁ bis u₁ n σ ρ) (retryLauf s₂ bis u₂ n σ ρ)
  | 0, σ, ρ => by
      simp only [retryLauf]
      exact AusgangUnter.ite (Or.inl rfl) (hu (bis σ ρ).1 ρ)
  | n + 1, σ, ρ => by
      simp only [retryLauf]
      by_cases hc : (bis σ ρ).2 = true
      · rw [if_pos hc, if_pos hc]; exact Or.inl rfl
      · rw [if_neg hc, if_neg hc]
        rcases hs (bis σ ρ).1 ρ with h | ⟨m, h1, hE⟩
        · rw [h]
          cases hx : s₂ (bis σ ρ).1 ρ with
          | ok σ' ρ' => exact retryLauf_kongruent s₁ s₂ bis u₁ u₂ hs hu n σ' ρ'
          | next hl σ' ρ' => exact retryLauf_kongruent s₁ s₂ bis u₁ u₂ hs hu n σ' ρ'
          | leave hl σ' ρ' => exact Or.inl rfl
          | zurueck σ' v => exact Or.inl rfl
          | grund σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

theorem foreverLauf_kongruent {l : Bool} {Γ : Ctx} (a : D.Annahme)
    (s₁ s₂ : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, AusgangUnter Er (s₁ σ ρ) (s₂ σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (foreverLauf (l := l) a s₁ inv n σ ρ) (foreverLauf (l := l) a s₂ inv n σ ρ)
  | 0, σ, ρ => Or.inl rfl
  | n + 1, σ, ρ => by
      simp only [foreverLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact Or.inl rfl
      · rw [if_neg hc, if_neg hc]
        rcases hs (inv σ ρ).1 ρ with h | ⟨m, h1, hE⟩
        · rw [h]
          cases hx : s₂ (inv σ ρ).1 ρ with
          | ok σ' ρ' => exact foreverLauf_kongruent a s₁ s₂ inv hs n σ' ρ'
          | next hl σ' ρ' => exact foreverLauf_kongruent a s₁ s₂ inv hs n σ' ρ'
          | leave hl σ' ρ' => exact Or.inl rfl
          | zurueck σ' v => exact Or.inl rfl
          | grund σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

end Schleifen

/-! ## 4. THE CONGRUENCE -/

section Kongruenz

variable {V : Vertrag D} (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}

mutual

/-- **A statement under two handlers.** -/
theorem Stmt.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execStmt O passes R₁ s σ ρ) (execStmt O passes R₂ s σ ρ)
  | .ite c t e, σ, ρ => by
      simp only [execStmt]
      exact AusgangUnter.ite (Block.kongruent hR t _ ρ)
        (Block.kongruent hR e _ ρ)
  | .onOption o p a, σ, ρ => by
      simp only [execStmt]
      cases hv : (eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ : Option _) with
      | none => exact Block.kongruent hR a _ ρ
      | some k => exact (Block.kongruent hR p _ (.cons k ρ)).schrumpf
  | .onTag v arms, σ, ρ => by
      simp only [execStmt]
      exact Arms.kongruent hR arms _ _ ρ
  | .onGrund r arms, σ, ρ => by
      simp only [execStmt]
      exact GrundArms.kongruent hR arms _ _ ρ
  | .locks L hr body, σ, ρ => by
      simp only [execStmt]
      exact (Block.kongruent hR body (σ.nimmt L) ρ).mapWelt
  | .breaking i body, σ, ρ => by
      simp only [execStmt]
      exact Block.kongruent hR body σ ρ
  | .traverse t inv body, σ, ρ => by
      simp only [execStmt]
      exact traverseLauf_kongruent _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ') _ σ ρ
  | .retry n bis body ueber, σ, ρ => by
      simp only [execStmt]
      exact retryLauf_kongruent _ _ _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ')
        (fun σ' ρ' => Block.kongruent hR ueber σ' ρ') n σ ρ
  | .forever a inv body, σ, ρ => by
      simp only [execStmt]
      exact foreverLauf_kongruent _ _ _ _
        (fun σ' ρ' => Block.kongruent hR body σ' ρ') passes σ ρ
  | .call g args hp hr, σ, ρ => by
      simp only [execStmt]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]; exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .callInd p args hp hr, σ, ρ => by
      simp only [execStmt]
      generalize (eval (σ.lese Λ (p.orte ++ args.orte)) p
          (σ.lese Λ (p.orte ++ args.orte)) ρ) = w
      obtain ⟨g, hg⟩ := w
      · dsimp only
        rcases hR g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          h | ⟨m, h1, hE⟩
        · rw [h]; exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .assignSlot .., _, _ => Or.inl rfl
  | .assignDurch .., _, _ => Or.inl rfl
  | .assignGlob .., _, _ => Or.inl rfl
  | .schreibBytes .., _, _ => Or.inl rfl
  | .assignVar .., _, _ => Or.inl rfl
  | .uebergang .., _, _ => Or.inl rfl
  | .axiomCall .., _, _ => Or.inl rfl
  | .regSchreib .., _, _ => Or.inl rfl
  | .transition .., _, _ => Or.inl rfl
  | .publish .., _, _ => Or.inl rfl
  | .advances .., _, _ => Or.inl rfl
  | .retires .., _, _ => Or.inl rfl
  | .ret .., _, _ => Or.inl rfl
  | .retGrund .., _, _ => Or.inl rfl
  | .leave .., _, _ => Or.inl rfl
  | .next .., _, _ => Or.inl rfl

/-- **A block under two handlers.** -/
theorem Block.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execBlock O passes R₁ b σ ρ) (execBlock O passes R₂ b σ ρ)
  | .nil, σ, ρ => Or.inl rfl
  | .cons s rest, σ, ρ => by
      simp only [execBlock]
      rcases Stmt.kongruent hR s σ ρ with h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : execStmt O passes R₂ s σ ρ with
        | ok σ' ρ' => exact Block.kongruent hR rest σ' ρ'
        | zurueck σ' v => exact Or.inl rfl
        | grund σ' r => exact Or.inl rfl
        | leave hl σ' ρ' => exact Or.inl rfl
        | next hl σ' ρ' => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bind e rest, σ, ρ => by
      simp only [execBlock]
      exact (Block.kongruent hR rest _ _).schrumpf
  | .bindCall g args he hp hr rest, σ, ρ => by
      simp only [execBlock]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : R₂ g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => exact (Block.kongruent hR rest σ' _).schrumpf
        | grund σ' r => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [execBlock]
      generalize (eval (σ.lese Λ (p.orte ++ args.orte)) p
          (σ.lese Λ (p.orte ++ args.orte)) ρ) = w
      obtain ⟨g, hg⟩ := w
      · dsimp only
        rcases hR g (σ.lese Λ (p.orte ++ args.orte))
            (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
              (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          h | ⟨m, h1, hE⟩
        · rw [h]
          cases hx : R₂ g (σ.lese Λ (p.orte ++ args.orte))
              (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
                (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v => exact (Block.kongruent hR rest σ' _).schrumpf
          | grund σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [execBlock]
      rcases hR g (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : R₂ g (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        | ok σ' v => exact (Block.kongruent hR rest σ' _).schrumpf
        | grund σ' r =>
            exact ((Endblock.kongruent hR err σ' _).schrumpf).zuAusgang
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bindAxiom a args he hp hw hL hg rest, σ, ρ => by
      simp only [execBlock]
      cases hx : axiomAntwort O a (σ.lese Λ args.orte)
          (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ2 ov =>
        cases ov with
        | none => exact Or.inl rfl
        | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .regLies r hr rest, σ, ρ => by
      simp only [execBlock]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | none => exact Or.inl rfl
      | some v =>
          exact AusgangUnter.ite ((Block.kongruent hR rest σ (.cons v ρ)).schrumpf)
            (Or.inl rfl)
  | .regLiesElse r hr zusage sonst rest, σ, ρ => by
      simp only [execBlock]
      cases hx : einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | none => exact Or.inl rfl
      | some v =>
          exact AusgangUnter.ite
            ((Block.kongruent hR rest _ (.cons v ρ)).schrumpf)
            ((Endblock.kongruent hR sonst _ ρ).zuAusgang)
  | .awaits g hg hw hL rest, σ, ρ => by
      simp only [execBlock]
      by_cases hs : O.sichtbar g σ = true
      · rw [if_pos hs, if_pos hs]
        exact (Block.kongruent hR rest _ _).schrumpf
      · rw [if_neg hs, if_neg hs]; exact Or.inl rfl
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execBlock]
      exact (Block.kongruent hR rest _ _).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [execBlock]
      exact AusgangUnter.dite (fun _ => (Block.kongruent hR rest _ _).schrumpf)
        (fun _ => (Endblock.kongruent hR sonst _ ρ).zuAusgang)
  | .pruefung c sonst rest, σ, ρ => by
      simp only [execBlock]
      exact AusgangUnter.ite (Block.kongruent hR rest _ ρ)
        ((Endblock.kongruent hR sonst _ ρ).zuAusgang)
  | .gleit op a b lo hi rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => exact Or.inl rfl
      | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .gleitLit q lo hi rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (bruch q) with
      | none => exact Or.inl rfl
      | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .gleitVon e lo hi rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (gleitAusInt
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => exact Or.inl rfl
      | some v => exact (Block.kongruent hR rest _ _).schrumpf
  | .gleitNarrow e lo hi sonst rest, σ, ρ => by
      simp only [execBlock]
      cases hx : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => exact (Endblock.kongruent hR sonst _ ρ).zuAusgang
      | some v => exact (Block.kongruent hR rest _ _).schrumpf

/-- **A terminal block under two handlers** -- the form the two consumers
    use, since a function body is an `Endblock`. -/
theorem Endblock.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → ∀ (σ : World D) (ρ : Env D Γ),
      EndUnter Er (execEnd O passes R₁ b σ ρ) (execEnd O passes R₂ b σ ρ)
  | .ret .., _, _ => Or.inl rfl
  | .retGrund .., _, _ => Or.inl rfl
  | .leave .., _, _ => Or.inl rfl
  | .next .., _, _ => Or.inl rfl
  | .cons s rest, σ, ρ => by
      simp only [execEnd]
      rcases Stmt.kongruent hR s σ ρ with h | ⟨m, h1, hE⟩
      · rw [h]
        cases hx : execStmt O passes R₂ s σ ρ with
        | ok σ' ρ' => exact Endblock.kongruent hR rest σ' ρ'
        | zurueck σ' v => exact Or.inl rfl
        | grund σ' r => exact Or.inl rfl
        | leave hl σ' ρ' => exact Or.inl rfl
        | next hl σ' ρ' => exact Or.inl rfl
        | logik e => exact Or.inl rfl
        | hardware e => exact Or.inl rfl
      · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩
  | .bind e rest, σ, ρ => by
      simp only [execEnd]
      exact (Endblock.kongruent hR rest _ _).schrumpf

theorem Arms.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execArms O passes R₁ a v σ ρ) (execArms O passes R₂ a v σ ρ)
  | .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [execArms]
      exact (Block.kongruent hR b σ (armEnv nutz ρ)).schrumpfArm
  | .cons b rest, ⟨⟨i + 1, hk⟩, nutz⟩, σ, ρ => by
      simp only [execArms]
      exact Arms.kongruent hR rest _ σ ρ

theorem GrundArms.kongruent (hR : HandlerUnter Er R₁ R₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er (execGrund O passes R₁ a r σ ρ) (execGrund O passes R₂ a r σ ρ)
  | .nil, r, _, _ => r.elim0
  | .cons b rest, ⟨0, _⟩, σ, ρ => by
      simp only [execGrund]
      exact Block.kongruent hR b σ ρ
  | .cons b rest, ⟨i + 1, hk⟩, σ, ρ => by
      simp only [execGrund]
      exact GrundArms.kongruent hR rest _ σ ρ

end

end Kongruenz

/-! ## 5. ONE UNFOLDING OF `rufAt`, and its congruence

    `rufAt P O passes (n+1)` IS one entry-contract test, one body run against
    the handler `rufAt P O passes n`, one exit-contract test and the owed
    invariants (`rufAt_succ_eq` -- `rfl`). Naming that step as a function of
    the handler is what lets the congruence above be used at the call level:
    the two consumers both compare `rufAt` with SOME other handler in exactly
    this shape. -/

/-- **One unfolding of `rufAt`, with the handler as a parameter.** -/
def rufSchritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) : RufAusgang f :=
  let σ := σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
  if wahr? (eval σ (P.requires f) σ ρ) = false then .logik (.vorbedingung f) else
  match execEnd (V := vertragVon D f) O passes R (P.rumpf f) σ ρ with
  | EndAusgang.zurueck σ' v =>
      let σ' := σ'.lese (vertragVon D f).ende (P.ensures f).orte
      if wahr? (eval σ (P.ensures f) σ' (ergEnv (D.erg f) v ρ)) = false then
        .logik (.nachbedingung f)
      else
        let σ' := (D.invs.filter (schuldet f)).foldl
          (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ'
        match D.invs.find? (fun i => schuldet f i && !wahr? (eval σ' (P.invariante i) σ' .nil)) with
        | Option.some i => .logik (.invariante i)
        | Option.none => .ok σ' v
  | .grund σ' r => .grund σ' r
  | .leave h _ _ => absurd h (by decide)
  | .next h _ _ => absurd h (by decide)
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- **`rufAt` at depth `n+1` IS that step over `rufAt` at depth `n`** -- by
    definition, so `rfl`. -/
theorem rufAt_succ_eq (P : Programm D) (O : Orakel D) (passes n : Nat) :
    rufAt P O passes (n + 1) = rufSchritt P O passes (rufAt P O passes n) := rfl

/-- **THE CONGRUENCE AT THE CALL LEVEL.** Two handlers that differ only where
    the first answers an error give CALLS that differ only where the first is
    an error -- the entry test, the exit test and the invariant test are the
    same computation on both sides, and the body run is related by
    `Endblock.kongruent`. -/
theorem rufSchritt_kongruent {Er : Fehlermarke D → Prop}
    {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : HandlerUnter Er R₁ R₂) (P : Programm D) (O : Orakel D) (passes : Nat)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    RufUnter Er (rufSchritt P O passes R₁ f σ ρ) (rufSchritt P O passes R₂ f σ ρ) := by
  have hcong := Endblock.kongruent (V := vertragVon D f) O passes R₁ R₂ hR (P.rumpf f)
    (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ
  simp only [rufSchritt]
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte)
      (P.requires f) (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = false
  · rw [if_pos hq, if_pos hq]; exact Or.inl rfl
  · rw [if_neg hq, if_neg hq]
    rcases hcong with h | ⟨mk, h1, hE⟩
    · rw [h]
      cases hx : execEnd (V := vertragVon D f) O passes R₂ (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ with
      | zurueck σ' v => exact Or.inl rfl
      | grund σ' r => exact Or.inl rfl
      | leave hl σ' ρ' => exact Or.inl rfl
      | next hl σ' ρ' => exact Or.inl rfl
      | logik e => exact Or.inl rfl
      | hardware e => exact Or.inl rfl
    · exact Or.inr ⟨mk, by rw [h1]; cases mk <;> rfl, hE⟩

#print axioms Gabbro.Grammatik.rufSchritt_kongruent
#print axioms Gabbro.Grammatik.Stmt.kongruent
#print axioms Gabbro.Grammatik.Block.kongruent
#print axioms Gabbro.Grammatik.Endblock.kongruent

end Gabbro.Grammatik
