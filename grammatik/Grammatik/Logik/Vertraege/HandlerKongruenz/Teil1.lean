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
module

public import Grammatik.Kern.Semantik.Semantik

@[expose] public section



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
    (c : Option Ty) (m : Fehlermarke D) :
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
  · exact Or.inr ⟨m, by rw [h1]; simp only [Fehlermarke.schrumpf_zuAusgang], hE⟩

theorem AusgangUnter.schrumpfArm {c : Option Ty} {o₁ o₂ : Ausgang V l (ArmCtx Γ c)}
    (h : AusgangUnter Er o₁ o₂) :
    AusgangUnter Er (Ausgang.schrumpfArm c o₁) (Ausgang.schrumpfArm c o₂) := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg _ h)
  · exact Or.inr ⟨m, by rw [h1]; simp only [Fehlermarke.schrumpfArm_zuAusgang], hE⟩

theorem AusgangUnter.mapWelt {f : World D → World D} {o₁ o₂ : Ausgang V l Γ}
    (h : AusgangUnter Er o₁ o₂) :
    AusgangUnter Er (o₁.mapWelt f) (o₂.mapWelt f) := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg _ h)
  · exact Or.inr ⟨m, by rw [h1]; simp only [Fehlermarke.mapWelt_zuAusgang], hE⟩

theorem EndUnter.schrumpf {τ : Ty} {o₁ o₂ : EndAusgang V l (τ :: Γ)}
    (h : EndUnter Er o₁ o₂) : EndUnter Er o₁.schrumpf o₂.schrumpf := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg EndAusgang.schrumpf h)
  · exact Or.inr ⟨m, by rw [h1]; simp only [Fehlermarke.schrumpf_zuEnd], hE⟩

theorem EndUnter.zuAusgang {o₁ o₂ : EndAusgang V l Γ} (h : EndUnter Er o₁ o₂) :
    AusgangUnter Er o₁.zuAusgang o₂.zuAusgang := by
  rcases h with h | ⟨m, h1, hE⟩
  · exact Or.inl (congrArg EndAusgang.zuAusgang h)
  · exact Or.inr ⟨m, by rw [h1]; simp only [Fehlermarke.zuAusgang_zuEnd], hE⟩

theorem AusgangUnter.ite {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : Ausgang V l Γ}
    (ha : AusgangUnter Er a₁ a₂) (hb : AusgangUnter Er b₁ b₂) :
    AusgangUnter Er (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

theorem EndUnter.ite {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : EndAusgang V l Γ}
    (ha : EndUnter Er a₁ a₂) (hb : EndUnter Er b₁ b₂) :
    EndUnter Er (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

theorem EndUnter.dite {c : Prop} [Decidable c] {a₁ a₂ : c → EndAusgang V l Γ}
    {b₁ b₂ : ¬c → EndAusgang V l Γ} (ha : ∀ h, EndUnter Er (a₁ h) (a₂ h))
    (hb : ∀ h, EndUnter Er (b₁ h) (b₂ h)) :
    EndUnter Er (dite c a₁ b₁) (dite c a₂ b₂) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]; exact ha h
  · rw [dif_neg h, dif_neg h]; exact hb h

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
          | why σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

/-- A consuming run with congruent bodies: like `traverseLauf_kongruent`,
    by induction on the fuel. Selection, invariant and measure are shared;
    every failing check is `.logik .schleife` on both sides. -/
theorem verbrauchLauf_kongruent {l : Bool} {Γ : Ctx} (t : D.Tab)
    (s₁ s₂ : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ, AusgangUnter Er (s₁ σ ρ) (s₂ σ ρ)) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ),
      AusgangUnter Er
        (verbrauchLauf (l := l) t s₁ inv sel massW bound fuel σ ρ)
        (verbrauchLauf (l := l) t s₂ inv sel massW bound fuel σ ρ)
  | 0, σ, ρ => Or.inl rfl
  | n + 1, σ, ρ => by
      simp only [verbrauchLauf]
      by_cases hc : (inv σ ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact Or.inl rfl
      · rw [if_neg hc, if_neg hc]
        obtain ⟨σr, w, b⟩ := sel (inv σ ρ).1 ρ
        cases w with
        | none =>
            cases b with
            | false => exact Or.inl rfl
            | true => exact Or.inl rfl
        | some v =>
            obtain ⟨σm, m⟩ := massW σr ρ
            rcases hs σm (.cons v ρ) with h | ⟨m', h1, hE⟩
            · rw [h]
              cases hx : s₂ σm (Env.cons v ρ) with
              | ok σ' ρ' =>
                  by_cases hfall : 0 ≤ (massW σ' ρ'.tail).2 ∧
                      (massW σ' ρ'.tail).2 ≤ bound ∧ (massW σ' ρ'.tail).2 < m
                  · rw [if_pos hfall, if_pos hfall]
                    exact verbrauchLauf_kongruent t s₁ s₂ inv sel massW bound
                      hs n (massW σ' ρ'.tail).1 ρ'.tail
                  · rw [if_neg hfall, if_neg hfall]; exact Or.inl rfl
              | next hl σ' ρ' =>
                  by_cases hfall : 0 ≤ (massW σ' ρ'.tail).2 ∧
                      (massW σ' ρ'.tail).2 ≤ bound ∧ (massW σ' ρ'.tail).2 < m
                  · rw [if_pos hfall, if_pos hfall]
                    exact verbrauchLauf_kongruent t s₁ s₂ inv sel massW bound
                      hs n (massW σ' ρ'.tail).1 ρ'.tail
                  · rw [if_neg hfall, if_neg hfall]; exact Or.inl rfl
              | leave hl σ' ρ' =>
                  by_cases hfall : 0 ≤ (massW σ' ρ'.tail).2 ∧
                      (massW σ' ρ'.tail).2 ≤ bound ∧ (massW σ' ρ'.tail).2 < m
                  · rw [if_pos hfall, if_pos hfall]
                    by_cases hc' : (inv σ' ρ'.tail).2 = true
                    · rw [if_pos hc', if_pos hc']; exact Or.inl rfl
                    · rw [if_neg hc', if_neg hc']; exact Or.inl rfl
                  · rw [if_neg hfall, if_neg hfall]; exact Or.inl rfl
              | zurueck σ' v => exact Or.inl rfl
              | why σ' r => exact Or.inl rfl
              | logik e => exact Or.inl rfl
              | hardware e => exact Or.inl rfl
            · exact Or.inr ⟨m', by rw [h1]; cases m' <;> rfl, hE⟩

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
          | why σ' r => exact Or.inl rfl
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
          | why σ' r => exact Or.inl rfl
          | logik e => exact Or.inl rfl
          | hardware e => exact Or.inl rfl
        · exact Or.inr ⟨m, by rw [h1]; cases m <;> rfl, hE⟩

end Schleifen

/-! ## 4. THE CONGRUENCE -/

section Kongruenz

variable {V : Vertrag D} (O : Orakel D) (passes : Nat)
  (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {Er : Fehlermarke D → Prop}

end Kongruenz
end Gabbro.Grammatik
