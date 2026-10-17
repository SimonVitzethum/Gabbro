/- Part 4 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.RufAdaequatRufG.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Abbruch

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem ohneAbbruch_schrumpf {τ : Ty} {o : Ausgang V l (τ :: Γ)} (h : o.ohneAbbruch) :
    o.schrumpf.ohneAbbruch := by
  cases o <;> simp_all [Ausgang.schrumpf, Ausgang.ohneAbbruch]

theorem ohneAbbruch_schrumpfArm (c : Option (Int × Int)) {o : Ausgang V l (ArmCtx Γ c)}
    (h : o.ohneAbbruch) : (o.schrumpfArm c).ohneAbbruch := by
  cases c with
  | none => exact h
  | some p => exact ohneAbbruch_schrumpf h

theorem ohneAbbruch_mapWelt {o : Ausgang V l Γ} (g : World D → World D) (h : o.ohneAbbruch) :
    (o.mapWelt g).ohneAbbruch := by
  cases o <;> simp_all [Ausgang.mapWelt, Ausgang.ohneAbbruch]

theorem zuAusgang_ohneAbbruch (hl : l = false) (o : EndAusgang V l Γ) :
    o.zuAusgang.ohneAbbruch := by
  cases o <;> simp_all [EndAusgang.zuAusgang, Ausgang.ohneAbbruch]

/-- `traverseLauf` consumes every `leave`/`next` of its body. -/
theorem traverseLauf_ohneAbbruch {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      (traverseLauf (l := l) schritt inv ks σ ρ).ohneAbbruch
  | [], σ, ρ => by
      simp only [traverseLauf]
      split <;> trivial
  | k :: ks, σ, ρ => by
      simp only [traverseLauf]
      split
      · trivial
      · split
        · exact traverseLauf_ohneAbbruch schritt inv ks _ _
        · exact traverseLauf_ohneAbbruch schritt inv ks _ _
        · split <;> trivial
        all_goals trivial

/-- `retryLauf` consumes every `leave`/`next` of its body; its overflow block
    is the only other exit. -/
theorem retryLauf_ohneAbbruch (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hu : ∀ σ ρ, (ueberlauf σ ρ).ohneAbbruch) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), (retryLauf schritt bis ueberlauf n σ ρ).ohneAbbruch
  | 0, σ, ρ => by
      simp only [retryLauf]
      split
      · trivial
      · exact hu _ ρ
  | n + 1, σ, ρ => by
      simp only [retryLauf]
      split
      · trivial
      · split
        · exact retryLauf_ohneAbbruch schritt bis ueberlauf hu n _ _
        · exact retryLauf_ohneAbbruch schritt bis ueberlauf hu n _ _
        all_goals trivial

/-- `traverseLauf` returns only where its body returns. -/
theorem traverseLauf_nicht_zurueck {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ (σ σ' : World D) (ρ : Env D (τ :: Γ)) (v : ErgVal D V.erg),
      schritt σ ρ ≠ .zurueck σ' v) :
    ∀ (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
      traverseLauf (l := l) schritt inv ks σ ρ ≠ .zurueck σ' v
  | [], σ, σ', ρ, v => by
      simp only [traverseLauf]
      split <;> intro h <;> cases h
  | k :: ks, σ, σ', ρ, v => by
      simp only [traverseLauf]
      split
      · intro h; cases h
      · split
        · exact traverseLauf_nicht_zurueck schritt inv hs ks _ _ _ _
        · exact traverseLauf_nicht_zurueck schritt inv hs ks _ _ _ _
        · split <;> intro h <;> cases h
        · rename_i σ2 v2 heq; exact absurd heq (hs _ _ _ _)
        all_goals intro h; cases h

/-- `retryLauf` returns only where its body or its overflow block returns. -/
theorem retryLauf_nicht_zurueck (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg), schritt σ ρ ≠ .zurueck σ' v)
    (hu : ∀ (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg), ueberlauf σ ρ ≠ .zurueck σ' v) :
    ∀ (n : Nat) (σ σ' : World D) (ρ : Env D Γ) (v : ErgVal D V.erg),
      retryLauf schritt bis ueberlauf n σ ρ ≠ .zurueck σ' v
  | 0, σ, σ', ρ, v => by
      simp only [retryLauf]
      split
      · intro h; cases h
      · exact hu _ σ' ρ v
  | n + 1, σ, σ', ρ, v => by
      simp only [retryLauf]
      split
      · intro h; cases h
      · split
        · exact retryLauf_nicht_zurueck schritt bis ueberlauf hs hu n _ _ _ _
        · exact retryLauf_nicht_zurueck schritt bis ueberlauf hs hu n _ _ _ _
        · intro h; cases h
        · rename_i σ2 v2 heq; exact absurd heq (hs _ _ _ _)
        all_goals intro h; cases h

end Abbruch
/-- A covered leaf never exits abruptly. -/
theorem BlattG.ohneAbbruch {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) (σ : World D) (ρ : Env D Γ) :
    (execStmt O passes R s σ ρ).ohneAbbruch := by
  cases h <;> simp only [execStmt] <;> (try split) <;> trivial

/-! ### The sequential outcomes the simulations follow -/

section Aus

variable {V : Vertrag D} {Γ : Ctx}

/-- The abrupt part of an outcome: kind (`true` for `leave`), world,
    environment. -/
def Ausgang.abb? {l : Bool} : Ausgang V l Γ → Option (Bool × World D × Env D Γ)
  | .leave _ σ ρ => some (true, σ, ρ)
  | .next _ σ ρ => some (false, σ, ρ)
  | _ => none

theorem abb_none_of {l : Bool} {o : Ausgang V l Γ} (h : o.ohneAbbruch) : o.abb? = none := by
  cases o <;> simp_all [Ausgang.ohneAbbruch, Ausgang.abb?]

theorem abb_schrumpf {l : Bool} {τ : Ty} {o : Ausgang V l (τ :: Γ)} {w : Bool} {σ' : World D}
    {ρ' : Env D Γ} (h : o.schrumpf.abb? = some (w, σ', ρ')) :
    ∃ ρ1 : Env D (τ :: Γ), o.abb? = some (w, σ', ρ1) ∧ ρ' = ρ1.tail := by
  cases o with
  | leave _ σ ρ =>
    simp only [Ausgang.schrumpf, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ρ, rfl, rfl⟩
  | next _ σ ρ =>
    simp only [Ausgang.schrumpf, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ρ, rfl, rfl⟩
  | _ => simp [Ausgang.schrumpf, Ausgang.abb?] at h

theorem abb_mapWelt {l : Bool} (g : World D → World D) {o : Ausgang V l Γ} {w : Bool} {σ' : World D}
    {ρ' : Env D Γ} (h : (o.mapWelt g).abb? = some (w, σ', ρ')) :
    ∃ σ1, o.abb? = some (w, σ1, ρ') ∧ σ' = g σ1 := by
  cases o with
  | leave _ σ ρ =>
    simp only [Ausgang.mapWelt, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨σ, rfl, rfl⟩
  | next _ σ ρ =>
    simp only [Ausgang.mapWelt, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨σ, rfl, rfl⟩
  | _ => simp [Ausgang.mapWelt, Ausgang.abb?] at h

/-- The two ends of a frame: a return with a value, or a reason. -/
inductive EndeW (V : Vertrag D) where
  | zurueck (σ : World D) (v : ErgVal D V.erg)
  | why (σ : World D) (r : Fin V.gruende)

/-- The world a frame ends in. -/
def EndeW.welt : EndeW V → World D
  | .zurueck σ _ => σ
  | .why σ _ => σ

/-- The end part of an outcome. -/
def Ausgang.ende? {l : Bool} : Ausgang V l Γ → Option (EndeW V)
  | .zurueck σ v => some (.zurueck σ v)
  | .why σ r => some (.why σ r)
  | _ => none

/-- The end part of an end-block outcome. -/
def EndAusgang.ende? {l : Bool} : EndAusgang V l Γ → Option (EndeW V)
  | .zurueck σ v => some (.zurueck σ v)
  | .why σ r => some (.why σ r)
  | _ => none

theorem ende_schrumpf {l : Bool} {τ : Ty} (o : Ausgang V l (τ :: Γ)) :
    o.schrumpf.ende? = o.ende? := by
  cases o <;> rfl

theorem ende_schrumpfArm {l : Bool} (c : Option (Int × Int)) (o : Ausgang V l (ArmCtx Γ c)) :
    (o.schrumpfArm c).ende? = o.ende? := by
  cases c with
  | none => rfl
  | some p => exact ende_schrumpf o

theorem endEnde_schrumpf {l : Bool} {τ : Ty} (o : EndAusgang V l (τ :: Γ)) :
    o.schrumpf.ende? = o.ende? := by
  cases o <;> rfl

theorem ende_zuAusgang {l : Bool} (o : EndAusgang V l Γ) : o.zuAusgang.ende? = o.ende? := by
  cases o <;> rfl

theorem ende_mapWelt_none {l : Bool} (g : World D → World D) {o : Ausgang V l Γ}
    (h : o.ende? = none) : (o.mapWelt g).ende? = none := by
  cases o <;> simp_all [Ausgang.mapWelt, Ausgang.ende?]

theorem EndeW.zuAusgang_ne_ok {l : Bool} (o : EndAusgang V l Γ) (σ' : World D) (ρ' : Env D Γ) :
    o.zuAusgang ≠ .ok σ' ρ' := by
  cases o <;> simp [EndAusgang.zuAusgang]

end Aus
theorem execBlock_cons_abb (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    {σ : World D} {ρ : Env D Γ} {x : Bool × World D × Env D Γ}
    (h : (execBlock O passes R (.cons s rest) σ ρ).abb? = some x) :
    (execStmt O passes R s σ ρ).abb? = some x ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        (execBlock O passes R rest σ1 ρ1).abb? = some x := by
  simp only [execBlock] at h
  generalize execStmt O passes R s σ ρ = o at h ⊢
  cases o with
  | ok σ1 ρ1 => exact Or.inr ⟨σ1, ρ1, rfl, h⟩
  | _ => exact Or.inl h

theorem execBlock_cons_ende (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    {σ : World D} {ρ : Env D Γ} {e : EndeW V}
    (h : (execBlock O passes R (.cons s rest) σ ρ).ende? = some e) :
    (execStmt O passes R s σ ρ).ende? = some e ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        (execBlock O passes R rest σ1 ρ1).ende? = some e := by
  simp only [execBlock] at h
  generalize execStmt O passes R s σ ρ = o at h ⊢
  cases o with
  | ok σ1 ρ1 => exact Or.inr ⟨σ1, ρ1, rfl, h⟩
  | _ => exact Or.inl h

theorem execEnd_cons_ende (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    {σ : World D} {ρ : Env D Γ} {e : EndeW V}
    (h : (execEnd O passes R (.cons s rest) σ ρ).ende? = some e) :
    (execStmt O passes R s σ ρ).ende? = some e ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        (execEnd O passes R rest σ1 ρ1).ende? = some e := by
  simp only [execEnd] at h
  generalize execStmt O passes R s σ ρ = o at h ⊢
  cases o with
  | ok σ1 ρ1 => exact Or.inr ⟨σ1, ρ1, rfl, h⟩
  | _ => exact Or.inl h

/-- `foreverLauf` consumes every `leave`/`next` of its body. -/
theorem foreverLauf_ohneAbbruch {V : Vertrag D} {l : Bool} {Γ : Ctx} (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      (foreverLauf (l := l) a schritt inv n σ ρ).ohneAbbruch
  | 0, σ, ρ => trivial
  | n + 1, σ, ρ => by
      simp only [foreverLauf]
      split
      · trivial
      · split
        · exact foreverLauf_ohneAbbruch a schritt inv n _ _
        · exact foreverLauf_ohneAbbruch a schritt inv n _ _
        all_goals trivial

/-- A covered leaf never ends the frame. -/
theorem BlattG.ende_none {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {s : Stmt D V l Γ Λ Λ'} (h : BlattG s) (σ : World D) (ρ : Env D Γ) :
    (execStmt O passes R s σ ρ).ende? = none := by
  cases h <;> simp only [execStmt] <;> (try split) <;> rfl

/-- `traverseLauf` ends the frame only where its body does. -/
theorem traverseLauf_ende_none {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, (schritt σ ρ).ende? = none) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      (traverseLauf (l := l) schritt inv ks σ ρ).ende? = none
  | [], σ, ρ => by
      simp only [traverseLauf]
      split <;> rfl
  | k :: ks, σ, ρ => by
      simp only [traverseLauf]
      split
      · rfl
      · have h1 := hs (inv σ ρ).1 (.cons k ρ)
        split
        · exact traverseLauf_ende_none schritt inv hs ks _ _
        · exact traverseLauf_ende_none schritt inv hs ks _ _
        · split <;> rfl
        · rename_i heq; rw [heq] at h1; cases h1
        · rename_i heq; rw [heq] at h1; cases h1
        all_goals rfl

/-- `retryLauf` ends the frame only where its body or overflow block does. -/
theorem retryLauf_ende_none {V : Vertrag D} {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, (schritt σ ρ).ende? = none) (hu : ∀ σ ρ, (ueberlauf σ ρ).ende? = none) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      (retryLauf schritt bis ueberlauf n σ ρ).ende? = none
  | 0, σ, ρ => by
      simp only [retryLauf]
      split
      · rfl
      · exact hu _ ρ
  | n + 1, σ, ρ => by
      simp only [retryLauf]
      split
      · rfl
      · have h1 := hs (bis σ ρ).1 ρ
        split
        · exact retryLauf_ende_none schritt bis ueberlauf hs hu n _ _
        · exact retryLauf_ende_none schritt bis ueberlauf hs hu n _ _
        · rfl
        · rename_i heq; rw [heq] at h1; cases h1
        · rename_i heq; rw [heq] at h1; cases h1
        all_goals rfl

/-- `foreverLauf` ends the frame only where its body does. -/
theorem foreverLauf_ende_none {V : Vertrag D} {l : Bool} {Γ : Ctx} (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, (schritt σ ρ).ende? = none) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      (foreverLauf (l := l) a schritt inv n σ ρ).ende? = none
  | 0, σ, ρ => rfl
  | n + 1, σ, ρ => by
      simp only [foreverLauf]
      split
      · rfl
      · have h1 := hs (inv σ ρ).1 ρ
        split
        · exact foreverLauf_ende_none a schritt inv hs n _ _
        · exact foreverLauf_ende_none a schritt inv hs n _ _
        · rfl
        · rename_i heq; rw [heq] at h1; cases h1
        · rename_i heq; rw [heq] at h1; cases h1
        all_goals rfl



/-! ## 6. Normal completion and abrupt exits: the machine reaches the continuation

    As `RufAdaequatG.lean` §7, for any handler `R` and fragment `C`, with a
    log that may GROW (calls log `eintritt`/`rueck`/`grund` events); a call
    is discharged by the callee obligation `RufOk`. Mutually with it, the
    abrupt exits: a block that ends in `leave`/`next` runs to the exit
    statement directly above its continuation (`SimAbbBR`), which the loop
    simulations hand to the loop shim. -/


end Gabbro.Grammatik
