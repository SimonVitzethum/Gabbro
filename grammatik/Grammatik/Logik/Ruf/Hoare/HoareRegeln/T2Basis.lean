/- Part 2 of 4 of `HoareRegeln` (split by instrumente/teile/lean-teilen.py; the umbrella `HoareRegeln.lean` imports all parts). -/
module
public import Grammatik.Logik.Ruf.Hoare.HoareRegeln.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

theorem traverseKey {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (blockEq : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (ks : List (Wert D (.index (D.count t)))) (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R₁ (Stmt.traverse (V := V) (l := l) (Γ := Γ) (Λ := Λ) t inv body) σ' ρ' =
    execStmt O passes R₂ (Stmt.traverse (V := V) (l := l) (Γ := Γ) (Λ := Λ) t inv body) σ' ρ' := by
      have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEq σ ρ
      have key : ∀ (ks : List (Wert D (.index (D.count t)))) (σ' : World D) (ρ' : Env D Γ),
          traverseLauf (V := V) (l := l) (τ := .index (D.count t)) (Γ := Γ)
            (fun σ ρ => execBlock O passes R₁ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            ks σ' ρ' =
          traverseLauf (V := V) (l := l) (τ := .index (D.count t)) (Γ := Γ)
            (fun σ ρ => execBlock O passes R₂ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            ks σ' ρ' := by
        intro ks
        induction ks with
        | nil => intro σ' ρ'; simp only [traverseLauf]
        | cons k ks ih =>
            intro σ' ρ'
            simp only [traverseLauf]
            cases hsch : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₁ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') with
            | ok σ'' ρ'' =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.ok σ'' ρ'' := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch, ih]
            | zurueck σ'' v =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.zurueck σ'' v := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | why σ'' r =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.why σ'' r := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | leave h σ'' ρ'' =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.leave h σ'' ρ'' := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | next h σ'' ρ'' =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.next h σ'' ρ'' := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch, ih]
            | logik e =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.logik e := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
            | hardware e =>
                have hsame : execBlock (l := true) (Γ := .index (D.count t) :: Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 (.cons k ρ') = Ausgang.hardware e := by
                  rw [← hsch]; exact (hb' _ _).symm
                simp only [hsame, hsch]
      simp only [execStmt]
      exact key _ _ _
theorem retryKey {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueberlauf : Block D V l Γ Λ Λ)
    (blockEqB : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (blockEqU : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ ueberlauf σ ρ = execBlock O passes R₂ ueberlauf σ ρ)
    (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R₁ (Stmt.retry (V := V) (l := l) (Γ := Γ) (Λ := Λ) n bis body ueberlauf) σ' ρ' =
    execStmt O passes R₂ (Stmt.retry (V := V) (l := l) (Γ := Γ) (Λ := Λ) n bis body ueberlauf) σ' ρ' := by
      have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEqB σ ρ
      have hu' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEqU σ ρ
      have key : ∀ (m : Nat) (σ' : World D) (ρ' : Env D Γ),
          retryLauf (fun σ ρ => execBlock O passes R₁ body σ ρ)
            (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
            (fun σ ρ => execBlock O passes R₁ ueberlauf σ ρ) m σ' ρ' =
          retryLauf (fun σ ρ => execBlock O passes R₂ body σ ρ)
            (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
            (fun σ ρ => execBlock O passes R₂ ueberlauf σ ρ) m σ' ρ' := by
        intro m
        induction m with
        | zero => intro σ' ρ'; simp only [retryLauf, hu']
        | succ m ih =>
            intro σ' ρ'
            simp only [retryLauf]
            cases hsch : execBlock (l := true) (Γ := Γ) O passes R₁ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' with
          | ok σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.ok σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
              cases hb2 : wahr? (eval (σ'.lese Λ bis.orte) bis (σ'.lese Λ bis.orte) ρ') with
              | true => simp only [hb2, if_true, ih, hu']
              | false =>
                  have hF : ¬(false = true) := by decide
                  simp only [hb2, if_neg hF]
                  rw [ih]
          | zurueck σ'' v =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.zurueck σ'' v := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | why σ'' r =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.why σ'' r := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | leave h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.leave h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | next h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.next h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch, ih]
          | logik e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.logik e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | hardware e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ))) σ' ρ').1 ρ' = Ausgang.hardware e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
      simp only [execStmt, key]
theorem foreverKey {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ)
    (blockEq : ∀ (σ : World D) (ρ : Env D _),
      execBlock O passes R₁ body σ ρ = execBlock O passes R₂ body σ ρ)
    (σ' : World D) (ρ' : Env D Γ) :
    execStmt O passes R₁ (Stmt.forever (V := V) (l := l) (Γ := Γ) (Λ := Λ) a inv body) σ' ρ' =
    execStmt O passes R₂ (Stmt.forever (V := V) (l := l) (Γ := Γ) (Λ := Λ) a inv body) σ' ρ' := by
      have hb' : ∀ (σ : World D) (ρ : Env D _), _ := fun σ ρ => blockEq σ ρ
      have key : ∀ (m : Nat) (σ' : World D) (ρ' : Env D Γ),
          foreverLauf (V := V) (l := l) (Γ := Γ) a (fun σ ρ => execBlock O passes R₁ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            m σ' ρ' =
          foreverLauf (V := V) (l := l) (Γ := Γ) a (fun σ ρ => execBlock O passes R₂ body σ ρ)
            (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
            m σ' ρ' := by
        intro m
        induction m with
        | zero => intro σ' ρ'; rfl
        | succ m ih =>
            intro σ' ρ'
            simp only [foreverLauf]
            cases hsch : execBlock (l := true) (Γ := Γ) O passes R₁ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' with
          | ok σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.ok σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch, ih]
          | zurueck σ'' v =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.zurueck σ'' v := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | why σ'' r =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.why σ'' r := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | leave h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.leave h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | next h σ'' ρ'' =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.next h σ'' ρ'' := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch, ih]
          | logik e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.logik e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
          | hardware e =>
              have hsame : execBlock (l := true) (Γ := Γ) O passes R₂ body ((fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) σ' ρ').1 ρ' = Ausgang.hardware e := by
                rw [← hsch]; exact (hb' _ _).symm
              simp only [hsame, hsch]
      simp only [execStmt, key]
end Gabbro.Grammatik
