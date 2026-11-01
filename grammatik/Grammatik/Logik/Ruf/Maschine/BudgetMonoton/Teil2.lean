module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG
public import Grammatik.Speichermodell.Maschine.GXMaschine
public import Grammatik.Logik.Ruf.Maschine.BudgetMonoton.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

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

/-! ## 5. Reading the head of a residue -/

/-- The residue is a `forever` loop with its counter. -/
def GRest.istEwig {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .ewig .. => true
  | _ => false

/-- The residue is a `forever` loop with budget left. -/
def GRest.istEwigPos {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .ewig _ (_ + 1) .. => true
  | _ => false

/-- **Shifted by at least one, a loop has budget left.** -/
theorem GRest.plus_istEwigPos (j : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (g : GRest D V l Γ Λ) (h : g.istEwig = true) : (g.plus (j + 1)).istEwigPos = true := by
  cases g <;> simp_all [GRest.istEwig, GRest.istEwigPos, GRest.plus, ← Nat.add_assoc]

/-- A Boolean reading of a residue, read through its own equation. -/
theorem sigmaRest_lies {V : Vertrag D} (F : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}, GRest D V l Γ Λ → Bool)
    {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {g : GRest D V l Γ Λ} (h : x = ⟨l, Γ, Λ, ρ, g⟩) :
    F x.2.2.2.2 = F g := by
  subst h; rfl

end Gabbro.Grammatik
