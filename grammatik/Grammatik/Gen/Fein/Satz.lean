/-
  File:      Grammatik/Gen/Fein/Satz.lean
  Subject:   EVERY FINE CELL OF EVERY PROGRAM IS IN THE UNIVERSE (`feinZellen_uF`): the fine cells of a term are allowed
             by the typing (`moeglich`), for every term of every declaration without foreign bodies, by induction over
             the terms. The cases are GENERATED from the constructor list of the model; each is closed by the lemmas
             below (the type class of an expression child, the loop context of a statement child).
-/
import Grammatik.Gen.Fein.Universum

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik

theorem kopf_lt (τ : Ty) : τ.kopf < 9 := by cases τ <;> simp [Ty.kopf]

theorem kopfOk_none (τ : Ty) : kopfOk none τ.kopf = true := decide_eq_true (kopf_lt τ)

theorem all_nil {α : Type} {p : α → Bool} : ([] : List α).all p = true := rfl

theorem all_cons {α : Type} {p : α → Bool} {x : α} {xs : List α} (h : p x = true) (hs : xs.all p = true) :
    (x :: xs).all p = true := by simp only [List.all_cons, h, Bool.true_and]; exact hs

theorem all_app {α : Type} {p : α → Bool} {xs ys : List α} (h : xs.all p = true) (hs : ys.all p = true) :
    (xs ++ ys).all p = true := by simp [List.all_append, h, hs]

theorem kc {q : Option Nat} {qs : List (Option Nat)} {h : Nat} {hs : List Nat} (h1 : kopfOk q h = true)
    (h2 : koepfeOk qs hs = true) : koepfeOk (q :: qs) (h :: hs) = true := by simp [koepfeOk, h1, h2]

theorem eig_ok {f k : Nat} {l : Bool} {hs : List Nat} {r : Zeile} (hr : zeile f k = some r)
    (h1 : (decide (4 ≤ f) || !l) = true) (h2 : (!r.fremd && (!r.lnoetig || l)) = true)
    (h3 : koepfeOk (exprReqs r.kinder) hs = true) : moeglich ⟨0, f, k, l, hs⟩ = true := by
  simp only [Bool.and_eq_true] at h2
  simp only [moeglich, hr, h1, h2, Bool.and_eq_true, datenOk, h3, and_self, typRegel]

theorem paar_ok {f k : Nat} {l : Bool} {p cf kk : Nat} {r : Zeile} {c : Nat × Option Nat × Option Bool}
    (hr : zeile f k = some r) (h1 : (decide (4 ≤ f) || !l) = true) (h2 : (!r.fremd && (!r.lnoetig || l)) = true)
    (hc : r.kinder[p]? = some c) (hcf : cf = c.1) (h3 : kindOk cf c.2.1 (c.2.2.getD l) kk = true)
    (ht : typRegel ⟨1, f, k, l, [p, cf, kk]⟩ = true := by rfl) :
    moeglich ⟨1, f, k, l, [p, cf, kk]⟩ = true := by
  subst hcf
  simp only [Bool.and_eq_true] at h2
  simp only [moeglich, hr, h1, h2, Bool.and_eq_true, datenOk, hc, beq_self_eq_true, h3, and_self, ht]

variable {D : Deklaration}

/-- **The constructors of `nullHaltig` start at or below zero**: a divisor of `div`/`rem` (`1 ≤ l`) is none of them. -/
theorem nullHaltig_kE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (b : Expr D Γ Λ τ) {l h : Int} (hτ : τ = .int l h)
    (hl : 1 ≤ l) : nullHaltig.contains (kE b) = false := by
  cases b with
  | sdiv hb a b' =>
    injection hτ with h1 _
    simp only [betragMax] at h1
    omega
  | srem hb a b' =>
    injection hτ with h1 _
    simp only [betragMax] at h1
    rcases hb with hb | hb <;> omega
  | _ => first
    | rfl
    | (injection hτ with h1 _; omega)

/-- **The constructors of `nullFest` hold zero**: a divisor of `sdiv`/`srem` (`1 ≤ l ∨ h ≤ -1`) is none of them. -/
theorem nullFest_kE {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (b : Expr D Γ Λ τ) {l h : Int} (hτ : τ = .int l h)
    (hl : 1 ≤ l ∨ h ≤ -1) : nullFest.contains (kE b) = false := by
  cases b with
  | sdiv hb a b' =>
    injection hτ with h1 h2
    simp only [betragMax] at h1 h2
    omega
  | srem hb a b' =>
    injection hτ with h1 h2
    simp only [betragMax] at h1 h2
    rcases hb with hb | hb <;> omega
  | getBytes t f hf n i hlo hhi hL =>
    injection hτ with h1 h2
    have hp : (0 : Int) < 256 ^ n := by
      have := Nat.pow_pos (n := n) (show 0 < 256 by decide); exact_mod_cast this
    omega
  | bor w h0 h0' hw1 hw2 a b' =>
    injection hτ with h1 h2
    have hp : (0 : Int) < 2 ^ w := by
      have := Nat.pow_pos (n := w) (show 0 < 2 by decide); exact_mod_cast this
    omega
  | bxor w h0 h0' hw1 hw2 a b' =>
    injection hτ with h1 h2
    have hp : (0 : Int) < 2 ^ w := by
      have := Nat.pow_pos (n := w) (show 0 < 2 by decide); exact_mod_cast this
    omega
  | _ => rfl

/-- The range rule at the divisor of `div`/`rem`. -/
theorem typRegel_teiler {Γ : Ctx} {Λ : List (Res D)} {l h : Int} (b : Expr D Γ Λ (.int l h)) (hl : 1 ≤ l)
    (k : Nat) (lk : Bool) (hk : k = 16 ∨ k = 17) : typRegel ⟨1, 0, k, lk, [1, 0, kE b]⟩ = true := by
  have h0 := nullHaltig_kE b rfl hl
  rcases hk with rfl | rfl <;> simp only [typRegel, h0, Bool.and_false, Bool.not_false, Bool.true_and] <;> rfl

/-- The range rule at the divisor of `sdiv`/`srem`. -/
theorem typRegel_steiler {Γ : Ctx} {Λ : List (Res D)} {l h : Int} (b : Expr D Γ Λ (.int l h)) (hl : 1 ≤ l ∨ h ≤ -1)
    (k : Nat) (lk : Bool) (hk : k = 18 ∨ k = 19) : typRegel ⟨1, 0, k, lk, [1, 0, kE b]⟩ = true := by
  have h0 := nullFest_kE b rfl hl
  rcases hk with rfl | rfl <;> simp only [typRegel, h0, Bool.and_false, Bool.not_false, Bool.and_true] <;> rfl

theorem kopf_frei {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) : kopfOk none (tk e) = true :=
  kopfOk_none τ

theorem kE_erg {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) : ergPasst (kE e) τ.kopf = true := by
  cases e <;> first | rfl | exact decide_eq_true (kopf_lt _)

theorem kE_kind (q : Option Nat) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (hq : kopfOk q τ.kopf = true) (lk : Bool) : kindOk 0 q lk (kE e) = true := by
  unfold kindOk
  rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
  exact List.any_eq_true.2 ⟨τ.kopf, List.mem_range.2 (kopf_lt τ), by rw [hq, kE_erg e]; rfl⟩

theorem kN_kind {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)} (x : NutzlastExpr D Γ Λ o) (lk : Bool) :
    kindOk 1 none lk (kN x) = true := by cases x <;> rfl

theorem kA_kind {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (x : Args D Γ Λ τs) (lk : Bool) :
    kindOk 2 none lk (kA x) = true := by cases x <;> rfl

theorem kR_kind {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} (x : ErgExpr D Γ Λ o) (lk : Bool) :
    kindOk 3 none lk (kR x) = true := by cases x <;> rfl

section
variable {V : Vertrag D}

theorem kS_kind (hax : D.Ax → False) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (x : Stmt D V l Γ Λ Λ') :
    kindOk 4 none l (kS x) = true := by
  cases x <;> first | rfl | exact (hax ‹_›).elim | (rename_i h; subst h; rfl)

theorem kB_kind (hax : D.Ax → False) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (x : Block D V l Γ Λ Λ') :
    kindOk 5 none l (kB x) = true := by
  cases x <;> first | rfl | exact (hax ‹_›).elim | (rename_i h; subst h; rfl)

theorem kEnd_kind (hax : D.Ax → False) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (x : Endblock D V l Γ Λ) :
    kindOk 6 none l (kEnd x) = true := by
  cases x <;> first | rfl | exact (hax ‹_›).elim | (rename_i h; subst h; rfl)

theorem kArms_kind (hax : D.Ax → False) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (x : Arms D V l Γ Λ Λ' cs) : kindOk 7 none l (kArms x) = true := by cases x <;> rfl

theorem kGArms_kind (hax : D.Ax → False) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (x : GrundArms D V l Γ Λ Λ' n) : kindOk 8 none l (kGArms x) = true := by cases x <;> rfl

end

mutual
theorem fzE_ok (hax : D.Ax → False) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : (e : Expr D Γ Λ τ) → (fzE e).all moeglich = true
  | .lit .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .tru .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .fls .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .var .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .glob .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .slot (i := i) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) all_nil)) (fzE_ok hax i))
  | .thru (p := p) (i := i) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ p rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) all_nil))) (fzE_ok hax p)) (fzE_ok hax i))
  | .ptrOf .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .fnref .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .oldG .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .oldS (i := i) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) all_nil)) (fzE_ok hax i))
  | .widen (e := e) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) all_nil)) (fzE_ok hax e))
  | .add (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .sub (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .neg (a := a) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) all_nil)) (fzE_ok hax a))
  | .mul (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .div (h1' := hb) (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _) (typRegel_teiler b hb _ _ (Or.inl rfl))) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .rem (h1' := hb) (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _) (typRegel_teiler b hb _ _ (Or.inr rfl))) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .sdiv (hb := hb) (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _) (typRegel_steiler b hb _ _ (Or.inl rfl))) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .srem (hb := hb) (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _) (typRegel_steiler b hb _ _ (Or.inr rfl))) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .getBytes (i := i) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) all_nil)) (fzE_ok hax i))
  | .band (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .bor (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .bxor (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .shl (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .shr (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .lt (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .le (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .eq (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .fllt (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .flle (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .and (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .or (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))
  | .not (a := a) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) all_nil)) (fzE_ok hax a))
  | .none .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .some (e := e) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) all_nil)) (fzE_ok hax e))
  | .istSome (e := e) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) all_nil)) (fzE_ok hax e))
  | .case (nutz := nutz) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kN_kind nutz _)) all_nil)) (fzN_ok hax nutz))
  | .why .. => by simp only [fzE]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .forallSlots (body := body) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ body rfl _)) all_nil)) (fzE_ok hax body))
  | .existsSlots (body := body) .. => by simp only [fzE]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ body rfl _)) all_nil)) (fzE_ok hax body))
  | .reaches (a := a) (b := b) .. => by simp only [fzE]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) all_nil))) (fzE_ok hax a)) (fzE_ok hax b))

theorem fzN_ok (hax : D.Ax → False) {Γ : Ctx} {Λ : List (Res D)} {o : Option (Int × Int)} : (e : NutzlastExpr D Γ Λ o) → (fzN e).all moeglich = true
  | .empty .. => by simp only [fzN]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .num (e := e) .. => by simp only [fzN]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) all_nil)) (fzE_ok hax e))

theorem fzA_ok (hax : D.Ax → False) {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} : (e : Args D Γ Λ τs) → (fzA e).all moeglich = true
  | .nil .. => by simp only [fzA]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .cons (e := e) (rest := rest) .. => by simp only [fzA]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind rest _)) all_nil))) (fzE_ok hax e)) (fzA_ok hax rest))

theorem fzR_ok (hax : D.Ax → False) {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} : (e : ErgExpr D Γ Λ o) → (fzR e).all moeglich = true
  | .empty .. => by simp only [fzR]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .val (e := e) .. => by simp only [fzR]; exact (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil)) (fzE_ok hax e))

theorem fzS_ok (hax : D.Ax → False) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : (e : Stmt D V l Γ Λ Λ') → (fzS e).all moeglich = true
  | .assignSlot (i := i) (e := e) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl (kc rfl (kc (kopf_frei e) rfl))) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil))) (fzE_ok hax i)) (fzE_ok hax e))
  | .assignThru (p := p) (i := i) (e := e) .. => by simp only [fzS]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl (kc rfl (kc rfl (kc (kopf_frei e) rfl)))) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ p rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil)))) (fzE_ok hax p)) (fzE_ok hax i)) (fzE_ok hax e))
  | .assignGlob (e := e) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil)) (fzE_ok hax e))
  | .putBytes (i := i) (e := e) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) all_nil))) (fzE_ok hax i)) (fzE_ok hax e))
  | .assignVar (e := e) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil)) (fzE_ok hax e))
  | .shift (i := i) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ i rfl _)) all_nil)) (fzE_ok hax i))
  | .ite (c := c) (t := t) (e := e) .. => by simp only [fzS]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ c rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax t)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax e)) all_nil)))) (fzE_ok hax c)) (fzB_ok hax t)) (fzB_ok hax e))
  | .onOption (o := o) (p := p) (a := a) .. => by simp only [fzS]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ o rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax p)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax a)) all_nil)))) (fzE_ok hax o)) (fzB_ok hax p)) (fzB_ok hax a))
  | .onTag (v := v) (arms := arms) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ v rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kArms_kind hax arms)) all_nil))) (fzE_ok hax v)) (fzArms_ok hax arms))
  | .onWhy (r := r) (arms := arms) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ r rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kGArms_kind hax arms)) all_nil))) (fzE_ok hax r)) (fzGArms_ok hax arms))
  | .call (args := args) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) all_nil)) (fzA_ok hax args))
  | .callInd (p := p) (args := args) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ p rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) all_nil))) (fzE_ok hax p)) (fzA_ok hax args))
  | .locks (body := body) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax body)) all_nil)) (fzB_ok hax body))
  | .breaking (body := body) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax body)) all_nil)) (fzB_ok hax body))
  | .traverse (inv := inv) (body := body) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ inv rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax body)) all_nil))) (fzE_ok hax inv)) (fzB_ok hax body))
  | .retry (bis := bis) (body := body) (ueberlauf := ueberlauf) .. => by simp only [fzS]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ bis rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax body)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax ueberlauf)) all_nil)))) (fzE_ok hax bis)) (fzB_ok hax body)) (fzB_ok hax ueberlauf))
  | .forever (inv := inv) (body := body) .. => by simp only [fzS]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ inv rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax body)) all_nil))) (fzE_ok hax inv)) (fzB_ok hax body))
  | .axiomCall (a := a) .. => (hax a).elim
  | .regWrite (e := e) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil)) (fzE_ok hax e))
  | .transition .. => by simp only [fzS]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .publish (e := e) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) all_nil)) (fzE_ok hax e))
  | .advances .. => by simp only [fzS]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .retires .. => by simp only [fzS]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .ret (e := e) .. => by simp only [fzS]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kR_kind e _)) all_nil)) (fzR_ok hax e))
  | .retWhy .. => by simp only [fzS]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .leave (h := h) .. => by subst h; simp only [fzS]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .next (h := h) .. => by subst h; simp only [fzS]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)

theorem fzB_ok (hax : D.Ax → False) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : (e : Block D V l Γ Λ Λ') → (fzB e).all moeglich = true
  | .nil .. => by simp only [fzB]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .cons (s := s) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kS_kind hax s)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil))) (fzS_ok hax s)) (fzB_ok hax rest))
  | .bind (e := e) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil))) (fzE_ok hax e)) (fzB_ok hax rest))
  | .bindCall (args := args) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil))) (fzA_ok hax args)) (fzB_ok hax rest))
  | .bindCallInd (p := p) (args := args) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ p rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzE_ok hax p)) (fzA_ok hax args)) (fzB_ok hax rest))
  | .bindCallElse (args := args) (err := err) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax err)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzA_ok hax args)) (fzEnd_ok hax err)) (fzB_ok hax rest))
  | .bindAxiom (a := a) .. => (hax a).elim
  | .bindAxiomElse (a := a) .. => (hax a).elim
  | .regRead (rest := rest) .. => by simp only [fzB]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)) (fzB_ok hax rest))
  | .regReadElse (zusage := zusage) (sonst := sonst) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ zusage rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax sonst)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzE_ok hax zusage)) (fzEnd_ok hax sonst)) (fzB_ok hax rest))
  | .awaits (rest := rest) .. => by simp only [fzB]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)) (fzB_ok hax rest))
  | .exchange (neu := neu) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei neu) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ neu (kopfOk_none _) _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil))) (fzE_ok hax neu)) (fzB_ok hax rest))
  | .narrow (e := e) (sonst := sonst) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax sonst)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzE_ok hax e)) (fzEnd_ok hax sonst)) (fzB_ok hax rest))
  | .check (c := c) (sonst := sonst) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ c rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax sonst)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzE_ok hax c)) (fzEnd_ok hax sonst)) (fzB_ok hax rest))
  | .float (a := a) (b := b) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ a rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ b rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzE_ok hax a)) (fzE_ok hax b)) (fzB_ok hax rest))
  | .floatLit (rest := rest) .. => by simp only [fzB]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)) (fzB_ok hax rest))
  | .floatOf (e := e) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil))) (fzE_ok hax e)) (fzB_ok hax rest))
  | .floatNarrow (e := e) (sonst := sonst) (rest := rest) .. => by simp only [fzB]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax sonst)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax rest)) all_nil)))) (fzE_ok hax e)) (fzEnd_ok hax sonst)) (fzB_ok hax rest))

theorem fzEnd_ok (hax : D.Ax → False) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : (e : Endblock D V l Γ Λ) → (fzEnd e).all moeglich = true
  | .ret (e := e) .. => by simp only [fzEnd]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kR_kind e _)) all_nil)) (fzR_ok hax e))
  | .retWhy .. => by simp only [fzEnd]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .leave (h := h) .. => by subst h; simp only [fzEnd]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .next (h := h) .. => by subst h; simp only [fzEnd]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .cons (s := s) (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kS_kind hax s)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil))) (fzS_ok hax s)) (fzEnd_ok hax rest))
  | .bind (e := e) (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl (kc (kopf_frei e) rfl)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ e (kopfOk_none _) _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil))) (fzE_ok hax e)) (fzEnd_ok hax rest))
  | .bindCall (args := args) (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil))) (fzA_ok hax args)) (fzEnd_ok hax rest))
  | .bindCallElse (args := args) (err := err) (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax err)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil)))) (fzA_ok hax args)) (fzEnd_ok hax err)) (fzEnd_ok hax rest))
  | .bindAxiom (a := a) .. => (hax a).elim
  | .bindAxiomElse (a := a) .. => (hax a).elim
  | .regRead (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil)) (fzEnd_ok hax rest))
  | .regReadElse (zusage := zusage) (sonst := sonst) (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ zusage rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax sonst)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil)))) (fzE_ok hax zusage)) (fzEnd_ok hax sonst)) (fzEnd_ok hax rest))
  | .awaits (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil)) (fzEnd_ok hax rest))
  | .bindCallInd (p := p) (args := args) (rest := rest) .. => by simp only [fzEnd]; exact (all_app (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kE_kind _ p rfl _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kA_kind args _)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kEnd_kind hax rest)) all_nil)))) (fzE_ok hax p)) (fzA_ok hax args)) (fzEnd_ok hax rest))

theorem fzArms_ok (hax : D.Ax → False) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : (e : Arms D V l Γ Λ Λ' cs) → (fzArms e).all moeglich = true
  | .nil .. => by simp only [fzArms]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .cons (b := b) (rest := rest) .. => by simp only [fzArms]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax b)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kArms_kind hax rest)) all_nil))) (fzB_ok hax b)) (fzArms_ok hax rest))

theorem fzGArms_ok (hax : D.Ax → False) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} : (e : GrundArms D V l Γ Λ Λ' n) → (fzGArms e).all moeglich = true
  | .nil .. => by simp only [fzGArms]; exact (all_cons (eig_ok rfl rfl rfl rfl) all_nil)
  | .cons (b := b) (rest := rest) .. => by simp only [fzGArms]; exact (all_app (all_app (all_cons (eig_ok rfl rfl rfl rfl) (all_cons (paar_ok rfl rfl rfl rfl rfl (kB_kind hax b)) (all_cons (paar_ok rfl rfl rfl rfl rfl (kGArms_kind hax rest)) all_nil))) (fzB_ok hax b)) (fzGArms_ok hax rest))

end

/-- **Every fine cell of every program of the source is allowed by the typing**, so it is in the universe. -/
theorem feinZellen_moeglich (e : Gen.Einsatz) : e.feinZellen.all moeglich = true := by
  unfold Gen.Einsatz.feinZellen
  refine all_app ?_ ?_
  · refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, _, hf⟩ := List.mem_flatMap.1 hc
    exact List.all_eq_true.1 (all_app (all_app (fzEnd_ok e.keinAx _) (fzE_ok e.keinAx _)) (fzE_ok e.keinAx _)) c hf
  · refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 hc
    exact List.all_eq_true.1 (fzE_ok e.keinAx _) c hi

theorem feinZellen_uF (e : Gen.Einsatz) {c : FZelle} (h : e.HatF c) : c ∈ uF :=
  uF_vollst (List.all_eq_true.1 (feinZellen_moeglich e) c h)

end Gabbro.Grammatik.Gen.Fein
