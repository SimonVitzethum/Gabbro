/-
  File:      Grammatik/Gen/Erzeuger/AusdruckVollst.lean
  Subject:   The COMPLETENESS of the expression clauses (`exprS_vollst`: an expression of size `k` is among the
             items of size `k`, given the expressions of the sizes below), the TABLE of the expressions of one
             context by size (`genE`), and its completeness (`genE_vollst`): every typed expression of size at
             most `n` is in the bucket of its size. The proof cases on the term; a constructor without a clause
             stops the build, so new syntax shows up as a gap by itself.
-/
import Grammatik.Gen.Erzeuger.Ausdruck

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {Γ : Ctx} {Λ : List (Res D)}

/-- Every expression of size below `k` is in the stream, in the bucket of its size. -/
def Unter (E : Sz (SE D Γ Λ)) (k : Nat) : Prop :=
  ∀ (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e < k → (⟨τ, e⟩ : SE D Γ Λ) ∈ E (groesseExpr e)

/-- The oracle of the quantifier bodies holds every expression of size below `k`, at every context, for every
    bound that reaches its size. -/
def QUnter (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) (k : Nat) : Prop :=
  ∀ (n : Nat) (Γ' : Ctx) (τ : Ty) (e : Expr D Γ' Λ τ), groesseExpr e < k → groesseExpr e ≤ n →
    (⟨τ, e⟩ : SE D Γ' Λ) ∈ Q Γ' n (groesseExpr e)

theorem mem_dif {P : Prop} [Decidable P] {α : Type} {g : P → α} (h : P) :
    g h ∈ (if h' : P then [g h'] else []) := by
  rw [dif_pos h]; simp

theorem groesseExpr_pos {τ : Ty} (e : Expr D Γ Λ τ) : 1 ≤ groesseExpr e := by
  cases e <;> simp only [groesseExpr] <;> omega

theorem mem_nutzS {E : Sz (SE D Γ Λ)} {K : Nat} (hE : Unter E K) {o : Option (Int × Int)}
    (x : NutzlastExpr D Γ Λ o) (hx : groesseNutz x ≤ K) : x ∈ nutzS E o (groesseNutz x) := by
  cases x with
  | empty => exact Sz.mem_blatt (by simp)
  | num e =>
    simp only [groesseNutz] at hx ⊢
    have he := hE _ e (by omega)
    have hm : NutzlastExpr.num e ∈ nutzS E (some (_, _)) (groesseExpr e + 1) :=
      Sz.mem_knoten (Sz.mem_map (f := NutzlastExpr.num) (mem_tyS he))
    exact Sz.mem_cast hm (by omega)

/-- Close `x ∈ exprS ...` from `hc : x ∈ clause k`. -/
macro "ausd " c:term ", " h:term : tactic =>
  `(tactic| exact Sz.mem_alle (c := $c) (by simp) $h)

set_option maxHeartbeats 4000000 in
/-- **Completeness of the expression clauses.** -/
theorem exprS_vollst (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) (E : Sz (SE D Γ Λ)) {τ : Ty} (e : Expr D Γ Λ τ)
    (hu : groesseExpr e < unendlich) (hE : Unter E (groesseExpr e)) (hQ : QUnter Q (groesseExpr e)) :
    (⟨τ, e⟩ : SE D Γ Λ) ∈ exprS Q E (groesseExpr e) := by
  cases e with
  | lit n =>
    simp only [groesseExpr] at hu ⊢
    ausd (gLit (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_zW (n := n) rfl (by omega)) (Sz.mem_pure _))) (by omega)
  | tru =>
    simp only [groesseExpr]
    ausd (gBool (D := D) (Γ := Γ) (Λ := Λ)), Sz.mem_blatt (by simp)
  | fls =>
    simp only [groesseExpr]
    ausd (gBool (D := D) (Γ := Γ) (Λ := Λ)), Sz.mem_blatt (by simp)
  | var x =>
    simp only [groesseExpr] at hu ⊢
    ausd (gVar (D := D) (Λ := Λ) Γ),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_varS x) (Sz.mem_pure _))) (by omega)
  | glob g hL =>
    simp only [groesseExpr]
    ausd (gGlob (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_blatt (List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, mem_dif hL⟩)
  | slot t f i hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hi := hE _ i (by omega)
    ausd (gSlot E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t))
        (Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f))
          (Sz.mem_bind (mem_tyS hi) (Sz.mem_wenn hL (Sz.mem_pure _)))))) (by omega)
  | thru p t ht f i hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hp := hE _ p (by omega)
    have hi := hE _ i (by omega)
    ausd (gThru E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_ptrS hp) (Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t))
        (Sz.mem_wenn ht (Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f))
          (Sz.mem_bind (mem_tyS hi) (Sz.mem_wenn hL (Sz.mem_pure _)))))))) (by omega)
  | ptrOf t n ht rw =>
    simp only [groesseExpr] at hu hE hQ ⊢
    ausd (gPtrOf (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_nS (n := n) rfl (by omega))
        (Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t)) (Sz.mem_wenn ht (Sz.mem_bind
          (Sz.mem_wahl (by cases rw <;> simp)) (Sz.mem_pure _)))))) (by omega)
  | fnref f n hn =>
    subst hn
    simp only [groesseExpr]
    ausd (gFnref (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_blatt (List.mem_map.2 ⟨f, Aufz.fn_mem f, rfl⟩)
  | oldG g hL =>
    simp only [groesseExpr]
    ausd (gOldG (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_blatt (List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, mem_dif hL⟩)
  | oldS t f i hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hi := hE _ i (by omega)
    ausd (gOldS E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t))
        (Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f))
          (Sz.mem_bind (mem_tyS hi) (Sz.mem_wenn hL (Sz.mem_pure _)))))) (by omega)
  | @widen lo' lo hi hi' _ _ h1 h2 e =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have he := hE _ e (by omega)
    ausd (gWiden E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS he) (Sz.mem_bind (mem_zS (n := lo') rfl (by omega))
        (Sz.mem_bind (mem_zS (n := hi') rfl (by omega)) (Sz.mem_wenn h1 (Sz.mem_wenn h2 (Sz.mem_pure _))))))) (by omega)
  | add a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gAdd E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb) (Sz.mem_pure _)))) (by omega)
  | sub a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gSub E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb) (Sz.mem_pure _)))) (by omega)
  | neg a =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    ausd (gNeg E), Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_pure _))) (by omega)
  | mul a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gMul E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb) (Sz.mem_pure _)))) (by omega)
  | div p0 p1 a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gDiv E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb)
        (Sz.mem_wenn p0 (Sz.mem_wenn p1 (Sz.mem_pure _)))))) (by omega)
  | rem p0 p1 a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gRem E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb)
        (Sz.mem_wenn p0 (Sz.mem_wenn p1 (Sz.mem_pure _)))))) (by omega)
  | sdiv hb' a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gSdiv E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb)
        (Sz.mem_wenn hb' (Sz.mem_pure _))))) (by omega)
  | srem hb' a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gSrem E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb)
        (Sz.mem_wenn hb' (Sz.mem_pure _))))) (by omega)
  | getBytes t f hf n i hlo hhi hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hi := hE _ i (by omega)
    ausd (gGetBytes E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t))
        (Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) (Sz.mem_wenn hf
          (Sz.mem_bind (mem_nS (n := n) rfl (by omega)) (Sz.mem_bind (mem_intS hi)
            (Sz.mem_wenn hlo (Sz.mem_wenn hhi (Sz.mem_wenn hL (Sz.mem_pure _)))))))))) (by omega)
  | band h0 h0' a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gBand E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb)
        (Sz.mem_wenn h0 (Sz.mem_wenn h0' (Sz.mem_pure _)))))) (by omega)
  | bor w h0 h0' hw1 hw2 a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gBor E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_nS (n := w) rfl (by omega)) (Sz.mem_bind (mem_intS ha)
        (Sz.mem_bind (mem_intS hb) (Sz.mem_wenn h0 (Sz.mem_wenn h0' (Sz.mem_wenn hw1
          (Sz.mem_wenn hw2 (Sz.mem_pure _))))))))) (by omega)
  | bxor w h0 h0' hw1 hw2 a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gBxor E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_nS (n := w) rfl (by omega)) (Sz.mem_bind (mem_intS ha)
        (Sz.mem_bind (mem_intS hb) (Sz.mem_wenn h0 (Sz.mem_wenn h0' (Sz.mem_wenn hw1
          (Sz.mem_wenn hw2 (Sz.mem_pure _))))))))) (by omega)
  | shl w hw1 hw2 h0 h0' a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gShl E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_nS (n := w) rfl (by omega)) (Sz.mem_bind (mem_intS ha)
        (Sz.mem_bind (mem_intS hb) (Sz.mem_wenn hw1 (Sz.mem_wenn hw2 (Sz.mem_wenn h0
          (Sz.mem_wenn h0' (Sz.mem_pure _))))))))) (by omega)
  | shr w hw1 hw2 h0 h0' a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gShr E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_nS (n := w) rfl (by omega)) (Sz.mem_bind (mem_intS ha)
        (Sz.mem_bind (mem_intS hb) (Sz.mem_wenn hw1 (Sz.mem_wenn hw2 (Sz.mem_wenn h0
          (Sz.mem_wenn h0' (Sz.mem_pure _))))))))) (by omega)
  | lt a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gLt E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb) (Sz.mem_pure _)))) (by omega)
  | le a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gLe E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb) (Sz.mem_pure _)))) (by omega)
  | eq a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gEq E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_intS ha) (Sz.mem_bind (mem_intS hb) (Sz.mem_pure _)))) (by omega)
  | fllt a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gFllt E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_flS ha) (Sz.mem_bind (mem_flS hb) (Sz.mem_pure _)))) (by omega)
  | flle a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gFlle E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_flS ha) (Sz.mem_bind (mem_flS hb) (Sz.mem_pure _)))) (by omega)
  | and a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gAnd E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_tyS ha) (Sz.mem_bind (mem_tyS hb) (Sz.mem_pure _)))) (by omega)
  | or a b =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gOr E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_tyS ha) (Sz.mem_bind (mem_tyS hb) (Sz.mem_pure _)))) (by omega)
  | not a =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    ausd (gNot E), Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_tyS ha) (Sz.mem_pure _))) (by omega)
  | none n =>
    simp only [groesseExpr] at hu hE hQ ⊢
    ausd (gNone (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_zS (n := n) rfl (by omega)) (Sz.mem_pure _))) (by omega)
  | @some _ _ n e =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have he := hE _ e (by omega)
    ausd (gSome E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_zS (n := n) rfl (by omega))
        (Sz.mem_bind (mem_tyS he) (Sz.mem_pure _)))) (by omega)
  | istSome e =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have he := hE _ e (by omega)
    ausd (gIstSome E), Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_optS he) (Sz.mem_pure _))) (by omega)
  | case cs i nutz =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hm := mem_sfS (cs := cs) (by omega)
    have h0 := kostS_null hm
    have hf : cs ∈ sfS 0 := Sz.mem_wahl hm
    ausd (gCase E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind hf (Sz.mem_bind (Sz.mem_wahl (List.mem_finRange i))
        (Sz.mem_bind (mem_nutzS hE nutz (by omega)) (Sz.mem_pure _))))) (by omega)
  | why n r =>
    simp only [groesseExpr] at hu hE hQ ⊢
    ausd (gWhy (D := D) (Γ := Γ) (Λ := Λ)),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (mem_nS (n := n) rfl (by omega))
        (Sz.mem_bind (Sz.mem_wahl (List.mem_finRange r)) (Sz.mem_pure _)))) (by omega)
  | forallSlots t body hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hb := hQ (groesseExpr body) _ _ body (by omega) (Nat.le_refl _)
    have hc : (⟨.bool, .forallSlots t body hL⟩ : SE D Γ Λ) ∈ gForall Q (groesseExpr body + 1) :=
      List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨body, mem_tyS hb, mem_dif hL⟩⟩
    ausd (gForall Q), Sz.mem_cast hc (by omega)
  | existsSlots t body hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have hb := hQ (groesseExpr body) _ _ body (by omega) (Nat.le_refl _)
    have hc : (⟨.bool, .existsSlots t body hL⟩ : SE D Γ Λ) ∈ gExists Q (groesseExpr body + 1) :=
      List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨body, mem_tyS hb, mem_dif hL⟩⟩
    ausd (gExists Q), Sz.mem_cast hc (by omega)
  | reaches t f hf a b hL =>
    simp only [groesseExpr] at hu hE hQ ⊢
    have ha := hE _ a (by omega)
    have hb := hE _ b (by omega)
    ausd (gReaches E),
      Sz.mem_cast (Sz.mem_knoten (Sz.mem_bind (Sz.mem_wahl (Aufz.tab_mem t))
        (Sz.mem_bind (Sz.mem_wahl (Aufz.feld_mem t f)) (Sz.mem_wenn hf (Sz.mem_bind (mem_tyS ha)
          (Sz.mem_bind (mem_tyS hb) (Sz.mem_wenn hL (Sz.mem_pure _)))))))) (by omega)

/-! ## The table by size -/

/-- The buckets `0 .. n` of a step function: bucket `0` is `leer`, bucket `k + 1` is the step on the buckets below. -/
def buckets {β : Type} (leer : β) (step : List β → Nat → β) : Nat → List β
  | 0 => [leer]
  | n + 1 => (buckets leer step n) ++ [step (buckets leer step n) (n + 1)]

/-- A table of buckets as a stream. -/
def tab {α : Type} (t : List (List α)) : Sz α := fun i => t.getD i []

theorem length_buckets {β : Type} (leer : β) (step : List β → Nat → β) :
    ∀ n, (buckets leer step n).length = n + 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [buckets, ih]

theorem getD_buckets_alt {β : Type} (leer : β) (step : List β → Nat → β) {n i : Nat} (d : β) (h : i ≤ n) :
    (buckets leer step (n + 1)).getD i d = (buckets leer step n).getD i d := by
  simp only [buckets]
  have hl : i < (buckets leer step n).length := by rw [length_buckets]; omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]

theorem getD_buckets_neu {β : Type} (leer : β) (step : List β → Nat → β) (n : Nat) (d : β) :
    (buckets leer step (n + 1)).getD (n + 1) d = step (buckets leer step n) (n + 1) := by
  simp only [buckets]
  have hl := length_buckets leer step n
  have : n + 1 = (buckets leer step n).length := by omega
  rw [this]
  simp [List.getD_eq_getElem?_getD]

/-- **The expressions of one context by size**: the buckets `0 .. n`; the bodies of a quantifier are drawn from
    the table of the extended context, by fuel `f` (a nesting costs at least one, so `f ≥ size` suffices). -/
def genE : Nat → Nat → (Γ : Ctx) → (Λ : List (Res D)) → List (List (SE D Γ Λ))
  | 0, n, _, _ => List.replicate (n + 1) []
  | f + 1, n, Γ, Λ => buckets [] (fun prev k => exprS (fun Γ' j => tab (genE f j Γ' Λ)) (tab prev) k) n

/-- **Completeness of the expression table**: every typed expression of size at most `n` (and at most the fuel) is
    in the bucket of its size. -/
theorem genE_vollst : ∀ (f n : Nat) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ),
    groesseExpr e ≤ n → groesseExpr e ≤ f → groesseExpr e < unendlich →
    (⟨τ, e⟩ : SE D Γ Λ) ∈ tab (genE f n Γ Λ) (groesseExpr e) := by
  intro f
  induction f with
  | zero =>
    intro n Γ Λ τ e _ hf _
    have := groesseExpr_pos e
    omega
  | succ f ih =>
    intro n Γ Λ τ e hn hf hu
    induction n generalizing τ e with
    | zero =>
      have := groesseExpr_pos e
      omega
    | succ n ihn =>
      show _ ∈ tab (buckets [] (fun prev k => exprS (fun Γ' j => tab (genE f j Γ' Λ)) (tab prev) k) (n + 1)) _
      by_cases hlt : groesseExpr e ≤ n
      · unfold tab
        rw [getD_buckets_alt _ _ _ hlt]
        exact ihn τ e hlt hf hu
      · have heq : groesseExpr e = n + 1 := by omega
        unfold tab
        rw [heq, getD_buckets_neu]
        have hE : Unter (Γ := Γ) (tab (buckets [] (fun prev k => exprS (fun Γ' j => tab (genE f j Γ' Λ)) (tab prev) k) n))
            (groesseExpr e) := by
          intro τ' e' hlt'
          exact ihn τ' e' (by omega) (by omega) (by omega)
        have hQ : QUnter (fun Γ' j => tab (genE f j Γ' Λ)) (groesseExpr e) := by
          intro j Γ' τ' e' hlt' hj
          exact ih j Γ' Λ τ' e' hj (by omega) (by omega)
        have := exprS_vollst (fun Γ' j => tab (genE f j Γ' Λ))
          (tab (buckets [] (fun prev k => exprS (fun Γ' j => tab (genE f j Γ' Λ)) (tab prev) k) n)) e hu hE hQ
        rw [heq] at this
        exact this

end Gabbro.Grammatik.Gen
