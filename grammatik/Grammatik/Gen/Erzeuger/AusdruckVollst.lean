/-
  File:      Grammatik/Gen/Erzeuger/AusdruckVollst.lean
  Subject:   The generator of expressions by fuel, and its COMPLETENESS: every typed expression of size at most
             `m` is generated (`genExpr_vollst`). The proof cases on the term; a constructor without a clause
             stops the build.
-/
import Grammatik.Gen.Erzeuger.Ausdruck

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- The expressions of fuel `m + 1` from the expressions `es` of fuel `m` (`rek`: the same at other contexts). -/
def genExprS [Aufz D] (m : Nat) (es : List (SE D Γ Λ)) (rek : ∀ Γ' : Ctx, List (SE D Γ' Λ)) :
    List (SE D Γ Λ) :=
  gLit m ++ gBool ++ gVar Γ Λ ++ gGlob ++ gSlot es ++ gThru es ++ gPtrOf m ++ gFnref ++ gOldG ++ gOldS es ++
  gWiden m es ++ gAdd es ++ gSub es ++ gNeg es ++ gMul es ++ gDiv es ++ gRem es ++ gSdiv es ++ gSrem es ++
  gGetBytes m es ++ gBand es ++ gBor m es ++ gBxor m es ++ gShl m es ++ gShr m es ++ gLt es ++ gLe es ++ gEq es ++
  gFllt es ++ gFlle es ++ gAnd es ++ gOr es ++ gNot es ++ gNone m ++ gSome m es ++ gIstSome es ++ gCase m es ++
  gWhy m ++ gForall rek ++ gExists rek ++ gReaches es

/-- **The generator of expressions**: all typed expressions of size at most `m`, by fuel. -/
def genExpr [Aufz D] : Nat → (Γ : Ctx) → (Λ : List (Res D)) → List (SE D Γ Λ)
  | 0, _, _ => []
  | m + 1, Γ, Λ => genExprS m (genExpr m Γ Λ) (fun Γ' => genExpr m Γ' Λ)

/-- Close `x ∈ genExprS ...` from `hc : x ∈ clause`. -/
macro "gen_fin " h:ident : tactic =>
  `(tactic| (unfold genExprS; simp only [List.mem_append]; simp only [$h:ident, or_true, true_or]))

theorem mem_dif {P : Prop} [Decidable P] {α : Type} {g : P → α} (h : P) :
    g h ∈ (if h' : P then [g h'] else []) := by
  rw [dif_pos h]; simp

set_option maxHeartbeats 4000000 in
/-- **Completeness of the generator of expressions**: a typed expression of size at most `m` is generated. -/
theorem genExpr_vollst [Aufz D] : ∀ (m : Nat) (Γ : Ctx) (Λ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ τ),
    groesseExpr e ≤ m → (⟨τ, e⟩ : SE D Γ Λ) ∈ genExpr m Γ Λ := by
  intro m
  induction m with
  | zero =>
    intro Γ Λ τ e h
    cases e <;> (simp only [groesseExpr] at h; omega)
  | succ m ih =>
    intro Γ Λ τ e h
    simp only [genExpr]
    cases e with
    | lit n =>
      have hc : (⟨.int n n, .lit n⟩ : SE D Γ Λ) ∈ gLit m :=
        List.mem_map.2 ⟨n, mem_ints (by simp only [groesseExpr] at h; omega), rfl⟩
      gen_fin hc
    | tru =>
      have hc : (⟨.bool, .tru⟩ : SE D Γ Λ) ∈ gBool := by simp [gBool]
      gen_fin hc
    | fls =>
      have hc : (⟨.bool, .fls⟩ : SE D Γ Λ) ∈ gBool := by simp [gBool]
      gen_fin hc
    | var x =>
      have hc : (⟨_, .var x⟩ : SE D Γ Λ) ∈ gVar Γ Λ := List.mem_map.2 ⟨⟨_, x⟩, genVar_vollst _ _ x, rfl⟩
      gen_fin hc
    | glob g hL =>
      have hc : (⟨_, .glob g hL⟩ : SE D Γ Λ) ∈ gGlob :=
        List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, mem_dif hL⟩
      gen_fin hc
    | slot t f i hL =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .slot t f i hL⟩ : SE D Γ Λ) ∈ gSlot (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f,
          List.mem_flatMap.2 ⟨i, mem_ofTy (ih _ _ _ i (by omega)), mem_dif hL⟩⟩⟩
      gen_fin hc
    | thru p t ht f i hL =>
      simp only [groesseExpr] at h
      have hp := ih _ _ _ p (by omega)
      have hc : (⟨_, .thru p t ht f i hL⟩ : SE D Γ Λ) ∈ gThru (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨_, hp, List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, by
          rw [dif_pos ht]
          exact List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f,
            List.mem_flatMap.2 ⟨i, mem_ofTy (ih _ _ _ i (by omega)), mem_dif hL⟩⟩⟩⟩
      gen_fin hc
    | ptrOf t n ht rw =>
      have hc : (⟨_, .ptrOf t n ht rw⟩ : SE D Γ Λ) ∈ gPtrOf m :=
        List.mem_flatMap.2 ⟨n, List.mem_range.2 (by simp only [groesseExpr] at h; omega),
          List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, by
            rw [dif_pos ht]
            exact List.mem_map.2 ⟨rw, by cases rw <;> simp, rfl⟩⟩⟩
      gen_fin hc
    | fnref f n hn =>
      subst hn
      have hc : (⟨_, .fnref f (D.sig f) rfl⟩ : SE D Γ Λ) ∈ gFnref :=
        List.mem_map.2 ⟨f, Aufz.fn_mem f, rfl⟩
      gen_fin hc
    | oldG g hL =>
      have hc : (⟨_, .oldG g hL⟩ : SE D Γ Λ) ∈ gOldG :=
        List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, mem_dif hL⟩
      gen_fin hc
    | oldS t f i hL =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .oldS t f i hL⟩ : SE D Γ Λ) ∈ gOldS (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f,
          List.mem_flatMap.2 ⟨i, mem_ofTy (ih _ _ _ i (by omega)), mem_dif hL⟩⟩⟩
      gen_fin hc
    | @widen lo' lo hi hi' _ _ h1 h2 e =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .widen h1 h2 e⟩ : SE D Γ Λ) ∈ gWiden m (genExpr m Γ Λ) :=
        mem_mitInt (ih _ _ _ e (by omega)) (List.mem_flatMap.2 ⟨lo', mem_ints (by omega),
          List.mem_flatMap.2 ⟨hi', mem_ints (by omega), by
            rw [dif_pos h1, dif_pos h2]; simp⟩⟩)
      gen_fin hc
    | add a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .add a b⟩ : SE D Γ Λ) ∈ gAdd (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | sub a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .sub a b⟩ : SE D Γ Λ) ∈ gSub (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | neg a =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .neg a⟩ : SE D Γ Λ) ∈ gNeg (genExpr m Γ Λ) :=
        mem_mitInt (ih _ _ _ a (by omega)) (by simp)
      gen_fin hc
    | mul a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .mul a b⟩ : SE D Γ Λ) ∈ gMul (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | div p0 p1 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .div p0 p1 a b⟩ : SE D Γ Λ) ∈ gDiv (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by rw [dif_pos p0, dif_pos p1]; simp)
      gen_fin hc
    | rem p0 p1 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .rem p0 p1 a b⟩ : SE D Γ Λ) ∈ gRem (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by rw [dif_pos p0, dif_pos p1]; simp)
      gen_fin hc
    | sdiv hb a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .sdiv hb a b⟩ : SE D Γ Λ) ∈ gSdiv (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by rw [dif_pos hb]; simp)
      gen_fin hc
    | srem hb a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .srem hb a b⟩ : SE D Γ Λ) ∈ gSrem (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by rw [dif_pos hb]; simp)
      gen_fin hc
    | getBytes t f hf n i hlo hhi hL =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .getBytes t f hf n i hlo hhi hL⟩ : SE D Γ Λ) ∈ gGetBytes m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f, by
          rw [dif_pos hf]
          exact List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega),
            mem_mitInt (ih _ _ _ i (by omega)) (by rw [dif_pos hlo, dif_pos hhi, dif_pos hL]; simp)⟩⟩⟩
      gen_fin hc
    | band p0 p1 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .band p0 p1 a b⟩ : SE D Γ Λ) ∈ gBand (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by rw [dif_pos p0, dif_pos p1]; simp)
      gen_fin hc
    | bor w p0 p1 q1 q2 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .bor w p0 p1 q1 q2 a b⟩ : SE D Γ Λ) ∈ gBor m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨w, List.mem_range.2 (by omega),
          mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega))
            (by rw [dif_pos p0, dif_pos p1, dif_pos q1, dif_pos q2]; simp)⟩
      gen_fin hc
    | bxor w p0 p1 q1 q2 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .bxor w p0 p1 q1 q2 a b⟩ : SE D Γ Λ) ∈ gBxor m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨w, List.mem_range.2 (by omega),
          mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega))
            (by rw [dif_pos p0, dif_pos p1, dif_pos q1, dif_pos q2]; simp)⟩
      gen_fin hc
    | shl w q1 q2 p0 p1 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .shl w q1 q2 p0 p1 a b⟩ : SE D Γ Λ) ∈ gShl m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨w, List.mem_range.2 (by omega),
          mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega))
            (by rw [dif_pos q1, dif_pos q2, dif_pos p0, dif_pos p1]; simp)⟩
      gen_fin hc
    | shr w q1 q2 p0 p1 a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .shr w q1 q2 p0 p1 a b⟩ : SE D Γ Λ) ∈ gShr m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨w, List.mem_range.2 (by omega),
          mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega))
            (by rw [dif_pos q1, dif_pos q2, dif_pos p0, dif_pos p1]; simp)⟩
      gen_fin hc
    | lt a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .lt a b⟩ : SE D Γ Λ) ∈ gLt (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | le a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .le a b⟩ : SE D Γ Λ) ∈ gLe (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | eq a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .eq a b⟩ : SE D Γ Λ) ∈ gEq (genExpr m Γ Λ) :=
        mem_mitInt2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | fllt a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .fllt a b⟩ : SE D Γ Λ) ∈ gFllt (genExpr m Γ Λ) :=
        mem_mitFl2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | flle a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .flle a b⟩ : SE D Γ Λ) ∈ gFlle (genExpr m Γ Λ) :=
        mem_mitFl2 (ih _ _ _ a (by omega)) (ih _ _ _ b (by omega)) (by simp)
      gen_fin hc
    | and a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .and a b⟩ : SE D Γ Λ) ∈ gAnd (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨a, mem_ofTy (ih _ _ _ a (by omega)),
          List.mem_map.2 ⟨b, mem_ofTy (ih _ _ _ b (by omega)), rfl⟩⟩
      gen_fin hc
    | or a b =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .or a b⟩ : SE D Γ Λ) ∈ gOr (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨a, mem_ofTy (ih _ _ _ a (by omega)),
          List.mem_map.2 ⟨b, mem_ofTy (ih _ _ _ b (by omega)), rfl⟩⟩
      gen_fin hc
    | not a =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .not a⟩ : SE D Γ Λ) ∈ gNot (genExpr m Γ Λ) :=
        List.mem_map.2 ⟨a, mem_ofTy (ih _ _ _ a (by omega)), rfl⟩
      gen_fin hc
    | none n =>
      have hc : (⟨_, .none n⟩ : SE D Γ Λ) ∈ gNone m :=
        List.mem_map.2 ⟨n, mem_ints (by simp only [groesseExpr] at h; omega), rfl⟩
      gen_fin hc
    | @some _ _ n e =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .some e⟩ : SE D Γ Λ) ∈ gSome m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨n, mem_ints (by omega),
          List.mem_map.2 ⟨e, mem_ofTy (ih _ _ _ e (by omega)), rfl⟩⟩
      gen_fin hc
    | istSome e =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .istSome e⟩ : SE D Γ Λ) ∈ gIstSome (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨_, ih _ _ _ e (by omega), by simp⟩
      gen_fin hc
    | case cs i nutz =>
      simp only [groesseExpr] at h
      have hl := length_le_groesseFaelle cs
      have hb : ∀ c ∈ cs, ∀ lo hi, c = some (lo, hi) → lo.natAbs ≤ m ∧ hi.natAbs ≤ m := by
        intro c hc lo hi hch
        subst hch
        have := mem_groesseFaelle hc
        omega
      have hc : (⟨_, .case cs i nutz⟩ : SE D Γ Λ) ∈ gCase m (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨cs, mem_listenBis m m cs (by omega) hb,
          List.mem_flatMap.2 ⟨i, List.mem_finRange i,
            List.mem_map.2 ⟨nutz, mem_nutzAt (fun τ e he => ih _ _ τ e he) _ nutz (by omega), rfl⟩⟩⟩
      gen_fin hc
    | why n r =>
      have hc : (⟨_, .why n r⟩ : SE D Γ Λ) ∈ gWhy m :=
        List.mem_flatMap.2 ⟨n, List.mem_range.2 (by simp only [groesseExpr] at h; omega),
          List.mem_map.2 ⟨r, List.mem_finRange r, rfl⟩⟩
      gen_fin hc
    | forallSlots t body hL =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .forallSlots t body hL⟩ : SE D Γ Λ) ∈ gForall (fun Γ' => genExpr m Γ' Λ) :=
        List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨body,
          mem_ofTy (ih _ _ _ body (by omega)), mem_dif hL⟩⟩
      gen_fin hc
    | existsSlots t body hL =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .existsSlots t body hL⟩ : SE D Γ Λ) ∈ gExists (fun Γ' => genExpr m Γ' Λ) :=
        List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨body,
          mem_ofTy (ih _ _ _ body (by omega)), mem_dif hL⟩⟩
      gen_fin hc
    | reaches t f hf a b hL =>
      simp only [groesseExpr] at h
      have hc : (⟨_, .reaches t f hf a b hL⟩ : SE D Γ Λ) ∈ gReaches (genExpr m Γ Λ) :=
        List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f, by
          rw [dif_pos hf]
          exact List.mem_flatMap.2 ⟨a, mem_ofTy (ih _ _ _ a (by omega)),
            List.mem_flatMap.2 ⟨b, mem_ofTy (ih _ _ _ b (by omega)), mem_dif hL⟩⟩⟩⟩
      gen_fin hc

end Gabbro.Grammatik.Gen
