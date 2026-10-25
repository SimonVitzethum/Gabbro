/- Part 2 of 4 of `MitRuheSemantik` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheSemantik.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The packed answer of a fallible axiom decodes in `D.mitRuhe` as in `D` (C-free lane,
    2026-09-30): the value half through `einpassenErg_ru`, the reason half unchanged. -/
theorem sonstPasst_ru (z : Int → Option D.Fn) (z' : Int → Option D.mitRuhe.Fn)
    (hz : ∀ k, (z' k).bind id = z k) (e : Option Ty) (n : Nat) (roh : Int) :
    sonstPasst (D := D.mitRuhe) z' (e.map tyR) n roh =
      (sonstPasst (D := D) z e n roh).map (Sum.map (ergR e) id) := by
  unfold sonstPasst
  dsimp only
  split
  · rw [einpassenErg_ru z z' hz e]
    cases einpassenErg z e _ <;> rfl
  · split <;> rfl

theorem axiomAntwortSonst_ruG {O : Orakel D} {O' : Orakel D.mitRuhe} (hO : OrakelRu O O')
    (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwortSonst O' a (worldR σ) (envR ρ) =
      (worldR (axiomAntwortSonst O a σ ρ).1,
        (axiomAntwortSonst O a σ ρ).2.map (Sum.map (ergR (D.aerg a)) id)) := by
  unfold axiomAntwortSonst
  rw [worldR_fragt, hO.wirkt]
  exact congrArg _ (sonstPasst_ru O.zeiger O'.zeiger hO.zeiger (D.aerg a) (D.agruende a) _)

theorem axiomAntwortSonst_ru (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwortSonst O.mitRuhe a (worldR σ) (envR ρ) =
      (worldR (axiomAntwortSonst O a σ ρ).1,
        (axiomAntwortSonst O a σ ρ).2.map (Sum.map (ergR (D.aerg a)) id)) :=
  axiomAntwortSonst_ruG (orakelRu_mitRuhe O) a σ ρ

theorem regLies_mitRuhe (O : Orakel D) (r : D.Reg) (σ : World D) :
    O.mitRuhe.regLies r (worldR σ) = O.regLies r σ := by
  show O.regLies r (worldZ (worldR σ)) = _
  rw [worldZ_worldR]

theorem sichtbar_mitRuhe (O : Orakel D) (g : D.Glob) (σ : World D) :
    O.mitRuhe.sichtbar g (worldR σ) = O.sichtbar g σ := by
  show O.sichtbar g (worldZ (worldR σ)) = _
  rw [worldZ_worldR]

theorem rzusage_mitRuhe (r : D.Reg) (v : Wert D (D.rtyp r)) :
    (D.mitRuhe).rzusage r (valR (D.rtyp r) v) = D.rzusage r v := by
  show D.rzusage r (valZ (D.rtyp r) (valR (D.rtyp r) v)) = _
  rw [valZ_valR]



/-! ## 5. Statement helpers -/

section Hilfen

variable (O : Orakel D) (passes : Nat)

theorem execStmt_nachΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (Stmt.nachΛ h s) σ ρ = execStmt O passes R s σ ρ := by
  subst h; rfl

theorem execBlock_vorΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (Block.vorΛ h b) σ ρ = execBlock O passes R b σ ρ := by
  subst h; rfl

theorem execEnd_umΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execEnd O passes R (Endblock.umΛ h e) σ ρ = execEnd O passes R e σ ρ := by
  subst h; rfl

end Hilfen
theorem envR_set : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ),
    (envR ρ).set (varR x) (valR τ v) = envR (ρ.set x v)
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons w ρ, .there x, v => congrArg (Env.cons _) (envR_set ρ x v)

theorem evalErg_ru (σ₀ σ : World D) {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {e : Option Ty} (a : ErgExpr D Γ Λ e) (ρ : Env D Γ),
      evalErg (worldR σ₀) (ruErg a) (worldR σ) (envR ρ) = ergR e (evalErg σ₀ a σ ρ)
  | _, .empty, _ => rfl
  | _, .val e, ρ => eval_ru σ₀ σ e ρ

theorem ergWert_ru {τ : Ty} : ∀ {e : Option Ty} (he : e = some τ)
    (he' : e.map tyR = some (tyR τ)) (v : ErgVal D e),
    ergWert (D := D.mitRuhe) he' (ergR e v) = valR τ (ergWert he v)
  | _, rfl, _, _ => rfl

theorem armEnv_ru {Γ : Ctx} : ∀ {c : Option (Int × Int)} (nutz : Nutzlast c) (ρ : Env D Γ),
    HEq (envR (armEnv nutz ρ)) (armEnv (D := D.mitRuhe) nutz (envR ρ))
  | none, _, _ => HEq.rfl
  | some (_, _), _, _ => HEq.rfl

theorem map_valR_int (lo hi : Int) (l : List (Zahl lo hi)) :
    l.map (valR (D := D) (.int lo hi)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

theorem envR_mpr {a b : Ctx} (h : a = b) (H1 : Env D.mitRuhe (a.map tyR) = Env D.mitRuhe (b.map tyR))
    (H2 : Env D a = Env D b) (ρ : Env D b) : Eq.mpr H1 (envR ρ) = envR (Eq.mpr H2 ρ) := by
  subst h; rfl

theorem umsig_ru {f : D.Fn} {n : Nat} (hf : D.passt f n = true)
    (hf' : (D.mitRuhe).passt (some f) (n + 1) = true) (ρ : Env D (D.sigNr n).params) :
    umsig (D := D.mitRuhe) hf' (envR ρ) = envR (umsig hf ρ) := by
  unfold umsig
  exact envR_mpr (D.passt_sig hf).params _ _ ρ

theorem int_cast_gen (τ : Ty) (lo hi : Int) (h : τ = .int lo hi) (h' : tyR τ = .int lo hi)
    (x : Val D.Fn D.passt τ) :
    @Eq (Zahl lo hi) (h' ▸ valR τ x : Val (Option D.Fn) (passtM D) (.int lo hi))
      (h ▸ x : Val D.Fn D.passt (.int lo hi)) := by
  subst h; rfl

theorem int_cast_gen' (τ : Ty) (lo hi : Int) (h : τ = .int lo hi) (h' : tyR τ = .int lo hi)
    (z : Zahl lo hi) :
    (h' ▸ (z : Val (Option D.Fn) (passtM D) (.int lo hi)) : Val (Option D.Fn) (passtM D) (tyR τ)) =
      valR τ (h ▸ (z : Val D.Fn D.passt (.int lo hi)) : Val D.Fn D.passt τ) := by
  subst h; rfl

theorem slotInt_cast_worldR {lo hi : Int} (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hτ : D.typ t f = .int lo hi) (hτ' : (D.mitRuhe).typ t f = .int lo hi) (k : Int) :
    @Eq (Zahl lo hi) (hτ' ▸ (worldR σ).slots t k f : Wert D.mitRuhe (.int lo hi))
      (hτ ▸ σ.slots t k f : Wert D (.int lo hi)) :=
  int_cast_gen (D.typ t f) lo hi hτ hτ' (σ.slots t k f)

/-! ## 6. Loops -/

section Schleifen

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem traverseLauf_ru {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (schritt' : World D.mitRuhe → Env D.mitRuhe (tyR τ :: Γ.map tyR) →
      Ausgang (vertragR V) true (tyR τ :: Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, schritt' (worldR σ) (envR ρ) = ausR (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ),
      traverseLauf (l := l) schritt' inv' (ks.map (valR τ)) (worldR σ) (envR ρ) =
        ausR (traverseLauf (l := l) schritt inv ks σ ρ)
  | [], σ, ρ => by
      simp only [List.map_nil, traverseLauf, hi]
      by_cases hc : (inv σ ρ).2 = true <;> simp only [hc, if_true, if_false] <;> rfl
  | k :: ks, σ, ρ => by
      simp only [List.map_cons, traverseLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false]
        have e := hs (inv σ ρ).1 (Env.cons k ρ)
        change schritt' (worldR (inv σ ρ).1) (Env.cons (valR τ k) (envR ρ)) = _ at e
        rw [e]
        cases schritt (inv σ ρ).1 (Env.cons k ρ) with
        | ok σ' ρ' =>
            simp only [ausR, envR_tail]
            exact traverseLauf_ru schritt schritt' inv inv' hs hi ks σ' ρ'.tail
        | next h σ' ρ' =>
            simp only [ausR, envR_tail]
            exact traverseLauf_ru schritt schritt' inv inv' hs hi ks σ' ρ'.tail
        | leave h σ' ρ' =>
            simp only [ausR, envR_tail, hi]
            by_cases hc' : (inv σ' ρ'.tail).2 = true <;> simp only [hc', if_true, if_false] <;> rfl
        | zurueck => rfl
        | why => rfl
        | logik => rfl
        | hardware => rfl

theorem retryLauf_ru
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (bis : World D → Env D Γ → World D × Bool)
    (bis' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (ueber : World D → Env D Γ → Ausgang V l Γ)
    (ueber' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) l (Γ.map tyR))
    (hs : ∀ σ ρ, schritt' (worldR σ) (envR ρ) = ausR (schritt σ ρ))
    (hb : ∀ σ ρ, bis' (worldR σ) (envR ρ) = (worldR (bis σ ρ).1, (bis σ ρ).2))
    (hu : ∀ σ ρ, ueber' (worldR σ) (envR ρ) = ausR (ueber σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      retryLauf schritt' bis' ueber' n (worldR σ) (envR ρ) =
        ausR (retryLauf schritt bis ueber n σ ρ)
  | 0, σ, ρ => by
      simp only [retryLauf, hb]
      by_cases hc : (bis σ ρ).2 = true <;> simp only [hc, if_true, if_false, hu] <;> rfl
  | n + 1, σ, ρ => by
      simp only [retryLauf, hb]
      by_cases hc : (bis σ ρ).2 = true
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false, Bool.false_eq_true]
        rw [hs]
        cases schritt (bis σ ρ).1 ρ with
        | ok σ' ρ' => exact retryLauf_ru schritt schritt' bis bis' ueber ueber' hs hb hu n σ' ρ'
        | next h σ' ρ' => exact retryLauf_ru schritt schritt' bis bis' ueber ueber' hs hb hu n σ' ρ'
        | leave h σ' ρ' => rfl
        | zurueck => rfl
        | why => rfl
        | logik => rfl
        | hardware => rfl

theorem foreverLauf_ru (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (schritt' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → Ausgang (vertragR V) true (Γ.map tyR))
    (inv : World D → Env D Γ → World D × Bool)
    (inv' : World D.mitRuhe → Env D.mitRuhe (Γ.map tyR) → World D.mitRuhe × Bool)
    (hs : ∀ σ ρ, schritt' (worldR σ) (envR ρ) = ausR (schritt σ ρ))
    (hi : ∀ σ ρ, inv' (worldR σ) (envR ρ) = (worldR (inv σ ρ).1, (inv σ ρ).2)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      foreverLauf (D := D.mitRuhe) (l := l) a schritt' inv' n (worldR σ) (envR ρ) =
        ausR (foreverLauf (l := l) a schritt inv n σ ρ)
  | 0, _, _ => rfl
  | n + 1, σ, ρ => by
      simp only [foreverLauf, hi]
      by_cases hc : (inv σ ρ).2 = false
      · simp only [hc, if_true]; rfl
      · simp only [hc, if_false]
        rw [hs]
        cases schritt (inv σ ρ).1 ρ with
        | ok σ' ρ' => exact foreverLauf_ru a schritt schritt' inv inv' hs hi n σ' ρ'
        | next h σ' ρ' => exact foreverLauf_ru a schritt schritt' inv inv' hs hi n σ' ρ'
        | leave h σ' ρ' => rfl
        | zurueck => rfl
        | why => rfl
        | logik => rfl
        | hardware => rfl

end Schleifen
/-! ## 7. Every statement, block and end block behaves as translated -/

theorem valR_bool (b : Bool) : valR (D := D) .bool b = b := rfl
theorem valR_int {lo hi : Int} (z : Zahl lo hi) : valR (D := D) (.int lo hi) z = z := rfl
theorem valR_opt {n : Int} (z : Option (Zahl 0 (n - 1))) : valR (D := D) (.opt n) z = z := rfl
theorem valR_fl {lo hi : Int × Int} (z : Gleit lo hi) : valR (D := D) (.fl lo hi) z = z := rfl
theorem valR_fnptr {n : Nat} (f : D.Fn) (h : D.passt f n = true) :
    valR (D := D) (.fnptr n) ⟨f, h⟩ = ⟨some f, h⟩ := rfl

theorem orte2 {Γ : Ctx} {Λ : List (Res D)} {τ₁ τ₂ : Ty} (a : Expr D Γ Λ τ₁) (b : Expr D Γ Λ τ₂) :
    (ruE a).orte ++ (ruE b).orte = a.orte ++ b.orte := kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)


end Gabbro.Grammatik
