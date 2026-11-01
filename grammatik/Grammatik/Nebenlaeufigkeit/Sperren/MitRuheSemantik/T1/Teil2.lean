module

public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheStatisch
public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem wirkt_mitRuhe (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    O.mitRuhe.wirkt a (worldR σ) (envR ρ) = (worldR (O.wirkt a σ ρ).1, (O.wirkt a σ ρ).2) := by
  show (worldR (O.wirkt a (worldZ (worldR σ)) (envZ (envR ρ))).1,
    (O.wirkt a (worldZ (worldR σ)) (envZ (envR ρ))).2) = _
  rw [worldZ_worldR, envZ_envR]

/-- **An oracle of `D.mitRuhe` answering like `O`** on translated worlds and arguments. Until
    2026-09-15 the only such oracle the transfer used was `O.mitRuhe` itself, and every oracle
    of `D.mitRuhe` was one (`zurueck_mitRuhe`). Since the loaded image joined the oracle (G1
    repair, `Orakel.zeiger`), an oracle of `D.mitRuhe` may place the runtime's root at an
    address, which no oracle of `D` can: `O.mitRuhe` is then not `O'`, but it still ANSWERS
    like `O'` on every translated type -- the root has signature number `0`, which no
    translated `fnptr` type names (`einpassen_ru`). -/
structure OrakelRu (O : Orakel D) (O' : Orakel D.mitRuhe) : Prop where
  wirkt : ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)),
    O'.wirkt a (worldR σ) (envR ρ) = (worldR (O.wirkt a σ ρ).1, (O.wirkt a σ ρ).2)
  regLies : ∀ (r : D.Reg) (σ : World D), O'.regLies r (worldR σ) = O.regLies r σ
  sichtbar : ∀ (g : D.Glob) (σ : World D), O'.sichtbar g (worldR σ) = O.sichtbar g σ
  zeiger : ∀ k, (O'.zeiger k).bind id = O.zeiger k

/-- A raw answer decodes in `D.mitRuhe` as in `D`, under images that agree off the root. -/
theorem einpassen_ru (z : Int → Option D.Fn) (z' : Int → Option D.mitRuhe.Fn)
    (hz : ∀ k, (z' k).bind id = z k) : ∀ (τ : Ty) (n : Int),
    einpassen (D := D.mitRuhe) z' (tyR τ) n = (einpassen (D := D) z τ n).map (valR τ)
  | .int lo hi, n => by
      show einpassen (D := D.mitRuhe) z' (.int lo hi) n =
        Option.map (valR (.int lo hi)) (einpassen (D := D) z (.int lo hi) n)
      simp only [einpassen]
      split <;> rfl
  | .bool, _ => rfl
  | .opt m, n => by
      show einpassen (D := D.mitRuhe) z' (.opt m) n =
        Option.map (valR (.opt m)) (einpassen (D := D) z (.opt m) n)
      simp only [einpassen]
      split
      · rfl
      · split <;> rfl
  | .sum cs, n => by
      show summePasst cs n = Option.map (valR (D := D) (.sum cs)) (summePasst cs n)
      cases summePasst cs n <;> rfl
  | .why m, n => by
      show einpassen (D := D.mitRuhe) z' (.why m) n =
        Option.map (valR (.why m)) (einpassen (D := D) z (.why m) n)
      simp only [einpassen]
      split <;> rfl
  | .ref m, n => by
      show einpassen (D := D.mitRuhe) z' (.ref m) n =
        Option.map (valR (.ref m)) (einpassen (D := D) z (.ref m) n)
      simp only [einpassen]
      split <;> rfl
  | .never, _ => rfl
  | .fl lo hi, n => by
      show gleitWortPasst lo hi n = Option.map (valR (D := D) (.fl lo hi)) (gleitWortPasst lo hi n)
      cases gleitWortPasst lo hi n <;> rfl
  | .fnptr m, n => by
      show zeigerPasst (D := D.mitRuhe) z' (m + 1) n =
        Option.map (valR (D := D) (.fnptr m)) (zeigerPasst z m n)
      have h := hz n
      cases hz' : z' n with
      | none =>
          have hzn : z n = Option.none := by rw [← h, hz']; rfl
          simp only [zeigerPasst, hz', hzn]
          try rfl
      | some g =>
          cases g with
          | none =>
              have hzn : z n = Option.none := by rw [← h, hz']; rfl
              have hs : ¬ (D.mitRuhe).passt Option.none (m + 1) = true := by
                show ¬ decide (m + 1 = 0) = true
                simp only [Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, decide_false, Bool.false_eq_true,
  not_false_eq_true]
              simp only [zeigerPasst, hz', hzn, dif_neg hs]
              try rfl
          | some f =>
              have hzn : z n = some f := by rw [← h, hz']; rfl
              by_cases h2 : D.passt f m = true
              · have h2' : (D.mitRuhe).passt (some f) (m + 1) = true := h2
                simp only [zeigerPasst, hz', hzn, dif_pos h2, dif_pos h2']
                try rfl
              · have h2' : ¬ (D.mitRuhe).passt (some f) (m + 1) = true := h2
                simp only [zeigerPasst, hz', hzn, dif_neg h2, dif_neg h2']
                try rfl
  | .ptr _ _, _ => rfl
  | .arr _ _, _ => rfl
  | .str _, _ => rfl

theorem einpassenErg_ru (z : Int → Option D.Fn) (z' : Int → Option D.mitRuhe.Fn)
    (hz : ∀ k, (z' k).bind id = z k) : ∀ (e : Option Ty) (n : Int),
    einpassenErg (D := D.mitRuhe) z' (e.map tyR) n = (einpassenErg (D := D) z e n).map (ergR e)
  | none, _ => rfl
  | some τ, n => einpassen_ru z z' hz τ n

/-- The translated image agrees with `O`'s off the root (it never names the root). -/
theorem zeiger_mitRuhe (O : Orakel D) (k : Int) : (O.mitRuhe.zeiger k).bind id = O.zeiger k := by
  show (Option.map some (O.zeiger k)).bind id = O.zeiger k
  cases O.zeiger k <;> rfl

theorem orakelRu_mitRuhe (O : Orakel D) : OrakelRu O O.mitRuhe :=
  ⟨wirkt_mitRuhe O, fun r σ => by
      show O.regLies r (worldZ (worldR σ)) = _
      rw [worldZ_worldR],
    fun g σ => by
      show O.sichtbar g (worldZ (worldR σ)) = _
      rw [worldZ_worldR],
    zeiger_mitRuhe O⟩

/-- A question to the outside translates as itself. -/
theorem worldR_fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) :
    (worldR σ).fragt q = worldR (σ.fragt q) := by rfl

theorem axiomAntwort_ruG {O : Orakel D} {O' : Orakel D.mitRuhe} (hO : OrakelRu O O') (a : D.Ax)
    (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O' a (worldR σ) (envR ρ) =
      (worldR (axiomAntwort O a σ ρ).1, (axiomAntwort O a σ ρ).2.map (ergR (D.aerg a))) := by
  unfold axiomAntwort
  rw [worldR_fragt, hO.wirkt]
  exact congrArg _ (einpassenErg_ru O.zeiger O'.zeiger hO.zeiger (D.aerg a) _)

theorem axiomAntwort_ru (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O.mitRuhe a (worldR σ) (envR ρ) =
      (worldR (axiomAntwort O a σ ρ).1, (axiomAntwort O a σ ρ).2.map (ergR (D.aerg a))) :=
  axiomAntwort_ruG (orakelRu_mitRuhe O) a σ ρ


end Gabbro.Grammatik
