/- Part 4 of 4 of `MitRuheSemantik` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheSemantik.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem invFold_mitRuhe (P : Programm D) : ∀ (l : List D.Inv) (σ : World D),
    l.foldl (fun σ' i => σ'.lese (invSicht D.mitRuhe i) (P.mitRuhe.invariante i).orte) (worldR σ) =
      worldR (l.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ)
  | [], _ => rfl
  | i :: l, σ => by
      simp only [List.foldl_cons]
      rw [invariante_mitRuhe_orte, ← invSicht_map, lese_worldR]
      exact invFold_mitRuhe P l _

theorem lese_anfang_mitRuhe (P : Programm D) (f : D.Fn) (σ : World D) :
    (worldR σ).lese (Signatur.anfang D.mitRuhe (D.mitRuhe.signatur (some f)))
        (P.mitRuhe.requires (some f)).orte =
      worldR (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := by
  rw [requires_mitRuhe_orte]
  erw [← anfang_map (D.signatur f)]
  rw [lese_worldR]

theorem lese_ende_mitRuhe (P : Programm D) (f : D.Fn) (σ : World D) :
    (worldR σ).lese (vertragVon D.mitRuhe (some f)).ende (P.mitRuhe.ensures (some f)).orte =
      worldR (σ.lese (vertragVon D f).ende (P.ensures f).orte) := by
  rw [ensures_mitRuhe_orte]
  erw [← ende_map (vertragVon D f)]
  rw [lese_worldR]

/-- **EVERY CALL OF `P.mitRuhe` AT `some f` BEHAVES AS THE CALL OF `P` AT `f`**
    -- `requires`, body, `ensures` and owed invariants, at every depth and
    every budget: the depth-`n` call semantics of the two programs answer
    translated calls with translated answers. -/
theorem rufAt_mitRuhe (P : Programm D) (O : Orakel D) (passes : Nat) :
    ∀ n, RufRu (rufAt P O passes n) (rufAt P.mitRuhe O.mitRuhe passes n)
  | 0 => fun _ _ _ => rfl
  | n + 1 => by
      intro g σ ρ
      have ih := rufAt_mitRuhe P O passes n
      simp only [rufAt]
      rw [lese_anfang_mitRuhe]
      erw [(eval_umΛ' _ _ _ _ _).trans (eval_ru _ _ (P.requires g) ρ)]
      cases hq : (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) (P.requires g)
          (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ : Bool)
      · simp only [wahr?, valR_bool, hq, if_true]
        rfl
      · simp only [wahr?, valR_bool, hq, Bool.true_eq_false, if_false]
        erw [rumpf_mitRuhe_verhalten P O passes _ _ ih g _ ρ]
        cases execEnd O passes (rufAt P O passes n) (P.rumpf g)
            (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ with
        | zurueck σ' v =>
            simp only [endR]
            erw [lese_ende_mitRuhe]
            have he := ens_mitRuhe_eval P g (σ.lese (Signatur.anfang D (D.signatur g))
              (P.requires g).orte) (σ'.lese (vertragVon D g).ende (P.ensures g).orte) v ρ
            erw [he]
            cases hs : (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
                (P.ensures g) (σ'.lese (vertragVon D g).ende (P.ensures g).orte)
                (ergEnv (D.erg g) v ρ) : Bool)
            · simp only [wahr?, hs, if_true]
              rfl
            · simp only [wahr?, hs, Bool.true_eq_false, if_false]
              erw [invFold_mitRuhe P]
              have hf : (fun i => schuldet (D := D.mitRuhe) (some g) i &&
                  !wahr? (eval (worldR ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte)))
                    (P.mitRuhe.invariante i) (worldR ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte))) Env.nil)) =
                  (fun i => schuldet g i && !wahr? (eval ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte))
                    (P.invariante i) ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte)) Env.nil)) := by
                funext i
                rw [inv_mitRuhe_eval]
                rfl
              erw [hf]
              cases hx : D.invs.find? (fun i => schuldet g i && !wahr? (eval
                  ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte))
                  (P.invariante i) ((D.invs.filter (schuldet g)).foldl
                    (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                    (σ'.lese (vertragVon D g).ende (P.ensures g).orte)) Env.nil)) with
              | none => (try erw [hx]); rfl
              | some i => (try erw [hx]); rfl
        | why σ' r => rfl
        | leave h _ _ => exact absurd h (by decide)
        | next h _ _ => exact absurd h (by decide)
        | logik e => rfl
        | hardware e => rfl

#print axioms Gabbro.Grammatik.eval_ru
#print axioms Gabbro.Grammatik.evalArgs_ru
#print axioms Gabbro.Grammatik.lese_worldR
#print axioms Gabbro.Grammatik.req_mitRuhe_iff
#print axioms Gabbro.Grammatik.execStmt_ru
#print axioms Gabbro.Grammatik.execEnd_ru
#print axioms Gabbro.Grammatik.rumpf_mitRuhe_verhalten
#print axioms Gabbro.Grammatik.rufAt_mitRuhe


end Gabbro.Grammatik
