module

public import Grammatik.Parser.Round.RundlaufVoll
public import Grammatik.Parser.Round.RundlaufTok.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser

theorem sammleSeg_kette (suff : List SuffFrag) (hne : suff ≠ []) (segs : List String) (R : List Token) :
    sammleSegmente (suffToks suff ++ R) segs = (segs, suffToks suff ++ R) := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s => cases f <;> rfl

theorem kette_nopar (suff : List SuffFrag) (hne : suff ≠ []) (R R2 : List Token) :
    suffToks suff ++ R ≠ .zeichen "(" :: R2 := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s => cases f <;> simp only [suffToks, List.cons_append, ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true, List.append_assoc, List.nil_append]

theorem kette_nogeneric (suff : List SuffFrag) (hne : suff ≠ []) (R R2 : List Token) :
    suffToks suff ++ R ≠ .zeichen "::" :: .zeichen "[" :: R2 := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s =>
    cases f <;> simp only [suffToks, List.cons_append, ne_eq, List.cons.injEq,
      Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true]

/-- Calls through a place through `parsePrimary` at token fuel. -/
theorem prim_methM (a : String) (suff : List SuffFrag) (xs : List SExpr) (rest : List Token) (F : Nat)
    (hka : (!istKopfWort a) = true) (hs : SuffLegs suff) (hne : suff ≠ [])
    (hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 6 * (druckToksListe xs).length + 40 ≤ F) :
    parsePrimary F (druckToks (.ext .call [] (applySuff (.variable a) suff :: xs)) ++ rest) =
      .ok (.ext .call [] (applySuff (.variable a) suff :: xs), rest) := by
  have hle := suffLen_le suff
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druck_ruf, druckToks_applySuff]
  simp only [druckToks, List.cons_append, List.nil_append, List.append_assoc]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hka)]
  simp only [parseKopf, nameText_nameTok]
  rw [sammleSeg_kette suff hne]
  have hmiss : ∀ (R2 : List Token), suffToks suff ++ (.zeichen "(" :: (druckToksListe xs ++
      (.zeichen ")" :: rest))) ≠ .zeichen "(" :: R2 := kette_nopar suff hne _
  rw [rufKopf_ohne _ _ _ _ (kette_nogeneric suff hne) hmiss]
  rw [suffWeiterM suff (.variable a) _ F'' hs (by omega)]
  obtain ⟨G, hG⟩ : ∃ G, F'' - suff.length = G + 1 := ⟨F'' - suff.length - 1, by omega⟩
  rw [hG, suff_ruf G _ _ (istVar_kette a suff hne)]
  have hA := argsM xs rest G hxs (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hA
  rw [hA]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  exact stopSuffix G' _ rest hr

/-! ### `old`, `sizeof`, `lenof`, `aligned` -/

theorem prim_altM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKopfWort a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 31 ≤ F) :
    parsePrimary F (druckToks (.old (applySuff (.variable a) suff)) ++ rest) =
      .ok (.old (applySuff (.variable a) suff), rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, parsePrimary]
  have hO := ortM a suff ([.zeichen ")"] ++ rest) F' hka hs (hrs_paren rest) (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
  simp only [hO, List.cons_append]

theorem prim_emb1M (w : String) (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hw : w = "sizeof" ∨ w = "lenof") (hka : (!istKopfWort a) = true) (hs : SuffLegs suff)
    (hp : gutPlatz (applySuff (.variable a) suff) = true)
    (htw : (!istTypWortVar (applySuff (.variable a) suff)) = true)
    (hr : ruhigSuff rest = true) (hF : 6 * (suffToks suff).length + 32 ≤ F) :
    parsePrimary F (druckToks (.built w [applySuff (.variable a) suff]) ++ rest) =
      .ok (.built w [applySuff (.variable a) suff], rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  have hO := ortM a suff ([.zeichen ")"] ++ rest) F'' hka hs (hrs_paren rest) (by omega)
  obtain rfl | rfl := hw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary]
    simp only [parseEingebaut_ein]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO]
    exact eingebaut_ein_ok "sizeof" _ rest hp htw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary]
    simp only [parseEingebaut_ein]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO]
    exact eingebaut_ein_ok "lenof" _ rest hp htw

theorem prim_alignedM (m : Nat) (a b : SExpr) (rest : List Token) (F : Nat)
    (hLa : LegsB m a) (hLb : LegsB m b)
    (hF : m + 10 ≤ F) :
    parsePrimary F (druckToks (.built "aligned" [a, b]) ++ rest) =
      .ok (.built "aligned" [a, b], rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, args_cons, args_einzeln, List.cons_append, parsePrimary]
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseEingebaut_zwei]
  have hkomma : ruhig ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true := rfl
  have hskomma : ruhigSuff ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true :=
    rfl
  have hgkomma : ruhigGleit ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true :=
    rfl
  have hOa := hLa.2.2.2.2.2.2.2 ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) F''
    hkomma hskomma hgkomma (by omega)
  have hOb := hLb.2.2.2.2.2.2.2 ([.zeichen ")"] ++ rest) F''
    (hr_paren rest) (hrs_paren rest) (hrg_paren rest) (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOa hOb
  simp only [hOa, hOb]

end Gabbro.Grammatik.Parser
