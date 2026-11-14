module

public import Grammatik.Parser.Round.RundlaufTok.Teil3a

public import Grammatik.Parser.Round.RundlaufVoll
public import Grammatik.Parser.Round.RundlaufTok.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser
/-- Size and printability of index payloads. -/
theorem suff_idx_mem : ∀ (suff : List SuffFrag) (i : SExpr), SuffFrag.idx i ∈ suff →
    suffGut suff = true → groesse i ≤ suffGroesse suff ∧ gut i = true := by
  intro suff
  induction suff with
  | nil => intro i h; simp only [List.not_mem_nil] at h
  | cons f s ih =>
    intro i h hg
    simp only [List.mem_cons] at h
    cases f with
    | dot g =>
      simp only [suffGut] at hg
      rcases h with h | h
      · cases h
      · obtain ⟨h1, h2⟩ := ih i h hg; exact ⟨by simp only [suffGroesse]; omega, h2⟩
    | arrow g =>
      simp only [suffGut] at hg
      rcases h with h | h
      · cases h
      · obtain ⟨h1, h2⟩ := ih i h hg; exact ⟨by simp only [suffGroesse]; omega, h2⟩
    | idx j =>
      simp only [suffGut, Bool.and_eq_true] at hg
      rcases h with h | h
      · cases h; simp only [suffGroesse]; exact ⟨by omega, hg.1⟩
      · obtain ⟨h1, h2⟩ := ih i h hg.2; exact ⟨by simp only [suffGroesse]; omega, h2⟩

/-! ### Calls -/

/-- One argument through `parseArg` at token fuel (mirror of `arg_legs`). -/
theorem argM (x : SExpr) (sep : Token) (S : List Token) (F : Nat)
    (hL : LegsB (fb x) x) (hxg : gut x = true)
    (hsep : sep = .zeichen "," ∨ sep = .zeichen ")") (hF : fb x + 9 ≤ F) :
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
    obtain ⟨a, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
    rw [hxb] at hcon
    simp only [List.cons_append] at hcon
    injection hcon with _ ht
    cases hR : R2 with
    | nil =>
      rw [hR] at ht
      simp only [List.nil_append, List.cons_append] at ht
      injection ht with hsep2 _
      cases hsep with
      | inl h => subst h; simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
      | inr h => subst h; simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp only [hxb, hR, List.mem_cons, true_or, or_true]
      exact keinDP_tree (groesse x) x (Nat.le_refl _) hxg b hbmem hb
  simp only [parseArg]
  have hr1 : ruhig ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr2 : ruhigSuff ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr3 : ruhigGleit ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hOr := hL.2.2.2.2.2.2.2 ([sep] ++ S) F' hr1 hr2 hr3 (by omega)
  simpa only [List.append_assoc] using hOr

theorem kopf_nicht_zu (x : SExpr) (hxg : gut x = true) (S : List Token) (R2 : List Token) :
    druckToks x ++ S ≠ .zeichen ")" :: R2 := by
  intro hcon
  have hkop := toksKopf (groesse x) x (Nat.le_refl _) hxg
  have hne : druckToks x ≠ [] := by
    intro he
    have hlen := toksLang (groesse x) x (Nat.le_refl _)
    rw [he] at hlen
    simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
  obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
  have ha := hkop a R3 hxb
  rw [hxb] at hcon
  simp only [List.cons_append] at hcon
  injection hcon with ha2 _
  exact ha ha2

/-- Whole argument lists through `parseArgs` at token fuel (mirror of `args_legs`). -/
theorem argsM : ∀ (xs : List SExpr) (rest : List Token) (F : Nat),
    (∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true) →
    6 * (druckToksListe xs).length + 36 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) = .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro rest F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append, List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hF
    obtain ⟨hLx, hxg⟩ := hs x (by simp only [List.mem_cons, true_or])
    have hzs : ∀ y ∈ zs, LegsB (fb y) y ∧ gut y = true :=
      fun y hy => hs y (List.mem_cons_of_mem _ hy)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases zs with
    | nil =>
      rw [args_einzeln] at ⊢ hF
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠ .zeichen ")" :: R2 := by
        intro R2; rw [List.append_assoc]; exact kopf_nicht_zu x hxg _ R2
      simp only [parseArgs, hmiss2]
      have harg := argM x (.zeichen ")") rest F' hLx hxg (Or.inr rfl)
        (by simp only [fb] at ⊢; omega)
      simp only [harg, List.cons_append]
      rfl
    | cons y ys =>
      rw [args_cons] at ⊢ hF
      simp only [List.length_append, List.length_cons, List.length_nil] at hF
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠ .zeichen ")" :: R2 := by
        intro R2; simp only [List.append_assoc]; exact kopf_nicht_zu x hxg _ R2
      simp only [parseArgs, hmiss2]
      have harg := argM x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hLx hxg (Or.inl rfl) (by simp only [fb] at ⊢; omega)
      have htail := ihzs rest F' hzs (by omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append]

/-- Calls through `parsePrimary` at token fuel (mirror of `prim_ruf_legs`). -/
theorem prim_rufM (f : String) (xs : List SExpr) (rest : List Token) (F : Nat)
    (hf : (!istKopfWort f) = true) (hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true)
    (benign : ruhigSuff rest = true)
    (hF : 6 * (druckToksListe xs).length + 38 ≤ F) :
    parsePrimary F (druckToks (.call f xs) ++ rest) = .ok (.call f xs, rest) := by
  have hkaf' : istKopfWort f = false := nichtWahr_falsch _ hf
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ hkaf']
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [kopf_ruf_head]
  have hA := argsM xs rest F'' hxs (by omega)
  simp only [List.append_assoc] at hA ⊢
  simp only [List.nil_append, hA]
  exact awaitSuffix_stop _ _ benign

/-! ### Calls through a place (`o.is_some()`, `p->f(x)`) -/

/-- Every fragment prints at least one token. -/
theorem suffLen_le : ∀ (suff : List SuffFrag), suff.length ≤ (suffToks suff).length
  | [] => Nat.le_refl _
  | .dot _ :: s => by have := suffLen_le s; simp only [suffToks, List.length_cons]; omega
  | .arrow _ :: s => by have := suffLen_le s; simp only [suffToks, List.length_cons]; omega
  | .idx i :: s => by
    have := suffLen_le s
    simp only [suffToks, List.length_cons, List.length_append, List.length_singleton]; omega

/-- A suffix chain read off any follow: `parseSuffixe` spends one fuel per fragment and stands at the
    applied chain before the follow. -/
theorem suffWeiterM : ∀ (suff : List SuffFrag) (base : SExpr) (R : List Token) (F : Nat),
    SuffLegs suff → 6 * (suffToks suff).length + 29 ≤ F →
    parseSuffixe F base (suffToks suff ++ R) = parseSuffixe (F - suff.length) (applySuff base suff) R := by
  intro suff
  induction suff with
  | nil => intro base R F _ _; simp only [suffToks, List.nil_append, List.length_nil, Nat.sub_zero, applySuff]
  | cons frag suff ih =>
    intro base R F hs hF
    have hs' := suffLegs_tail hs
    simp only [List.length_cons]
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [Nat.add_sub_add_right]
    cases frag with
    | dot f =>
      simp only [suffToks, List.cons_append]
      have hstep : parseSuffixe (F' + 1) base
          (.zeichen "." :: nameTok f :: (suffToks suff ++ R)) =
            parseSuffixe F' (.field base f) (suffToks suff ++ R) := by
        unfold nameTok
        split <;> simp only [parseSuffixe, nameText]
      rw [hstep]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ R F' hs' (by omega)
    | arrow f =>
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe, nameText_nameTok]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ R F' hs' (by omega)
    | idx i =>
      have hLi := hs i (by simp only [List.mem_cons, true_or])
      simp only [suffToks, List.length_cons, List.length_append, List.length_singleton] at hF
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe]
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ R) = true := rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ R) = true := rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ R) = true := rfl
      have hOi := hLi.2.2.2.2.2.2.2 ([.zeichen "]"] ++ suffToks suff ++ R) F' hr1 hr2 hr3
        (by simp only [fb]; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append]
      simp only [applySuff]
      exact ih _ R F' hs' (by omega)

/-- A chain that is not a bare name reads `(` as a call through it. -/
theorem suff_ruf (G : Nat) (c : SExpr) (T : List Token) (hc : istVar c = false) :
    parseSuffixe (G + 1) c (.zeichen "(" :: T) =
      match parseArgs G T with
      | .ok (args, rest') => parseSuffixe G (.ext .call [] (c :: args)) rest'
      | .error e => .error e := by
  cases c with
  | «variable» s => simp only [istVar, Bool.true_eq_false] at hc
  | _ => simp only [parseSuffixe] <;> rfl

theorem istVar_applySuff : ∀ (suff : List SuffFrag) (base : SExpr), istVar base = false →
    istVar (applySuff base suff) = false
  | [], _, h => h
  | .dot _ :: s, _, _ => istVar_applySuff s _ rfl
  | .arrow _ :: s, _, _ => istVar_applySuff s _ rfl
  | .idx _ :: s, _, _ => istVar_applySuff s _ rfl

theorem istVar_kette (a : String) (suff : List SuffFrag) (hne : suff ≠ []) :
    istVar (applySuff (.variable a) suff) = false := by
  cases suff with
  | nil => exact absurd rfl hne
  | cons f s => cases f <;> exact istVar_applySuff s _ rfl

end Gabbro.Grammatik.Parser
