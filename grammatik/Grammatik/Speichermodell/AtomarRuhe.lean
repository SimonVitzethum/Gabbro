/-
  File:      Grammatik/Speichermodell/AtomarRuhe.lean
  Subject:   The idle root (MitRuhe.lean) and the semantics with the atomic rely: a body of
             `P.mitRuhe` under `execStmtHA` runs as the body of `P`, the atomic environment
             translated like the lock move (`hA`). The copy of MitRuheSperre.lean §4/§5 over
             `execStmtHA`. Opus lane O25b, 2026-09-26. Standalone.
-/
import Grammatik.MitRuheSperre
import Grammatik.Speichermodell.SperreSemA

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A read through translated environments is the translated read. -/
theorem leseA_worldR {A : AUmwelt D} {A' : AUmwelt D.mitRuhe}
    (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ)) (σ : World D) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) :
    leseA A' (worldR σ) (Λ.map resR) os = worldR (leseA A σ Λ os) := by
  unfold leseA
  rw [lese_worldR, hA]

section HilfenA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)

theorem execStmtHA_nachΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execStmtHA S O U A passes R (Stmt.nachΛ h s) σ ρ = execStmtHA S O U A passes R s σ ρ := by
  subst h; rfl

theorem execBlockHA_vorΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') (σ : World D) (ρ : Env D Γ) :
    execBlockHA S O U A passes R (Block.vorΛ h b) σ ρ = execBlockHA S O U A passes R b σ ρ := by
  subst h; rfl

theorem execEndHA_umΛ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) (σ : World D) (ρ : Env D Γ) :
    execEndHA S O U A passes R (Endblock.umΛ h e) σ ρ = execEndHA S O U A passes R e σ ρ := by
  subst h; rfl

end HilfenA

/-! ## 5. Every statement, block and end block, up to the label -/

section HauptA

variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (A : AUmwelt D) (A' : AUmwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ))
  (hR : RufRel R R')

include hO hU hA hR

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement under the lock-invariant
    semantics**, up to the label of a logic failure. -/
theorem execStmtHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS s) (worldR σ) (envR ρ))
      (execStmtHA S O U A passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [orte2, leseA_worldR hA, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignDurch p t ht f i e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
        kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), leseA_worldR hA, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, Λ, _, .schreibBytes t f hf n i hlo hhi e hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [orte2, leseA_worldR hA, eval_ru, eval_ru, schreibBytes_worldR t f hf]
      rfl
  | _, _, Λ, _, .assignVar x e, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru, envR_set]
      rfl
  | _, _, Λ, _, .uebergang (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
      erw [leseA_worldR hA, eval_ru]
      erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
      by_cases hc : (hτ ▸ (leseA A σ Λ (Sum.inl t :: i.orte)).slots t
          (eval (leseA A σ Λ (Sum.inl t :: i.orte)) i (leseA A σ Λ (Sum.inl t :: i.orte)) ρ).n f :
          Wert D (.int lo hi)).n = von
      · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _,
          schreibSlot_worldR]
        rfl
      · erw [if_neg hc, if_neg hc]
        rfl
  | _, _, Λ, _, .ite c t e, σ, ρ => by
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      cases h : (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ : Bool)
      · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
        exact execBlockHA_ru e _ ρ
      · simp only [wahr?, valR_bool, h, if_true]
        exact execBlockHA_ru t _ ρ
  | _, _, Λ, _, .onOption o p a, σ, ρ => by
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases h : eval (leseA A σ Λ o.orte) o (leseA A σ Λ o.orte) ρ with
      | none => exact execBlockHA_ru a _ ρ
      | some k =>
          simp only
          exact AusRelRu.schrumpf (execBlockHA_ru p _ (Env.cons k ρ))
  | _, _, Λ, _, .onTag v arms, σ, ρ => by
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      exact execArmsHA_ru arms _ _ ρ
  | _, _, Λ, _, .onGrund r arms, σ, ρ => by
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      exact execGrundHA_ru arms _ _ ρ
  | _, _, Λ, _, .call g args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmtHA_nachΛ]
      simp only [execStmtHA]
      erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
      rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (leseA A σ Λ args.orte)
            (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
        | ok σ' v => (try erw [hx]); exact Or.inl rfl
        | grund σ' r => exact (Fin.cast hr r).elim0
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmtHA_nachΛ]
      simp only [execStmtHA]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [leseA_worldR hA, eval_ru, evalArgs_ru]
      cases h : eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg]
          rcases hR g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
              (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ))
            with hx' | ⟨e', e, h1, h2, ht⟩
          · erw [hx']
            cases hx : R g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
                (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ)) with
            | ok σ' v => (try erw [hx]); exact Or.inl rfl
            | grund σ' r => exact keinGrundSig hg hr r
            | logik e => (try erw [hx]); exact Or.inl rfl
            | hardware e => (try erw [hx]); exact Or.inl rfl
          · erw [h1, h2]
            exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .locks L hr body, σ, ρ => by
      simp only [ruS, execStmtHA]
      rw [hU, nimmt_worldR]
      exact AusRelRu.frei S L (execBlockHA_ru body ((U L σ).nimmt L) ρ)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmtHA]
      exact execBlockHA_ru body σ ρ
  | l, _, Λ, _, .traverse t inv body, σ, ρ => by
      simp only [ruS, execStmtHA]
      have hL := traverseLauf_rel (l := l) (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
        (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
        (fun σ ρ => (leseA A σ Λ inv.orte, wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ)))
        (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE inv).orte,
          wahr? (eval (leseA A' σ (Λ.map resR) (ruE inv).orte) (ruE inv)
            (leseA A' σ (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlockHA_ru body σ ρ)
        (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?])
        (alleIndizes (D.count t)) σ ρ
      rw [map_valR_int] at hL
      exact hL
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ => by
      simp only [ruS, execStmtHA]
      exact retryLauf_rel (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
        (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
        (fun σ ρ => (leseA A σ Λ bis.orte, wahr? (eval (leseA A σ Λ bis.orte) bis (leseA A σ Λ bis.orte) ρ)))
        (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE bis).orte,
          wahr? (eval (leseA A' σ (Λ.map resR) (ruE bis).orte) (ruE bis)
            (leseA A' σ (Λ.map resR) (ruE bis).orte) ρ)))
        (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ)
        (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB ueber) σ ρ)
        (fun σ ρ => execBlockHA_ru body σ ρ)
        (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?])
        (fun σ ρ => execBlockHA_ru ueber σ ρ) n σ ρ
  | _, _, Λ, _, .forever a inv body, σ, ρ => by
      simp only [ruS, execStmtHA]
      exact foreverLauf_rel a (fun σ ρ => execBlockHA S O U A passes R body σ ρ)
        (fun σ ρ => execBlockHA S.mitRuhe O' U' A' passes R' (ruB body) σ ρ)
        (fun σ ρ => (leseA A σ Λ inv.orte, wahr? (eval (leseA A σ Λ inv.orte) inv (leseA A σ Λ inv.orte) ρ)))
        (fun σ ρ => (leseA A' σ (Λ.map resR) (ruE inv).orte,
          wahr? (eval (leseA A' σ (Λ.map resR) (ruE inv).orte) (ruE inv)
            (leseA A' σ (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlockHA_ru body σ ρ)
        (fun σ ρ => by simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_bool, wahr?]) passes σ ρ
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwort_ruG hO]
      cases axiomAntwort O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some _ => rfl
  | _, _, Λ, _, .regSchreib r hk e, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA]
      rfl
  | _, _, _, _, .transition .., σ, ρ => Or.inl rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, _, _, .advances .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtHA_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtHA_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ => by
      refine Or.inl ?_
      simp only [ruS, execStmtHA]
      erw [ruErg_orte, leseA_worldR hA, evalErg_ru]
      rfl
  | _, _, _, _, .retGrund .., σ, ρ => Or.inl rfl
  | _, _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, _, .next _, σ, ρ => Or.inl rfl

theorem execBlockHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB b) (worldR σ) (envR ρ))
      (execBlockHA S O U A passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => Or.inl rfl
  | _, _, _, _, .cons s rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rcases execStmtHA_ru s σ ρ with h | ⟨e', e, h1, h2, ht⟩
      · rw [h]
        cases execStmtHA S O U A passes R s σ ρ with
        | ok σ' ρ' => exact execBlockHA_ru rest σ' ρ'
        | _ => exact Or.inl rfl
      · rw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bind e rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      exact AusRelRu.schrumpf (execBlockHA_ru rest (leseA A σ Λ e.orte)
        (Env.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ))
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
      rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (leseA A σ Λ args.orte)
            (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execBlockHA_vorΛ, ergWert_ru he]
            exact AusRelRu.schrumpf (execBlockHA_ru rest σ' (Env.cons (ergWert he v) ρ))
        | grund σ' r => exact (Fin.cast hr r).elim0
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [leseA_worldR hA, eval_ru, evalArgs_ru]
      cases h : eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg]
          rcases hR g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
              (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ))
            with hx' | ⟨e', e, h1, h2, ht⟩
          · erw [hx']
            cases hx : R g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
                (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ)) with
            | ok σ' v =>
                try erw [hx]
                simp only [rufR]
                erw [execBlockHA_vorΛ, ergWert_ru (ergSig hg he)]
                exact AusRelRu.schrumpf
                  (execBlockHA_ru rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
            | grund σ' r => exact keinGrundSig hg hr r
            | logik e => (try erw [hx]); exact Or.inl rfl
            | hardware e => (try erw [hx]); exact Or.inl rfl
          · erw [h1, h2]
            exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
      rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (leseA A σ Λ args.orte)
            (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execBlockHA_vorΛ, ergWert_ru he]
            exact AusRelRu.schrumpf (execBlockHA_ru rest σ' (Env.cons (ergWert he v) ρ))
        | grund σ' r =>
            try erw [hx]
            simp only [rufR]
            erw [execEndHA_umΛ]
            exact EndRel.zuAusgang (EndRel.schrumpf (execEndHA_ru err σ' (Env.cons r ρ)))
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwort_ruG hO]
      cases axiomAntwort O a (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => exact Or.inl rfl
          | some v =>
              simp only [Option.map]
              rw [ergWert_ru he]
              exact AusRelRu.schrumpf (execBlockHA_ru rest σ' (Env.cons (ergWert he v) ρ))
  | _, _, _, _, .regLies r hk rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
      cases einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          erw [rzusage_mitRuhe]
          cases D.rzusage r v with
          | false => exact Or.inl rfl
          | true =>
              simp only [if_true]
              exact AusRelRu.schrumpf (execBlockHA_ru rest σ (Env.cons v ρ))
  | _, _, Λ, _, .regLiesElse r hk zusage sonst rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
      cases einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ruE_orte, leseA_worldR hA]
          have ez := eval_ru (leseA A σ Λ zusage.orte) (leseA A σ Λ zusage.orte) zusage (Env.cons v ρ)
          change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
          rw [ez]
          cases h : (eval (leseA A σ Λ zusage.orte) zusage (leseA A σ Λ zusage.orte) (Env.cons v ρ) : Bool) with
          | false =>
              simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
              exact EndRel.zuAusgang (execEndHA_ru sonst _ ρ)
          | true =>
              simp only [wahr?, valR_bool, h, if_true]
              exact AusRelRu.schrumpf (execBlockHA_ru rest _ (Env.cons v ρ))
  | _, _, Λ, _, .awaits g payload hp hL rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
        leseA_worldR hA, hO.sichtbar]
      cases O.sichtbar g (leseA A σ Λ [Sum.inr g]) with
      | false => exact Or.inl rfl
      | true =>
          simp only [if_true]
          exact AusRelRu.schrumpf (execBlockHA_ru rest (leseA A σ Λ [Sum.inr g])
            (Env.cons ((leseA A σ Λ [Sum.inr g]).globs g) ρ))
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), leseA_worldR hA]
      have ez := eval_ru (leseA A σ Λ (Sum.inr g :: neu.orte)) (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
        (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)
      change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
      rw [show ((worldR (leseA A σ Λ (Sum.inr g :: neu.orte))).globs g) =
        valR _ ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
      exact AusRelRu.schrumpf (execBlockHA_ru rest
        ((leseA A σ Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
          (leseA A σ Λ (Sum.inr g :: neu.orte)) (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
        (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ))
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_int]
      by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
          (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
      · erw [dif_pos hc, dif_pos hc]
        exact AusRelRu.schrumpf (execBlockHA_ru rest _
          (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
      · erw [dif_neg hc, dif_neg hc]
        exact EndRel.zuAusgang (execEndHA_ru sonst _ ρ)
  | _, _, Λ, _, .pruefung c sonst rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      cases h : (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          exact EndRel.zuAusgang (execEndHA_ru sonst _ ρ)
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact execBlockHA_ru rest _ ρ
  | _, _, Λ, _, .gleit op a b lo hi rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [orte2, leseA_worldR hA, eval_ru, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitRechne op
          (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ).x
          (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ).x) with
      | none => exact Or.inl rfl
      | some v => exact AusRelRu.schrumpf (execBlockHA_ru rest _ (Env.cons v ρ))
  | _, _, _, _, .gleitLit q lo hi rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      cases gleitPasst lo hi (bruch q) with
      | none => exact Or.inl rfl
      | some v => exact AusRelRu.schrumpf (execBlockHA_ru rest _ (Env.cons v ρ))
  | _, _, Λ, _, .gleitVon e lo hi rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitAusInt (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n) with
      | none => exact Or.inl rfl
      | some v => exact AusRelRu.schrumpf (execBlockHA_ru rest _ (Env.cons v ρ))
  | _, _, Λ, _, .gleitNarrow e lo hi sonst rest, σ, ρ => by
      simp only [ruB, execBlockHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x with
      | none => exact EndRel.zuAusgang (execEndHA_ru sonst _ ρ)
      | some v => exact AusRelRu.schrumpf (execBlockHA_ru rest _ (Env.cons v ρ))

theorem execEndHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd e) (worldR σ) (envR ρ))
      (execEndHA S O U A passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ => by
      refine Or.inl ?_
      simp only [ruEnd, execEndHA]
      erw [ruErg_orte, leseA_worldR hA, evalErg_ru]
      rfl
  | _, _, _, .retGrund .., σ, ρ => Or.inl rfl
  | _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, .next _, σ, ρ => Or.inl rfl
  | _, _, _, .cons s rest, σ, ρ => by
      simp only [ruEnd, execEndHA]
      rcases execStmtHA_ru s σ ρ with h | ⟨e', e, h1, h2, ht⟩
      · rw [h]
        cases execStmtHA S O U A passes R s σ ρ with
        | ok σ' ρ' => exact execEndHA_ru rest σ' ρ'
        | _ => exact Or.inl rfl
      · rw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩
  | _, _, Λ, .bind e rest, σ, ρ => by
      simp only [ruEnd, execEndHA]
      rw [ruE_orte, leseA_worldR hA, eval_ru]
      exact EndRel.schrumpf (execEndHA_ru rest (leseA A σ Λ e.orte)
        (Env.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ))

theorem execArmsHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    AusRelRu (execArmsHA S.mitRuhe O' U' A' passes R' (ruArms arms) (valR (.sum cs) v)
        (worldR σ) (envR ρ))
      (execArmsHA S O U A passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlockHA_ru b σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ =>
      AusRelRu.schrumpf (execBlockHA_ru b σ (Env.cons nutz ρ))
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsHA_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsHA_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrundHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    AusRelRu (execGrundHA S.mitRuhe O' U' A' passes R' (ruGArms arms) r (worldR σ) (envR ρ))
      (execGrundHA S O U A passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlockHA_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrundHA_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end HauptA

/-- **The body of `some f` in `P.mitRuhe` under the lock-invariant semantics
    runs as the body of `f` in `P`**, up to the label of a logic failure. -/
theorem rumpfHA_mitRuhe (P : Programm D) (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe)
    (hO : OrakelRu O O') (U : Umwelt D) (U' : Umwelt D.mitRuhe) (A : AUmwelt D)
    (A' : AUmwelt D.mitRuhe) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ)) (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ))
    (hR : RufRel R R')
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    @EndRel D (vertragVon D f) false (D.params f)
      (execEndHA S.mitRuhe O' U' A' passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ))
      (execEndHA S O U A passes R (P.rumpf f) σ ρ) := by
  have e := execEndHA_umΛ S.mitRuhe O' U' A' passes R' (anfang_map (D.signatur f))
    (ruEnd (P.rumpf f)) (worldR σ) (envR ρ)
  show @EndRel D (vertragVon D f) false (D.params f) (execEndHA S.mitRuhe O' U' A' passes R'
    (Endblock.umΛ (anfang_map (D.signatur f)) (ruEnd (P.rumpf f))) (worldR σ) (envR ρ)) _
  rw [e]
  exact execEndHA_ru S O O' hO U U' A A' passes R R' hU hA hR (P.rumpf f) σ ρ

#print axioms Gabbro.Grammatik.execEndHA_ru
#print axioms Gabbro.Grammatik.rumpfHA_mitRuhe

end Gabbro.Grammatik
