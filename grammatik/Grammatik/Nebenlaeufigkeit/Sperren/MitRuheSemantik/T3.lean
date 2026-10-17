/- Part 3 of 4 of `MitRuheSemantik` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheSemantik.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Haupt

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hR : RufRu R R')

include hR

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement**: from the translated
    world and environment to the translated outcome, given a handler that
    answers translated calls with translated answers. -/
theorem execStmt_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    execStmt O.mitRuhe passes R' (ruS s) (worldR σ) (envR ρ) = ausR (execStmt O passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [orte2, lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignThru p t ht f i e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [show (ruE p).orte ++ (ruE i).orte ++ (ruE e).orte = p.orte ++ i.orte ++ e.orte from
        kongr₂ (· ++ ·) (orte2 p i) (ruE_orte e), lese_worldR, eval_ru, eval_ru, schreibSlot_worldR]
      rfl
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, Λ, _, .putBytes t f hf n i hlo hhi e hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [orte2, lese_worldR, eval_ru, eval_ru, schreibBytes_worldR t f hf]
      rfl
  | _, _, Λ, _, .assignVar x e, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru, envR_set]
      rfl
  | _, _, Λ, _, .shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      erw [show (Sum.inl t :: (ruE i).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inl t :: i.orte from congrArg (Sum.inl t :: ·) (ruE_orte i)]
      erw [lese_worldR, eval_ru]
      erw [slotInt_cast_worldR _ t f hτ (congrArg tyR hτ)]
      by_cases hc : (hτ ▸ (σ.lese Λ (Sum.inl t :: i.orte)).slots t
          (eval (σ.lese Λ (Sum.inl t :: i.orte)) i (σ.lese Λ (Sum.inl t :: i.orte)) ρ).n f :
          Wert D (.int lo hi)).n = von
      · erw [if_pos hc, if_pos hc, int_cast_gen' (D.typ t f) lo hi hτ (congrArg tyR hτ) _, schreibSlot_worldR]
        rfl
      · erw [if_neg hc, if_neg hc]
        rfl
  | _, _, Λ, _, .ite c t e, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
      · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
        exact execBlock_ru e _ ρ
      · simp only [wahr?, valR_bool, h, if_true]
        exact execBlock_ru t _ ρ
  | _, _, Λ, _, .onOption o p a, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases h : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ with
      | none => exact execBlock_ru a _ ρ
      | some k =>
          simp only
          rw [← ausR_schrumpf, ← execBlock_ru p _ (Env.cons k ρ)]
          rfl
  | _, _, Λ, _, .onTag v arms, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact execArms_ru arms _ _ ρ
  | _, _, Λ, _, .onWhy r arms, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru]
      exact execGrund_ru arms _ _ ρ
  | _, _, Λ, _, .call g args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      simp only [execStmt]
      erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v => (try erw [hx]); rfl
      | why σ' r => exact (Fin.cast hr r).elim0
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      simp only [execStmt]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [lese_worldR, eval_ru, evalArgs_ru]
      cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg, hR]
          cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v => (try erw [hx]); rfl
          | why σ' r => exact keinGrundSig hg hr r
          | logik e => (try erw [hx]); rfl
          | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .locks L hr body, σ, ρ => by
      simp only [ruS, execStmt]
      rw [nimmt_worldR]
      exact (congrArg _ (execBlock_ru body (σ.nimmt L) ρ)).trans (ausR_gibt L _)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmt]
      exact execBlock_ru body σ ρ
  | _, _, Λ, _, .traverse t inv body, σ, ρ => by
      simp only [ruS, execStmt]
      conv => lhs; rw [← map_valR_int (D := D) 0 (D.count t - 1) (alleIndizes (D.count t))]
      refine traverseLauf_ru (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
        (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlock_ru body σ ρ) (fun σ ρ => ?_) (alleIndizes (D.count t)) σ ρ
      simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ => by
      simp only [ruS, execStmt]
      refine retryLauf_ru (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
        (fun σ ρ => (σ.lese Λ bis.orte, wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE bis).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE bis).orte) (ruE bis) (σ.lese (Λ.map resR) (ruE bis).orte) ρ)))
        (execBlock O passes R ueber) (execBlock O.mitRuhe passes R' (ruB ueber))
        (fun σ ρ => execBlock_ru body σ ρ) (fun σ ρ => ?_) (fun σ ρ => execBlock_ru ueber σ ρ) n σ ρ
      simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  | _, _, Λ, _, .forever a inv body, σ, ρ => by
      simp only [ruS, execStmt]
      refine foreverLauf_ru a (execBlock O passes R body) (execBlock O.mitRuhe passes R' (ruB body))
        (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
        (fun σ ρ => (σ.lese (Λ.map resR) (ruE inv).orte,
          wahr? (eval (σ.lese (Λ.map resR) (ruE inv).orte) (ruE inv) (σ.lese (Λ.map resR) (ruE inv).orte) ρ)))
        (fun σ ρ => execBlock_ru body σ ρ) (fun σ ρ => ?_) passes σ ρ
      simp only [ruE_orte, lese_worldR, eval_ru, valR_bool, wahr?]
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ => by
      simp only [ruS, execStmt]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some _ => rfl
  | _, _, Λ, _, .regWrite r hk e, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR]
      rfl
  | _, _, _, _, .transition .., σ, ρ => rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ => by
      simp only [ruS, execStmt]
      rw [ruE_orte, lese_worldR, eval_ru, schreibGlob_worldR]
      rfl
  | _, _, _, _, .advances .., σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ => by
      simp only [ruS, execStmt]
      erw [ruErg_orte, lese_worldR, evalErg_ru]
      rfl
  | _, _, _, _, .retWhy .., σ, ρ => rfl
  | _, _, _, _, .leave _, σ, ρ => rfl
  | _, _, _, _, .next _, σ, ρ => rfl

theorem execBlock_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    execBlock O.mitRuhe passes R' (ruB b) (worldR σ) (envR ρ) = ausR (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => rfl
  | _, _, _, _, .cons s rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [execStmt_ru s σ ρ]
      cases execStmt O passes R s σ ρ with
      | ok σ' ρ' => exact execBlock_ru rest σ' ρ'
      | _ => rfl
  | _, _, Λ, _, .bind e rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru, ← ausR_schrumpf, ← execBlock_ru rest _ _]
      rfl
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execBlock_vorΛ, ergWert_ru he]
          exact (congrArg Ausgang.schrumpf (execBlock_ru rest σ' (Env.cons (ergWert he v) ρ))).trans
            (ausR_schrumpf _)
      | why σ' r => exact (Fin.cast hr r).elim0
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
        kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
      erw [lese_worldR, eval_ru, evalArgs_ru]
      cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
      | mk g hg =>
          rw [valR_fnptr]
          dsimp only
          erw [umsig_ru hg, hR]
          cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
          | ok σ' v =>
              try erw [hx]
              simp only [rufR]
              erw [execBlock_vorΛ, ergWert_ru (ergSig hg he)]
              exact (congrArg Ausgang.schrumpf
                (execBlock_ru rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))).trans (ausR_schrumpf _)
          | why σ' r => exact keinGrundSig hg hr r
          | logik e => (try erw [hx]); rfl
          | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, hR]
      cases hx : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execBlock_vorΛ, ergWert_ru he]
          exact (congrArg Ausgang.schrumpf (execBlock_ru rest σ' (Env.cons (ergWert he v) ρ))).trans
            (ausR_schrumpf _)
      | why σ' r =>
          try erw [hx]
          simp only [rufR]
          erw [execEnd_umΛ]
          exact (congrArg (fun a => EndAusgang.zuAusgang (EndAusgang.schrumpf a))
            (execEnd_ru err σ' (Env.cons r ρ))).trans
            ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [Option.map]
              rw [ergWert_ru he, ← ausR_schrumpf, ← execBlock_ru rest σ' (Env.cons _ ρ)]
              rfl
  | _, _, Λ, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [ruB, execBlock]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
            rw [ergWert_ru he, ← ausR_schrumpf, ← execBlock_ru rest σ' (Env.cons _ ρ)]
            rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            exact (congrArg (fun a => EndAusgang.zuAusgang (EndAusgang.schrumpf a))
              (execEnd_ru err σ' (Env.cons (τ := .why (D.agruende a)) r ρ))).trans
              ((congrArg EndAusgang.zuAusgang (endR_schrumpf _)).trans (endR_zuAusgang _))
  | _, _, _, _, .regRead r hk rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [regLies_mitRuhe, einpassen_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)]
      cases einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | none => rfl
      | some v =>
          simp only [Option.map]
          erw [rzusage_mitRuhe]
          cases D.rzusage r v with
          | false => rfl
          | true =>
              simp only [if_true]
              rw [← ausR_schrumpf, ← execBlock_ru rest σ (Env.cons v ρ)]
              rfl
  | _, _, Λ, _, .regReadElse r hk zusage sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [regLies_mitRuhe, einpassen_ru O.zeiger O.mitRuhe.zeiger (zeiger_mitRuhe O)]
      cases einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | none => rfl
      | some v =>
          simp only [Option.map]
          rw [ruE_orte, lese_worldR]
          have ez := eval_ru (σ.lese Λ zusage.orte) (σ.lese Λ zusage.orte) zusage (Env.cons v ρ)
          change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
          rw [ez]
          cases h : (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (Env.cons v ρ) : Bool) with
          | false =>
              simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
              rw [← endR_zuAusgang, execEnd_ru sonst _ ρ]
          | true =>
              simp only [wahr?, valR_bool, h, if_true]
              rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
              rfl
  | _, _, Λ, _, .awaits g payload hp hL rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [sichtbar_mitRuhe]
      cases O.sichtbar g σ with
      | false => rfl
      | true =>
          simp only [if_true]
          rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
            lese_worldR, ← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons _ ρ)]
          rfl
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
        Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
      have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
        (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
      change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
      rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
        valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR,
        ← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons _ ρ)]
      rfl
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
      by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
      · erw [dif_pos hc, dif_pos hc]
        exact (congrArg Ausgang.schrumpf (execBlock_ru rest _
          (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))).trans
          (ausR_schrumpf _)
      · erw [dif_neg hc, dif_neg hc, ← endR_zuAusgang, execEnd_ru sonst _ ρ]
  | _, _, Λ, _, .check c sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru]
      cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          rw [← endR_zuAusgang, execEnd_ru sonst _ ρ]
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact execBlock_ru rest _ ρ
  | _, _, Λ, _, .float op a b lo hi rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [orte2, lese_worldR, eval_ru, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitRechne op
          (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
          (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => rfl
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl
  | _, _, _, _, .floatLit q lo hi rest, σ, ρ => by
      simp only [ruB, execBlock]
      cases gleitPasst lo hi (bruch q) with
      | none => rfl
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl
  | _, _, Λ, _, .floatOf e lo hi rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) with
      | none => rfl
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl
  | _, _, Λ, _, .floatNarrow e lo hi sonst rest, σ, ρ => by
      simp only [ruB, execBlock]
      rw [ruE_orte, lese_worldR, eval_ru]
      try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
      cases gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x with
      | none => rw [← endR_zuAusgang, execEnd_ru sonst _ ρ]
      | some v =>
          rw [← ausR_schrumpf, ← execBlock_ru rest _ (Env.cons v ρ)]
          rfl

theorem execEnd_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    execEnd O.mitRuhe passes R' (ruEnd e) (worldR σ) (envR ρ) = endR (execEnd O passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ => by
      simp only [ruEnd, execEnd]
      erw [ruErg_orte, lese_worldR, evalErg_ru]
      rfl
  | _, _, _, .retWhy .., σ, ρ => rfl
  | _, _, _, .leave _, σ, ρ => rfl
  | _, _, _, .next _, σ, ρ => rfl
  | _, _, _, .cons s rest, σ, ρ => by
      simp only [ruEnd, execEnd]
      rw [execStmt_ru s σ ρ]
      cases execStmt O passes R s σ ρ with
      | ok σ' ρ' => exact execEnd_ru rest σ' ρ'
      | _ => rfl
  | _, _, Λ, .bind e rest, σ, ρ => by
      simp only [ruEnd, execEnd]
      rw [ruE_orte, lese_worldR, eval_ru, ← endR_schrumpf, ← execEnd_ru rest _ _]
      rfl
  | _, _, Λ, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [ruEnd, execEnd]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwort_ru]
      cases axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          cases w with
          | none => rfl
          | some v =>
              simp only [Option.map]
              rw [ergWert_ru he, ← endR_schrumpf, ← execEnd_ru rest σ' (Env.cons _ ρ)]
              rfl
  | _, _, Λ, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [ruEnd, execEnd]
      erw [ruA_orte, lese_worldR, evalArgs_ru, axiomAntwortSonst_ru]
      cases axiomAntwortSonst O a (σ.lese Λ args.orte)
        (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
      | mk σ' w =>
          rcases w with _ | v | r
          · rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
            rw [ergWert_ru he, ← endR_schrumpf, ← execEnd_ru rest σ' (Env.cons _ ρ)]
            rfl
          · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
            rw [← endR_schrumpf, ← execEnd_ru err σ' (Env.cons (τ := .why (D.agruende a)) r ρ)]
            rfl

theorem execArms_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    execArms O.mitRuhe passes R' (ruArms arms) (valR (.sum cs) v) (worldR σ) (envR ρ) =
      ausR (execArms O passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlock_ru b σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      exact (congrArg Ausgang.schrumpf (execBlock_ru b σ (Env.cons nutz ρ))).trans (ausR_schrumpf _)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrund_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrund O.mitRuhe passes R' (ruGArms arms) r (worldR σ) (envR ρ) =
      ausR (execGrund O passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlock_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrund_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Haupt
/-! ## 8. Every function behaves as in `P` -/

/-- **EVERY FUNCTION OF `P` BEHAVES IN `P.mitRuhe` AS IN `P`**: the body of
    `some f` in `P.mitRuhe`, run under the oracle `O.mitRuhe` from the
    translated world and parameters, ends in the translated outcome of the
    body of `f` in `P` under `O` -- for every budget and every pair of call
    handlers that answer translated calls with translated answers
    (`RufRu`). The generic form of `gPB_wie_gP_einzahlen`/`gPB_wie_gP_lies`
    (Schlusssatz104.lean). -/
theorem rumpf_mitRuhe_verhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hR : RufRu R R') (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    execEnd O.mitRuhe passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ) =
      endR (execEnd O passes R (P.rumpf f) σ ρ) :=
  (execEnd_umΛ O.mitRuhe passes R' _ _ _ _).trans (execEnd_ru O passes R R' hR (P.rumpf f) σ ρ)

/-- The root's body returns at once, touching nothing. -/
theorem rumpf_ruhe_verhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f) (σ : World D.mitRuhe) (ρ : Env D.mitRuhe (D.mitRuhe.params none)) :
    execEnd O.mitRuhe passes R' (P.mitRuhe.rumpf none) σ ρ = .zurueck σ () := rfl


/-! ## 9. Every call behaves as in `P` (`rufAt`) -/

theorem eval_umΓ_ergEnv {Γ : Ctx} {Λ' : List (Res D.mitRuhe)} :
    ∀ (e : Option Ty) (h : (ErgCtx Γ e).map tyR = ErgCtx (Γ.map tyR) (e.map tyR))
      (x : Expr D.mitRuhe ((ErgCtx Γ e).map tyR) Λ' .bool) (σ₀ σ : World D.mitRuhe)
      (v : ErgVal D e) (ρ : Env D Γ),
      eval σ₀ (Expr.umΓ h x) σ (ergEnv (e.map tyR) (ergR e v) (envR ρ)) =
        eval σ₀ x σ (envR (ergEnv e v ρ))
  | none, _, _, _, _, _, _ => rfl
  | some _, _, _, _, _, _, _ => rfl

theorem ens_mitRuhe_eval (P : Programm D) (f : D.Fn) (σ₀ σ : World D) (v : ErgVal D (D.erg f))
    (ρ : Env D (D.params f)) :
    eval (worldR σ₀) (P.mitRuhe.ensures (some f)) (worldR σ)
        (ergEnv ((D.erg f).map tyR) (ergR (D.erg f) v) (envR ρ)) =
      eval σ₀ (P.ensures f) σ (ergEnv (D.erg f) v ρ) :=
  (eval_umΓ_ergEnv (D.erg f) _ _ _ _ v ρ).trans
    ((eval_umΛ' _ _ _ _ _).trans (eval_ru σ₀ σ (P.ensures f) (ergEnv (D.erg f) v ρ)))

theorem inv_mitRuhe_eval (P : Programm D) (i : D.Inv) (σ : World D) :
    eval (worldR σ) (P.mitRuhe.invariante i) (worldR σ) Env.nil =
      eval σ (P.invariante i) σ Env.nil :=
  (eval_umΛ' _ _ _ _ _).trans (eval_ru σ σ (P.invariante i) Env.nil)


end Gabbro.Grammatik
