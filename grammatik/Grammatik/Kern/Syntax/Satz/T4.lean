/- Part 4 of 5 of `Satz` (split by instrumente/teile/lean-teilen.py; the umbrella `Satz.lean` imports all parts). -/
import Grammatik.Kern.Syntax.Satz.T3

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Rumpf
variable (O : Orakel D)

theorem axiomAntwort_gut (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    {Λ : List (Res D)}
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hh : HeldIn Λ σ.haelt) :
    Gut (D.aschreibt a) (D.agschreibt a) σ (axiomAntwort O a σ ρ).1 := by
  simp only [axiomAntwort]
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt :=
    fun t hwr L hL => hh L (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt :=
    fun g hwr L hL => hh L (hgd g hwr _ hL)
  obtain ⟨hr, hhaelt, hcond⟩ := hO a σ ρ
  obtain ⟨tabs, globs, Λe, _, _, hdt, hdg, _, hhi, hspur⟩ := hcond hgt hgg
  refine ⟨hr, hhaelt, fun e he => ?_, fun k => ?_⟩
  · have he' : e ∈ (O.wirkt a σ ρ).1.spur := he
    rw [hspur, List.mem_append] at he'
    rcases he' with hnew | hold
    · exact .inr (axiomSpur_gut tabs globs a Λe σ.haelt hdt hdg hhi e hnew)
    · exact .inl hold
  · have hc := konsistent_merke σ.haelt (axiomSpur tabs globs a Λe σ.haelt) σ.spur
      (fun e he => axiomSpur_zugriffMit tabs globs a Λe σ.haelt e he) rfl k
    exact hspur ▸ hc

variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : GutR R) (hO : GutO O)
include hR hO
set_option linter.unusedSectionVars false

mutual

/-- **Rahmen und Spur einer Anweisung**: ihr Ausgang unterscheidet sich von der Eingangswelt
    hoechstens an Traegern mit Schreibrecht im Vertrag, jede Sperre ist am Ende
    zurueckgegeben, und jedes neue Ereignis traegt seine Waechter. -/
theorem stmt_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), s.BodenOk bo → HeldB bo Λ σ.haelt →
    GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignThru p t _ f i e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
  | .assignGlob g e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldB hh).heldIn)
  | .putBytes t f hf n i _ _ e hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldB hh).heldIn)
  | .assignVar x e, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .shift t f hτ i von nach hn he hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_tab hL) i.orte_darf) hh.heldIn
        exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldB hh).heldIn)
      · simp [Ausgang.welt] at h
  | .ite c t e, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV t _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · exact (GutAusgang.vor hl (block_gutB bo hbV e _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .onOption o p a, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ o.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV p _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutAusgang.vor hl (block_gutB bo hbV a _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .onTag v arms, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ v.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (arms_gutB bo hbV arms _ _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .onWhy r arms, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ r.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (grund_gutB bo hbV arms _ _ ρ (by boden_tac) (hl.heldB hh))) σ' h
  | .call f args hp hr, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .callInd p args hp hr, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        subst hf
        exact hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .locks L hr body, σ, ρ, hbo, hh, σ', h =>
      (GutAusgang.gibt L (nicht_gehaltenB L hr hh (fun c hc => by
          have hsc := hbo c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at hsc; exact hsc.1))
        (block_gutB bo hbV body (σ.nimmt L) ρ (by boden_tac) (heldB_locks L hh))) σ' h
  | .breaking _ body, σ, ρ, hbo, hh, σ', h => block_gutB bo hbV body σ ρ (by boden_tac) hh σ' h
  | .traverse t inv body, σ, ρ, hbo, hh, σ', h =>
      traverseLauf_gut (Λ := Λ) _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh)
        (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) _ σ ρ hh σ' h
  | .retry n bis body ueberlauf, σ, ρ, hbo, hh, σ', h =>
      retryLauf_gut (Λ := Λ) _ _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh)
        (fun σ ρ hh => gut_lese σ Λ _ bis.orte_darf hh.heldIn)
        (fun σ ρ hh => block_gutB bo hbV ueberlauf σ ρ (by boden_tac) hh) n σ ρ hh σ' h
  | .forever a inv body, σ, ρ, hbo, hh, σ', h =>
      foreverLauf_gut (Λ := Λ) a _ _ (fun σ ρ hh => block_gutB bo hbV body σ ρ (by boden_tac) hh)
        (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) passes σ ρ hh σ' h
  | .axiomCall a args _ hw hg hd hgd, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at this
        exact hl.trans (Gut.weiter hw hg this)
      · simp [Ausgang.welt] at h
  | .regWrite r _ e, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .transition .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .publish g e _ _ hw hL, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldB hh).heldIn)
  | .advances .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retires .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .ret e _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retWhy .., σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hbo, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _

theorem block_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), b.BodenOk bo → HeldB bo Λ σ.haelt →
    GutAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · rename_i σ1 ρ1 hs
        have g1 := stmt_gutB bo hbV s σ ρ (by boden_tac) hh σ1 (by rw [hs]; rfl)
        exact g1.trans (block_gutB bo hbV rest σ1 ρ1 (by boden_tac) (heldB_weiter s.held_iff g1 hh) σ' h)
      · subst_vars
        exact stmt_gutB bo hbV s σ ρ (by boden_tac) hh σ' h
  | .bind e rest, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := block_gutB bo hbV rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) (by boden_tac)
        subst hf
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((g2 (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang σ' h)
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · simp [Ausgang.welt] at h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((block_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf.zuAusgang σ' h)
      · simp [Ausgang.welt] at h
  | .regRead r _ rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · split at h
        · exact (block_gutB bo hbV rest σ _ (by boden_tac) hh).schrumpf σ' h
        · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        split at h
        · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
      · simp [Ausgang.welt] at h
  | .awaits g _ _ hL rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
          (orte_cons (orte_glob hL) (by intro o ho; simp at ho)) hh.heldIn
        exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .exchange g neu hw hL rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_glob hL) neu.orte_darf) hh.heldIn
      have g1 := hl.trans (gut_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw hL (hl.heldB hh).heldIn)
      exact (GutAusgang.vor g1 (block_gutB bo hbV rest _ _ (by boden_tac) (g1.heldB hh))).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
  | .check c sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h
  | .float op a b lo hi rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append a.orte_darf b.orte_darf) hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .floatLit q lo hi rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · exact (block_gutB bo hbV rest σ _ (by boden_tac) hh).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .floatOf e lo hi rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .floatNarrow e lo hi sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))).zuAusgang σ' h

theorem end_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ), b.BodenOk bo → HeldB bo Λ σ.haelt →
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retWhy .., σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      have hs := stmt_gutB bo hbV s σ ρ (by boden_tac) hh
      split at h
      · rename_i σ1 ρ1 hs1
        have g1 := hs σ1 (by rw [hs1]; rfl)
        exact g1.trans (end_gutB bo hbV rest σ1 ρ1 (by boden_tac) (heldB_weiter s.held_iff g1 hh) σ' h)
      all_goals first
        | (rename_i hs1; simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           exact hs _ (by rw [hs1]; rfl))
        | (simp [EndAusgang.welt] at h)
  | .bind e rest, σ, ρ, hbo, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [EndAusgang.welt] at h
      · simp [EndAusgang.welt] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac)
          (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · simp [EndAusgang.welt] at h
      · simp [EndAusgang.welt] at h
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · simp [EndAusgang.welt] at h
  | .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) hd hgd (hl.heldB hh).heldIn
      rw [← axiomAntwortSonst_fst] at h1
      split at h
      · rename_i σ1 v ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV rest σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · rename_i σ1 r ha
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((end_gutB bo hbV err σ1 _ (by boden_tac) (g1.heldB hh)).schrumpf σ' h)
      · simp [EndAusgang.welt] at h
  | .regRead r _ rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      split at h
      · split at h
        · exact (end_gutB bo hbV rest σ _ (by boden_tac) hh).schrumpf σ' h
        · simp [EndAusgang.welt] at h
      · simp [EndAusgang.welt] at h
  | .regReadElse r _ zusage sonst rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        split at h
        · exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gutB bo hbV sonst _ ρ (by boden_tac) (hl.heldB hh))) σ' h
      · simp [EndAusgang.welt] at h
  | .awaits g _ _ hL rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
          (orte_cons (orte_glob hL) (by intro o ho; simp at ho)) hh.heldIn
        exact (GutEnd.vor hl (end_gutB bo hbV rest _ _ (by boden_tac) (hl.heldB hh))).schrumpf σ' h
      · simp [EndAusgang.welt] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hbo, hh, σ', h => by
      simp only [execEnd] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := end_gutB bo hbV rest σ1 (.cons (ergWert (ergSig hf he) v) ρ) (by boden_tac)
        subst hf
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((g2 (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [EndAusgang.welt] at h
      · simp [EndAusgang.welt] at h

theorem arms_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    arms.BodenOk bo → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, hbo, hh, σ', h => (block_gutB bo hbV b σ _ (by boden_tac) hh).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hbo, hh, σ', h => arms_gutB bo hbV rest _ σ ρ (by boden_tac) hh σ' h

theorem grund_gutB (bo : Option Int) (hbV : BodenUnter bo V.boden) :
    ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    arms.BodenOk bo → HeldB bo Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, hbo, hh, σ', h => block_gutB bo hbV b σ ρ (by boden_tac) hh σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, hbo, hh, σ', h => grund_gutB bo hbV rest _ σ ρ (by boden_tac) hh σ' h

end

/-! The exact-held-set forms (no extra lock, `HeldGenau`), with their old names. -/

theorem stmt_gut (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ) :=
  stmt_gutB O passes R hR hO none (bodenUnter_none _) s σ ρ (fun _ h => nomatch h) (heldB_of_genau none hh)

theorem block_gut (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    GutAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ) :=
  block_gutB O passes R hR hO none (bodenUnter_none _) b σ ρ (fun _ h => nomatch h) (heldB_of_genau none hh)

theorem end_gut (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ) :=
  end_gutB O passes R hR hO none (bodenUnter_none _) b σ ρ (fun _ h => nomatch h) (heldB_of_genau none hh)

end Rumpf
/-! ### Der Ruf, bis hinauf zum Programm -/

theorem held_invSicht_aux (L : D.Lock) : ∀ (ts : List D.Tab),
    Res.held L ∈ ts.foldr (fun t acc => (D.braucht t).map (Res.von D) ++ acc) [] →
    ∃ t ∈ ts, Sum.inl L ∈ D.braucht t := by
  intro ts
  induction ts with
  | nil => intro h; simp at h
  | cons t ts ih =>
      intro h
      simp only [List.foldr_cons, List.mem_append, List.mem_map] at h
      rcases h with ⟨w, hw, hwL⟩ | h
      · refine ⟨t, List.mem_cons_self, ?_⟩
        cases w with
        | inl M => simp [Res.von] at hwL; subst hwL; exact hw
        | inr m => obtain ⟨_, _⟩ := m; simp [Res.von] at hwL
      · obtain ⟨t', ht', hL⟩ := ih h
        exact ⟨t', List.mem_cons_of_mem _ ht', hL⟩

theorem held_invSicht (i : D.Inv) (L : D.Lock) (h : Res.held L ∈ invSicht D i) :
    ∃ t ∈ D.traeger i, Sum.inl L ∈ D.braucht t :=
  held_invSicht_aux L _ h

/-- Die Invarianten, die ein Rumpf schuldet, liest er unter Sperren, die er haelt (`U003`). -/
theorem heldIn_invarianten (P : Programm D) (f : D.Fn) {h : List D.Lock}
    (hh : HeldIn (Signatur.anfang D (D.signatur f)) h) (i : D.Inv) (hi : schuldet f i = true) :
    HeldIn (invSicht D i) h := by
  intro L hL
  obtain ⟨t, ht, hLt⟩ := held_invSicht i L hL
  have := D.invarianten_gehalten (D.sig f) i hi t ht L hLt
  exact hh L ((held_anfang _ L).mpr this)

theorem gut_foldl_lese {W G} (P : Programm D) (f : D.Fn) :
    ∀ (is : List D.Inv) (σ : World D), (∀ i ∈ is, schuldet f i = true) →
      HeldIn (Signatur.anfang D (D.signatur f)) σ.haelt →
      Gut W G σ (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ) := by
  intro is
  induction is with
  | nil => intro σ _ _; exact Gut.refl _ _ _
  | cons i is ih =>
      intro σ hs hh
      simp only [List.foldl_cons]
      have g1 : Gut W G σ (σ.lese (invSicht D i) (P.invariante i).orte) :=
        gut_lese σ _ _ (P.invariante i).orte_darf
          (heldIn_invarianten P f hh i (hs i List.mem_cons_self))
      exact g1.trans (ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj)) (g1.heldIn hh))

/-- **Rahmen und Spur eines Rufs, bis hinauf zum Programm**: auf jeder Rekursionstiefe haelt
    `rufAt` Rahmen und Spur des Gerufenen -- Induktion ueber die Tiefe, mit `end_gut` fuer
    den Rumpf. Die einzige Praemisse ist die Hardware (H1) -- and, since the
    held-set relaxation (2026-09-13), that every body respects its function's
    lock floor (`StufenOk`, trivial without floors: `stufenOk_ohne`). -/
theorem rufAt_gut (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O) (hP : StufenOk P) :
    ∀ fuel, GutR (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ _ σ' h; simp [rufAt, RufAusgang.welt] at h
  | succ n ih =>
      intro f σ ρ hh σ' h
      simp only [rufAt] at h
      have g0 : Gut (D.schreibt f) (D.gschreibt f) σ _ :=
        gut_lese σ _ _ (P.requires f).orte_darf hh.heldIn
      split at h
      · simp [RufAusgang.welt] at h
      · have hb := end_gutB O passes (rufAt P O passes n) ih hO (D.signatur f).boden
          (bodenUnter_refl _) (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (hP f) (g0.heldB hh)
        split at h
        · rename_i σ2 v hs
          have g2 : Gut (D.schreibt f) (D.gschreibt f) _ σ2 := hb σ2 (by rw [hs]; rfl)
          have hh2 : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ2.haelt :=
            g2.heldB (g0.heldB hh)
          have g3 : Gut (D.schreibt f) (D.gschreibt f) σ2 _ :=
            gut_lese σ2 (vertragVon D f).ende _ (P.ensures f).orte_darf
              (by intro L hL; exact hh2.heldIn L ((held_anfang _ L).mpr ((held_ende _ L).mp hL)))
          split at h
          · simp [RufAusgang.welt] at h
          · have g4 := gut_foldl_lese (W := D.schreibt f) (G := D.gschreibt f) P f
              (D.invs.filter (schuldet f)) _
              (fun i hi => (List.mem_filter.mp hi).2) (g3.heldB hh2).heldIn
            split at h
            · simp [RufAusgang.welt] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
              exact ((g0.trans g2).trans g3).trans g4
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
          exact g0.trans (hb _ (by rw [hs]; rfl))
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp [RufAusgang.welt] at h
        · simp [RufAusgang.welt] at h

/-- **Der Satz ueber Rahmen und Spur**: ein Rumpf unter Vertrag `V`, gestartet in einer Welt,
    die haelt, was sein `Λ` nennt, schreibt nur, was `V` nennt, gibt jede Sperre zurueck und
    tut keinen Zugriff ohne die Waechter seines Traegers -- fuer jedes Programm, jede Tiefe,
    jede Welt; die Hardware haelt ihr `effects` (H1). -/
theorem exec_gut (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O) (hP : StufenOk P)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    GutAusgang V.schreibt V.gschreibt σ (exec P O passes fuel V b σ ρ) :=
  block_gut O passes _ (rufAt_gut P O passes hO hP fuel) hO b σ ρ hh


end Gabbro.Grammatik
